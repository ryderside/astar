%%%-------------------------------------------------------------------
%%% @author jiangxiaowei@lilith.sh
%%% @copyright (C) 2018, Lilith Games
%%% @doc
%%% A*寻路算法
%%% @end
%%% Created : 30. 七月 2018 18:05
%%%-------------------------------------------------------------------
-module(astar).
-author("jiangxiaowei@lilith.sh").

-include_lib("eunit/include/eunit.hrl").

%% API
-export([graph/1, search/3, search/4]).

-record(graph, {width = 0, height = 0, grids = undefined}).

-record(node, {
    x = 0,
    y = 0,
    h = 0,
    g = 0,
    parent = undefined
}).

graph(Points) ->
    {ok, Height, Width, MapGrids} = generate_map_grids(Points),
    #graph{height = Height, width = Width, grids = MapGrids}.

generate_map_grids(Points) ->
    generate_map_grids(Points, 0, 0, []).

generate_map_grids([], Height, Width, GridsList) ->
    {ok, Height, Width, array:from_list(lists:reverse(GridsList))};
generate_map_grids([H|T], Height, Width, GridsList) when is_list(H) ->
    {ok, RowArray} = generate_row_grids(H),
    case Width == 0 orelse array:size(RowArray) == Width of
        true ->
            generate_map_grids(T, Height + 1, array:size(RowArray), [RowArray|GridsList]);
        false ->
            erlang:throw({error, badarg})
    end.

generate_row_grids(Row) ->
    generate_row_grids(Row, []).

generate_row_grids([], List) ->
    {ok, array:from_list(lists:reverse(List))};
generate_row_grids([H|T], List) when H == 0 orelse H == 1 ->
    generate_row_grids(T, [H|List]).

is_walk_grid({X, Y}, Graph) ->
    is_walk_grid(X, Y, Graph).
is_walk_grid(X, Y, #graph{width = Width, height = Height})
    when X < 0 orelse X >= Width orelse Y < 0 orelse Y >= Height ->
    false;
is_walk_grid(X, Y, #graph{grids = Grids}) ->
    case array:get(Y, Grids) of
        undefined ->
            false;
        Row ->
            case array:get(X, Row) of
                undefined ->
                    false;
                V ->
                    V == 0
            end
    end.

pos2node({X, Y}) ->
    #node{x = X, y = Y}.

search(Graph, Start, End) ->
    search(Graph, Start, End, []).

search(Graph, Start, End, Options) ->
    case is_walk_grid(Start, Graph) andalso is_walk_grid(End, Graph)  of
        false ->
            {error, bad_position};
        true ->
            OpenGbTree = gb_trees:from_orddict([]),
            ClosedDict = dict:new(),
            VisitedSets = sets:new(),
            StartNode = pos2node(Start),
            EndNode = pos2node(End),
            HeuristicsType = proplists:get_value(heuristics, Options, diagonal),
            OpenGbTree0 = push_open_nodes(StartNode#node{g = 0, h = h(HeuristicsType, StartNode, EndNode)}, OpenGbTree),
            do_search(Graph, EndNode, OpenGbTree0, ClosedDict, VisitedSets, HeuristicsType)
    end.

do_search(Graph, EndNode, OpenGbTree, ClosedDict, VisitedSets, HeuristicsType) ->
    case dequeue_cheapest_node(OpenGbTree) of
        none -> %% no other node
            none;
        {ok, OpenGbTree0, CurrentNode} ->
            case eq(CurrentNode, EndNode) of
                true -> %% Find it!
                    make_path(CurrentNode, ClosedDict);
                false ->
                    %% move currentNode from open to closed
                    ClosedDict0 = push_closed_node(CurrentNode, ClosedDict),
                    %% Find all neighbors for the current node.
                    NeighborsNodes = neighbors_nodes(HeuristicsType, CurrentNode),
                    %% push neighbors if node validity
                    {OpenGbTree1, ClosedDict1, VisitedSets0} = push_neighbors(NeighborsNodes, EndNode, CurrentNode, Graph,
                        HeuristicsType, OpenGbTree0, ClosedDict0, VisitedSets),
                    %% tail recursion
                    do_search(Graph, EndNode, OpenGbTree1, ClosedDict1, VisitedSets0, HeuristicsType)
            end
    end.

neighbors_nodes(manhattan, #node{x = X, y = Y}) ->
    [
        #node{x = X, y = Y - 1},
        #node{x = X - 1, y = Y}, #node{x = X + 1, y = Y},
        #node{x = X, y = Y + 1}
    ];
neighbors_nodes(diagonal, #node{x = X, y = Y}) ->
    [
        #node{x = X - 1, y = Y - 1}, #node{x = X, y = Y - 1}, #node{x = X + 1, y = Y - 1},
        #node{x = X - 1, y = Y}, #node{x = X + 1, y = Y},
        #node{x = X - 1, y = Y + 1}, #node{x = X, y = Y + 1}, #node{x = X + 1, y = Y + 1}
    ].

%% 获取相邻的node
push_neighbors([], _EndNode, _CurrentNode, _Graph, _HeuristicsType, OpenGbTree, ClosedDict, VisitedSets) ->
    {OpenGbTree, ClosedDict, VisitedSets};
push_neighbors([NeighborsNode = #node{x = X, y = Y}|T], EndNode, CurrentNode, Graph, HeuristicsType, OpenGbTree, ClosedDict, VisitedSets) ->
    case is_walk_grid(X, Y, Graph) andalso not is_closed(X, Y, ClosedDict) of
        true -> %% 可行走点，没有在closed列表
            %% 计算子节点G值 = 父节点G值 + G值开销
            G = CurrentNode#node.g + g(NeighborsNode, CurrentNode),
            %% 当前点到重点的H值
            H = h(HeuristicsType, NeighborsNode, EndNode),
            NeighborsNode0 = NeighborsNode#node{g = G, h = H, parent = {CurrentNode#node.x, CurrentNode#node.y}},
            case sets:is_element({X, Y}, VisitedSets) of
                true -> %% 已经寻到过的点，更新open列表node
                    OpenGbTree0 = rescore_open_node(NeighborsNode0, OpenGbTree),
                    push_neighbors(T, EndNode, CurrentNode, Graph, HeuristicsType, OpenGbTree0, ClosedDict, VisitedSets);
                false ->
                    OpenGbTree0 = push_open_nodes(NeighborsNode0, OpenGbTree),
                    VisitedSets0 = sets:add_element({X, Y}, VisitedSets),
                    push_neighbors(T, EndNode, CurrentNode, Graph, HeuristicsType, OpenGbTree0, ClosedDict, VisitedSets0)
            end;
        false ->
            push_neighbors(T, EndNode, CurrentNode, Graph, HeuristicsType, OpenGbTree, ClosedDict, VisitedSets)
    end.

%% 选择代价最小的点
dequeue_cheapest_node(OpenGbTree) ->
    case gb_trees:is_empty(OpenGbTree) of
        true ->
            none;
        false ->
            {{_Score, Node} = Key, _} = gb_trees:smallest(OpenGbTree),
            {ok, gb_trees:delete(Key, OpenGbTree), Node}
    end.

is_closed(X, Y, ClosedDict) ->
    dict:is_key({X, Y}, ClosedDict).

%% 生成路径
make_path(Node, ClosedDict) ->
    make_path(Node, ClosedDict, []).
make_path(#node{x = X, y = Y, parent = Parent}, ClosedDict, Path) ->
    case dict:find(Parent, ClosedDict) of
        'error' ->
            [{X, Y}|Path];
        {ok, ParentNode} ->
            make_path(ParentNode, ClosedDict, [{X, Y}|Path])
    end.

%% @doc 计算该点到终点的距离加权值
%% 启发函数: 曼哈顿距离
h(manhattan, #node{x = X1, y = Y1}, #node{x = X2, y = Y2}) ->
    erlang:abs(X2 - X1) + erlang:abs(Y2 - Y1);
%% 启发函数: 斜对角线
h(diagonal, #node{x = X1, y = Y1}, #node{x = X2, y = Y2}) ->
    D1 = erlang:abs(X2 - X1),
    D2 = erlang:abs(Y2 - Y1),
    (D1 + D2) + (-0.5857864376269049 * erlang:min(D1, D2)).

%% 更新已经在open列表的节点信息
%% f值越小则替换
rescore_open_node(Node = #node{x = X, y = Y, h = H, g = G}, OpenGbTree) ->
    case search_open_node(X, Y, OpenGbTree) of
        {ok, Key = {_Score, #node{h = H1, g = G1}}} ->
            case H + G < H1 + G1 of
                true -> %% 代价更小
                    OpenGbTree0 = gb_trees:delete(Key, OpenGbTree),
                    push_open_nodes(Node, OpenGbTree0);
                false ->
                    OpenGbTree
            end;
        _ ->
            push_open_nodes(Node, OpenGbTree)
    end.

search_open_node(X, Y, OpenGbTree) ->
    Iter = gb_trees:iterator(OpenGbTree),
    do_search_open_node(gb_trees:next(Iter), X, Y).
do_search_open_node(none, _X, _Y) ->
    none;
do_search_open_node({Key = {_Score, #node{x = X, y = Y}}, _Value, _Iter}, X, Y) ->
    {ok, Key};
do_search_open_node({_Key, _Value, Iter}, X, Y) ->
    do_search_open_node(gb_trees:next(Iter), X, Y).

push_open_nodes(#node{g = G, h = H} = Node, OpenGbTree) ->
    gb_trees:insert({G + H, Node}, true, OpenGbTree).

push_closed_node(#node{x = X, y = Y} = Node, ClosedDict) ->
    dict:store({X, Y}, Node, ClosedDict).

%% @doc G值开销
%% 直走
g(#node{x = X1, y = Y1}, #node{x = X2, y = Y2}) when X1 == X2 orelse Y1 == Y2 -> 1;
%% 斜对角行走
g(#node{}, #node{}) -> 1.41421.

%% @doc 判断是否是同一个点
eq(#node{x = X, y = Y}, #node{x = X, y = Y}) -> true;
eq(#node{}, #node{}) -> false.

-ifdef(TEST).

basic_test() ->
    Graph = astar:graph([
        [0,0,1,0,0,0,1,0,0,0], % 0
        [0,0,1,0,0,0,1,0,0,0], % 1
        [0,0,1,0,0,0,1,0,0,0], % 2
        [0,0,1,0,0,0,1,0,0,0], % 3
        [0,0,0,0,0,0,0,0,0,0], % 4
        [0,0,0,1,0,0,0,0,0,0], % 5
        [0,0,0,1,0,0,0,0,0,0], % 6
        [0,0,0,1,0,0,0,0,0,0], % 7
        [0,0,0,1,0,0,0,0,0,0], % 8
        [0,0,0,1,0,0,0,0,0,0]  % 9
    ]),
    %% {6, 4} -> {9, 9} heuristics: manhattan
    [{0,0}, {0,1}, {0,2}, {0,3}, {0,4}, {1,4}, {2,4}, {3,4}, {4,4}, {4,5}, {4,6}, {4,7}, {4,8},
        {4,9}, {5,9}, {6,9}, {7,9}, {8,9}, {9,9}] = astar:search(Graph, {0, 0}, {9, 9}, [{heuristics, manhattan}]),
    %% {6, 4} -> {9, 9} heuristics: diagonal
    [{0,0}, {1,1}, {1,2}, {1,3}, {2,4}, {3,4}, {4,5}, {5,6}, {6,7},
        {7,8}, {8,9}, {9,9}] = astar:search(Graph, {0, 0}, {9, 9}, [{heuristics, diagonal}]),
    %% bad position start / end
    ?assertEqual({error, bad_position}, astar:search(Graph, {10,1}, {9,9}, [])),
    ?assertEqual({error, bad_position}, astar:search(Graph, {0,0}, {10,10}, [])),

    %% 死路
    Graph1 = astar:graph([
        [0,0,0,0,0,0,0,0,0,0], % 0
        [0,0,0,0,0,0,0,0,0,0], % 1
        [0,0,0,0,0,0,0,0,0,0], % 2
        [0,0,0,0,0,0,0,0,0,0], % 3
        [0,0,0,0,0,0,0,0,0,0], % 4
        [0,0,0,1,1,1,1,1,1,1], % 5
        [0,0,0,1,0,0,0,0,0,0], % 6
        [0,0,0,1,0,0,0,0,0,0], % 7
        [0,0,0,1,0,0,0,0,0,0], % 8
        [0,0,0,1,0,0,0,0,0,0]  % 9
    ]),

    ?assertEqual(none, astar:search(Graph1, {0, 0}, {9, 9}, [{heuristics, manhattan}])),

    ok.

-endif.
