astar
=====

erlang Implementation of the A* Pathfinding Algorithm


Sample Usage
-----
```erlang
Graph = astar:graph([
        [0,0,1,0,0,0,1,0,0,0], % 9
        [0,0,1,0,0,0,1,0,0,0], % 8
        [0,0,1,0,0,0,1,0,0,0], % 7
        [0,0,1,0,0,0,1,0,0,0], % 6
        [0,0,0,0,0,0,0,0,0,0], % 5
        [0,0,0,1,0,0,0,0,0,0], % 4
        [0,0,0,1,0,0,0,0,0,0], % 3
        [0,0,0,1,0,0,0,0,0,0], % 2
        [0,0,0,1,0,0,0,0,0,0], % 1
        [0,0,0,1,0,0,0,0,0,0]  % 0
   ]),
   
astar:search(Graph, {0, 0}, {9, 9}).

```
