-- Prove2me | Definitions.Def_GraphNNSphere_IsNavGraph
-- name    : GraphNNSphere_IsNavGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:38:12.294748+00:00
-- url     : https://prove2.me/theorems/5748c86b-c993-4187-81e9-33a8e775a2aa
-- title:
--   Navigation graph
-- statement:
--   A navigation graph $G$ assigns to each data point $x$ a neighbor list $G(x)$ of distinct points of $D_n\setminus\{x\}$. In terms of labels, no label is listed at itself. A graph may be chosen after observing the sample, which is why the theorems quantify over $G$ after the sample.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3

import Mathlib
import Definitions.Def_GraphNNSphere_NavGraph

namespace GraphNNSphere

/-- A navigation graph: each `G(x)` is a neighbor list of distinct points in `D_n \ {x}` (Lu,
*Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission
(manuscript sha256 93565bc5…), §1.2, p.3).

**Formalization Note** No dependence on the sample is restricted: a graph may be chosen after
observing `D_n`, which is why every statement quantifies over `G` after the sample. -/
def IsNavGraph {n : ℕ} (G : NavGraph n) : Prop := ∀ i, i ∉ G i

end GraphNNSphere


