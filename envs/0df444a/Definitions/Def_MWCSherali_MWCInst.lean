-- Prove2me | Definitions.Def_MWCSherali_MWCInst
-- name    : MWCSherali_MWCInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:17.026833+00:00
-- url     : https://prove2.me/theorems/85d3902a-c20b-496e-9f47-55dd8b73bb1f
-- title:
--   Weighted Multiway Cut instance (unary multigraph weights)
-- statement:
--   An instance of the **(minimum) Multiway Cut** problem is a weighted undirected graph $G=(V,E,w)$ with $k$ designated vertices, the **terminals**. Here the graph is a loopless multigraph on $V=\{0,\dots,n-1\}$ given by a list of edges, an edge listed $m$ times having weight $m$ (the published `OptInapprox.MaxCut.WMaxCut`), and the terminals are $k$ distinct vertices $\tau_0,\dots,\tau_{k-1}$. Its total weight $W$ is the published `Max3CutHard.wt` of the graph, and the weight of a multiway cut is the published `Max3CutHard.cutK`.
--
--   This is the input of the problem whose approximability the paper studies (Section 1, p.2).
--
--   **Formalization Note** Weights are natural-number multiplicities written out in the edge list (a unary encoding), as in the published `OptInapprox.MaxCut.WMaxCut`. Hardness on these instances implies hardness for rational or real positive weights under any reasonable encoding. Terminals are 0-based: the paper's terminal $i\in[k]$ is $\tau_{i-1}$.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), §1, p.2 (definition of the Multiway Cut problem)

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_UGC

namespace MWCSherali

open OptInapprox.MaxCut

/-- **A weighted Multiway Cut instance.** Brakensiek–Huang–Potechin–Zwick, *Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations*,
arXiv:2611.05511 (version of Nov. 3, 2026), §1, p.2: "a weighted undirected graph
`G = (V, E, w)`, where `w : E → ℝ₊`, with `k` designated vertices called terminals".

The graph is the published weighted multigraph `OptInapprox.MaxCut.WMaxCut` (vertices `Fin n`,
a loopless edge list in which an edge listed `m` times has weight `m`); the terminals are
`term 0, …, term (k-1)`, distinct vertices.

**Formalization Note.**
* Weights are natural-number multiplicities written out in the edge list (a unary encoding).
  Hardness on these instances implies hardness for rational or real positive weights under any
  reasonable encoding.
* The terminal list is 0-based: the paper's terminal `i ∈ [k]` is `term (i - 1)`.
* The total weight and the cut weight are the published `Max3CutHard.wt` and
  `Max3CutHard.cutK` of the underlying `WMaxCut`. -/
structure MWCInst where
  /-- the weighted multigraph -/
  graph : WMaxCut
  /-- number of terminals -/
  k : ℕ
  /-- the terminals -/
  term : Fin k → Fin graph.n
  term_inj : Function.Injective term

end MWCSherali


