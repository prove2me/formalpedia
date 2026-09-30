-- Prove2me | Definitions.Def_PadbergRao_OddCut_cutCapacity
-- name    : PadbergRao_OddCut_cutCapacity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T22:34:20.266699+00:00
-- url     : https://prove2.me/theorems/ac3671f7-f9c3-4594-81f0-aed370b2889f
-- title:
--   $c(W : V - W)$: the capacity of the cut-set of a node set $W$
-- statement:
--   Let $G = (V, E)$ be a finite undirected graph without loops and multiple edges, with nonnegative edge weights. We record the weights as a function $c : V \times V \to \mathbb{R}$, where $c_{ij}$ is the weight of the edge $[i, j]$ and $c_{ij} = 0$ when $i$ and $j$ are not adjacent.
--
--   For a set of nodes $W \subseteq V$, the **cut-set** $(W : V - W)$ is the set of edges with exactly one end in $W$. Its **capacity** is
--
--   $$
--   c(W : V - W) \;=\; \sum_{e \in (W : V - W)} c_e \;=\; \sum_{i \in W} \sum_{j \in V - W} c_{ij}.
--   $$
--
--   Every quantity in the odd minimum cut-set problem is a cut capacity, so this is the basic object of the mission.
--
--   **Formalization Note** Node sets are `Finset V` over a `Fintype V`, and $V - W$ is the complement `Wᶜ`. The graph is encoded by its weight function; symmetry and nonnegativity of `c` are stated as hypotheses in the theorems, not in this definition. With a symmetric `c`, each edge across the cut is counted exactly once, and the diagonal values `c i i` never enter.
-- source:
--   Padberg, Rao, Odd Minimum Cut-Sets and b-Matchings, Math. Oper. Res. 7 (1982), p. 68, Section 1 (the capacity formula following Eq. (1.1))

import Mathlib

namespace PadbergRao.OddCut

/-- `c(W : V − W) = ∑_{i ∈ W} ∑_{j ∈ V − W} c_ij`: the capacity of the cut-set `(W : V − W)`
of a finite undirected graph on the node type `V`, whose edge weights are given by the
(symmetric, nonnegative) weight function `c`, with `c i j = 0` when there is no edge `[i, j]`.
Padberg–Rao 1982, p. 68, Section 1 (the formula after (1.1)). -/
def cutCapacity {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ) (W : Finset V) : ℝ :=
  ∑ i ∈ W, ∑ j ∈ Wᶜ, c i j

end PadbergRao.OddCut


