-- Prove2me | Definitions.Def_VDCyclePack_nuStar
-- name    : VDCyclePack_nuStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:10:53.850395+00:00
-- url     : https://prove2.me/theorems/61c26fe9-8f7f-4e02-8188-e25531c35d45
-- title:
--   $\nu^*(G)$, the optimum of the natural LP (1)
-- statement:
--   For a finite graph $G$,
--   $$
--   \nu^*(G)=\max\Bigl\{\sum_{C\in\mathcal C(G)}x_C\ :\ x\ \text{a fractional packing of } G\Bigr\},
--   $$
--   the optimum of the natural LP relaxation (1) of vertex-disjoint cycle packing. It satisfies $\nu(G)\le\nu^*(G)\le n/3$, and $\nu^*(G)=0$ exactly when $G$ is a forest.
--
--   Theorem 1.1 measures the size of the packing it returns against $\nu^*(G)$.
--
--   **Formalization Note** Defined as the real supremum of the values of all fractional packings. The set of values is nonempty ($x=0$) and bounded by $|V(G)|$, and the LP has finitely many variables, so the supremum is the maximum.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), (1), p.3

import Mathlib
import Definitions.Def_VDCyclePack_IsFracPacking
import Definitions.Def_VDCyclePack_value

namespace VDCyclePack

/-- **ν*(G), the optimum of the natural LP (1).**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), (1), p.3: "ν*(G) = max Σ_{C∈C(G)} x_C subject to Σ_{C∈C(G), v∈V(C)} x_C ≤ 1 for every
v ∈ V(G), x_C ≥ 0 for every C ∈ C(G)."

`nuStar G` is the supremum of the values of all fractional packings of `G`.

**Formalization Note.** The set of values is nonempty (`x = 0`) and bounded above by `|V(G)|`
(every cycle has a vertex, so its weight is at most the load there), so the real supremum is the
LP optimum; the LP has finitely many variables, so the supremum is attained. -/
noncomputable def nuStar {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ :=
  sSup {T | ∃ x : G.Subgraph → ℝ, IsFracPacking G x ∧ value G x = T}

end VDCyclePack


