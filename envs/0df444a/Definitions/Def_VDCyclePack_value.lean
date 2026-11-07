-- Prove2me | Definitions.Def_VDCyclePack_value
-- name    : VDCyclePack_value
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:08:19.262572+00:00
-- url     : https://prove2.me/theorems/c9e63a08-3118-42a0-b75d-a9cb143792e8
-- title:
--   Value $T=\sum_C x_C$ of a weighting of the cycles
-- statement:
--   For weights $x$ on the cycles of a finite graph $G$, the **value** is
--   $$
--   T=\sum_{C\in\mathcal C(G)} x_C .
--   $$
--
--   It is the objective of the natural LP (1).
--
--   **Formalization Note** Only the values of $x$ on cycles of $G$ enter the sum.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Section 3, p.9

import Mathlib
import Definitions.Def_VDCyclePack_cycles

namespace VDCyclePack

/-- **Value of a weighting of the cycles.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Section 3, p.9: "the value of the packing is T = Σ_C x_C".

`value G x = Σ_{C ∈ 𝒞(G)} x C`.

**Formalization Note.** Only the values of `x` on cycles of `G` are read. -/
noncomputable def value {V : Type*} [Fintype V] (G : SimpleGraph V) (x : G.Subgraph → ℝ) : ℝ :=
  ∑ C ∈ cycles G, x C

end VDCyclePack


