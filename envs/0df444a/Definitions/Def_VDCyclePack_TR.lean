-- Prove2me | Definitions.Def_VDCyclePack_TR
-- name    : VDCyclePack_TR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:15.515202+00:00
-- url     : https://prove2.me/theorems/c9278385-3d00-4733-bef8-b2b8ce806fb3
-- title:
--   $T_R=\sum_{C\in R}x_C$: total weight of a family
-- statement:
--   For a family $R$ of cycles with weights $x$, $T_R=\sum_{C\in R}x_C$. For $R=S$ this is the total weight $T$ of Theorem 4.2.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Section 5.1, p.15

import Mathlib

namespace VDCyclePack

/-- **T_R: the total weight of a family.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Section 5.1, p.15: "For R ⊆ S, let T_R = Σ_{C∈R} x_C".

`TR R x = Σ_{C ∈ R} x C`. For `R = S` this is the paper's `T`. -/
def TR {V : Type*} {G : SimpleGraph V} (R : Finset G.Subgraph) (x : G.Subgraph → ℝ) : ℝ :=
  ∑ C ∈ R, x C

end VDCyclePack


