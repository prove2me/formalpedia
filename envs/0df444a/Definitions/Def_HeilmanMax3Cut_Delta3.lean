-- Prove2me | Definitions.Def_HeilmanMax3Cut_Delta3
-- name    : HeilmanMax3Cut_Delta3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:26:57.494377+00:00
-- url     : https://prove2.me/theorems/35fe19e7-06d8-47c8-a68a-2d0ad96508e7
-- title:
--   The simplex $\Delta_3$
-- statement:
--   $$\Delta_3=\Bigl\{z\in[0,1]^3:\ \sum_{i=1}^3 z_i=1\Bigr\}.$$
--
--   For a partition of $\mathbb R^2$ and a radius, the normalized angular measures of the three cells on the circle of that radius form a point of $\Delta_3$; its centre is $b\mathbf 1=(1/3,1/3,1/3)$.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Section 7, p.21

import Mathlib

namespace HeilmanMax3Cut

/-- **The simplex `Δ₃`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Section 7, p.21:
`Δ₃ = {z ∈ [0, 1]³ : ∑_{i=1}^3 zᵢ = 1}`.

**Formalization Note.** Vectors of `ℝ³` are functions `Fin 3 → ℝ` (coordinates `0, 1, 2` for the
paper's `1, 2, 3`). -/
def Delta3 : Set (Fin 3 → ℝ) :=
  {z | (∀ i, z i ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ i, z i = 1}

end HeilmanMax3Cut


