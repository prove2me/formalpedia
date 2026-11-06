-- Prove2me | Definitions.Def_GradSuffice_Thm8Data_affinePiece
-- name    : GradSuffice_Thm8Data_affinePiece
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:22:37.493202+00:00
-- url     : https://prove2.me/theorems/b56ae2a1-df41-466a-ba1a-b621942e1e80
-- title:
--   Affine pieces $\tfrac1{16}\eta_{t,k}\cdot y_k(w)+b_{t,k}+Z_{t,k}$
-- statement:
--   For a noise realization $Z$, the affine pieces of copy $k$ of the hard function are
--   $$\frac1{16}\,\eta_{t,k}\cdot y_k(w)+b_{t,k}+Z_{t,k}\qquad(t=1,\dots,D).$$
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §7, p.19

import Mathlib
import Definitions.Def_GradSuffice_Thm8Data_NoiseIdx
import Definitions.Def_GradSuffice_Thm8Data_y
import Definitions.Def_GradSuffice_Thm8Data_b
import Definitions.Def_GradSuffice_Thm8Data_eta

namespace GradSuffice

/-- **The affine pieces `(1/16) η_{t,k} · y_k(w) + b_{t,k} + Z_{t,k}`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §7, p.19
(inside the definition of `f_k`).

**Formalization Note.** 0-based `t`, `k`; `Z_{t,k}` is `Z (inr (inr (t, k)))`. -/
noncomputable def Thm8Data.affinePiece {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c : Thm8Data X) (t : Fin c.D) (k : Fin c.κ)
    (Z : c.NoiseIdx → ℝ) (w : X) : ℝ :=
  (1 / 16) * c.eta t k (c.y k w) + c.b t k + Z (.inr (.inr (t, k)))

end GradSuffice


