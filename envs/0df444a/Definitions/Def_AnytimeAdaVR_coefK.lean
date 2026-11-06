-- Prove2me | Definitions.Def_AnytimeAdaVR_coefK
-- name    : AnytimeAdaVR_coefK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:28:09.5431+00:00
-- url     : https://prove2.me/theorems/d443c755-424d-44b8-91fd-e7eb30ff5f9e
-- title:
--   Constant $K_\Lambda$
-- statement:
--   With $c_\Lambda=E_\Lambda+L/2$,
--   $$
--   K_\Lambda=2+\frac{\Delta_f}{2}+c_\Lambda+\frac{9c_\Lambda}{2}\log\big(\max\{1,9c_\Lambda/2\}\big).
--   $$
--   It bounds the expected final scale, $\mathbb E\,a_{J+1}\le K$.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), App. C.3, eq. (41), p.21; eq. (63), p.30

import Mathlib
import Definitions.Def_AnytimeAdaVR_coefE

namespace AnytimeAdaVR

/-- **The constant `K_Λ`.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), App. C.3, p.21, eq. (41) and App. G.1, p.30, eq. (63):
`c_Λ = E_Λ + L/2` and `K_Λ = 2 + ∆f/2 + c_Λ + (9c_Λ/2)·log(max{1, 9c_Λ/2})`. -/
noncomputable def coefK (Δf L σ Λ : ℝ) : ℝ :=
  let c := coefE σ Λ + L / 2
  2 + Δf / 2 + c + 9 * c / 2 * Real.log (max 1 (9 * c / 2))

end AnytimeAdaVR


