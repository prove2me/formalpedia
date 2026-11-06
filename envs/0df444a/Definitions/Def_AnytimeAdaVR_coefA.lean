-- Prove2me | Definitions.Def_AnytimeAdaVR_coefA
-- name    : AnytimeAdaVR_coefA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:00.083843+00:00
-- url     : https://prove2.me/theorems/822f7291-d732-4df3-8e9c-bd14b22c04af
-- title:
--   Constant $A_\Lambda$
-- statement:
--   $$
--   A_\Lambda=K_\Lambda^2+\frac{E_\Lambda^2}{4}\,(9\log K_\Lambda+2),
--   $$
--   the bound on the second moment $\mathbb E\,a_\infty^2$ of the limiting scale.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), App. C.3, eq. (42), p.22; eq. (63), p.30

import Mathlib
import Definitions.Def_AnytimeAdaVR_coefK

namespace AnytimeAdaVR

/-- **The constant `A_Λ = K_Λ² + (E_Λ²/4)(9 log K_Λ + 2)`**, the bound on `E a_∞²`. Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), App. C.3,
p.22, eq. (42) and App. G.1, p.30, eq. (63). -/
noncomputable def coefA (Δf L σ Λ : ℝ) : ℝ :=
  coefK Δf L σ Λ ^ 2 + coefE σ Λ ^ 2 / 4 * (9 * Real.log (coefK Δf L σ Λ) + 2)

end AnytimeAdaVR


