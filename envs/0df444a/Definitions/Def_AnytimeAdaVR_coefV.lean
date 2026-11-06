-- Prove2me | Definitions.Def_AnytimeAdaVR_coefV
-- name    : AnytimeAdaVR_coefV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:02.76208+00:00
-- url     : https://prove2.me/theorems/0794e1df-0bc7-44a4-8e5c-125370e36006
-- title:
--   Constant $V_\Lambda$
-- statement:
--   With $c_\Lambda=E_\Lambda+L/2$,
--   $$
--   V_\Lambda=2L\big(\Delta_f+c_\Lambda(9\log K_\Lambda+2)\big),
--   $$
--   the bound on the second moment $\mathbb E\,G_\infty^2$ of the largest gradient norm visited by the path.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), App. C.4, eq. (43), p.22; eq. (63), p.30

import Mathlib
import Definitions.Def_AnytimeAdaVR_coefK

namespace AnytimeAdaVR

/-- **The constant `V_Λ = 2L(∆f + c_Λ(9 log K_Λ + 2))`**, the bound on `E G_∞²`. Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), App. C.4,
p.22, eq. (43) and App. G.1, p.30, eq. (63), with `c_Λ = E_Λ + L/2`. -/
noncomputable def coefV (Δf L σ Λ : ℝ) : ℝ :=
  2 * L * (Δf + (coefE σ Λ + L / 2) * (9 * Real.log (coefK Δf L σ Λ) + 2))

end AnytimeAdaVR


