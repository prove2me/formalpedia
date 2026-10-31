-- Prove2me | Definitions.Def_TechBreakthrough_Model_hitTransform
-- name    : TechBreakthrough_Model_hitTransform
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:34:31.985434+00:00
-- url     : https://prove2.me/theorems/14b9402a-dbc7-4434-8210-b869d0f3b4b0
-- title:
--   The transform $\mathbf E_x[e^{-r\tau(y)}]$ and $M_\tau$ with values in $\overline{\mathbb R}$
-- statement:
--   The hitting time of $y$ is $\tau(y)=\inf\{t\ge0:X_t=y\}$, and the transform of (15) is the map $(x,y)\mapsto\mathbf E_x[e^{-r\tau(y)}]$, with $e^{-r\infty}=0$. For a stopping time $\tau$, $M_\tau$ is taken with values in the extended reals: on $\{\tau=\infty\}$ it is $\sup_tM_t$, which may equal $\beta$.
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, (15), p.11; (22), p.14

import Definitions.Def_TechBreakthrough_Model_payoff

open MeasureTheory
open scoped NNReal

namespace TechBreakthrough

namespace Model

variable (M : Model)

/-- The hitting time `τ(y) = inf {t ≥ 0 : X_t = y}`, arXiv:2106.05112v1, p.11. -/
noncomputable def hitTime (ω : M.Ω) (y : ℝ) : WithTop ℝ≥0 := firstTime {t | M.X t ω = y}

/-- The transform `(x, y) ↦ E_x[e^{−rτ(y)}]` of (15), arXiv:2106.05112v1, p.11, with
`e^{−r∞} = 0`. -/
noncomputable def hitTransform (x y : ℝ) : ℝ :=
  ∫ ω, discountedAt M.r (fun _ => 1) (M.hitTime ω y) ∂M.P x

/-- `M_τ` with values in `EReal`: on `{τ = ∞}` it is `sup_t M_t`, which may equal `β`. -/
noncomputable def maxAt (m : ℝ) (τ : M.Ω → WithTop ℝ≥0) (ω : M.Ω) : EReal :=
  ⨆ t : ℝ≥0, ⨆ _ : (t : WithTop ℝ≥0) ≤ τ ω, (runningMax m t ω : EReal)

end Model

end TechBreakthrough


