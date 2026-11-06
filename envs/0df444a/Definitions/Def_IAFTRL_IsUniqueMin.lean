-- Prove2me | Definitions.Def_IAFTRL_IsUniqueMin
-- name    : IAFTRL_IsUniqueMin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:40.91042+00:00
-- url     : https://prove2.me/theorems/d578c945-8ab5-46f8-8482-ec3b696c98c9
-- title:
--   Unique optimal action $a^*$
-- statement:
--   For a loss vector $\theta\in\mathbb R^d$, the action $a^*=a_{j^*}$ is the **unique optimal action** if
--   $$
--   a^{*\top}\theta<a^\top\theta\qquad\text{for every } a\in\mathcal A,\ a\ne a^* .
--   $$
--   Losses are minimized. The **loss gap** of an action is $\Delta(a)=(a-a^*)^\top\theta$, which is positive for every $a\ne a^*$; the paper assumes a unique optimal action throughout the stochastic and corrupted stochastic regimes.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Section 1.1, pp.5–6

import Mathlib

namespace IAFTRL

open Matrix

/-- **Unique optimal action.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Section 1.1, p.5: "Throughout this work, we assume
there exists a unique optimal action `a*` in the stochastic regime." Losses are minimized, so `a*`
is the unique minimizer of `a ↦ a^⊤θ` over `𝒜`.

`IsUniqueMin arms θ jstar` says that the action `arms jstar` has strictly smaller loss
`⟨arms jstar, θ⟩` than every other action. The loss gap of p.6 is then
`Δ(a_j) = (arms j − arms jstar)^⊤θ > 0` for `j ≠ jstar`. -/
def IsUniqueMin {d K : ℕ} (arms : Fin K → Fin d → ℝ) (θ : Fin d → ℝ) (jstar : Fin K) : Prop :=
  ∀ j, j ≠ jstar → arms jstar ⬝ᵥ θ < arms j ⬝ᵥ θ

end IAFTRL


