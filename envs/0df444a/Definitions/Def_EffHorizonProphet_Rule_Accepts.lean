-- Prove2me | Definitions.Def_EffHorizonProphet_Rule_Accepts
-- name    : EffHorizonProphet_Rule_Accepts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:41:35.164454+00:00
-- url     : https://prove2.me/theorems/95d2767b-f403-47fd-a22b-1b8d69699b41
-- title:
--   The randomized acceptance event $A_i$
-- statement:
--   A rule $(\alpha,\theta)$ **accepts** a stage with base reward $y$ and coin $u\in[0,1]$ if $y>\alpha$, or if $y=\alpha$ and $u\le\theta$. This is the event
--   $$A_i=\{X_i>\alpha_s\}\cup\{X_i=\alpha_s,\ U_i\le\theta\}$$
--   of Remark 16, written in the base scale.
--
--   **Formalization Note** The comparison is made in $[0,\infty]$ through the embedding of $y$, which sends negative $y$ to $0$; under an admissible law negative values have probability $0$.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Remark 16, p.31

import Mathlib
import Definitions.Def_EffHorizonProphet_Rule

namespace EffHorizonProphet

/-- The **randomized acceptance event** of a rule at a stage with base reward `y` and coin `u`
(Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Remark 16, p.31): `A_i = {X_i > α_s} ∪ {X_i = α_s, U_i ≤ θ}`, rewritten in the base scale
as `Y_i > α₁` or (`Y_i = α₁` and `U_i ≤ θ`).

**Formalization Note** For `γ̃ > 0` the base-scale event is the paper's, since
`X_i = γ̃^{s-1} Y_i` and `α_s = γ̃^{s-1} α₁`. At `γ̃ = 0` it may stop in a phase `s ≥ 2`, where the
reward is `0` either way (footnote 3, p.8). -/
def Rule.Accepts (ρ : Rule) (y : ℝ) (u : unitInterval) : Prop :=
  ρ.α < ENNReal.ofReal y ∨ (ρ.α = ENNReal.ofReal y ∧ (u : ℝ) ≤ ρ.θ)

end EffHorizonProphet


