-- Prove2me | Definitions.Def_EffHorizonProphet_Supplement_infGambler
-- name    : EffHorizonProphet_Supplement_infGambler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:59:01.922494+00:00
-- url     : https://prove2.me/theorems/2f638389-05be-4954-933e-8934a9f16e57
-- title:
--   Expected reward of the infinite-horizon quantile rule
-- statement:
--   For a base threshold $\alpha$ and a tie-breaking probability $\theta$, the **infinite-horizon quantile rule** stops at the first stage $i$ with
--   $$X_i>\tilde\gamma^{i-1}\alpha\quad\text{or}\quad\big(X_i=\tilde\gamma^{i-1}\alpha\ \text{and}\ U_i\le\theta\big),$$
--   and receives $0$ if no stage accepts. This item is its expected reward.
--
--   **Formalization Note** Acceptance is tested in the base scale, $Y_i$ against $\alpha$ (the published `Rule.Accepts`), which is the same event since $\tilde\gamma>0$. The expectation is a lower Lebesgue integral in $[0,\infty]$.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Theorem 10, p.12; A.11, p.52

import Mathlib
import Definitions.Def_EffHorizonProphet_Rule_Accepts
import Definitions.Def_EffHorizonProphet_Supplement_infSampleLaw
import Definitions.Def_EffHorizonProphet_Supplement_infReward

open MeasureTheory
open scoped ENNReal

namespace EffHorizonProphet.Supplement

open scoped Classical in
/-- The **expected reward of the infinite-horizon quantile rule** (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Theorem 10, p.12; A.11,
p.52): with base threshold `α` and tie-breaking probability `θ` (a `Rule`), stop at the first stage
`i` whose acceptance event `{X_i > γ̃^{i−1} α} ∪ {X_i = γ̃^{i−1} α, U_i ≤ θ}` holds; payoff `0` if no
stage accepts.

**Formalization Note** Acceptance is tested in the base scale, `Y_i` against `α` (`Rule.Accepts`),
which is the paper's event because `γ̃ > 0` in Section 7. The expectation is a lower Lebesgue
integral in `ℝ≥0∞` of `∑' i, 1{τ = i} · ofReal (X_i)`. -/
noncomputable def infGambler (γ : ℝ) (D : Measure ℝ) (ρ : Rule) : ℝ≥0∞ :=
  ∫⁻ ω, ∑' i : ℕ,
    (if ρ.Accepts (ω i).1 (ω i).2 ∧ ∀ j, j < i → ¬ ρ.Accepts (ω j).1 (ω j).2 then
      ENNReal.ofReal (infReward γ i ω) else 0) ∂infSampleLaw D

end EffHorizonProphet.Supplement


