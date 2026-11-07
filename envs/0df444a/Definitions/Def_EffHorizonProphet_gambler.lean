-- Prove2me | Definitions.Def_EffHorizonProphet_gambler
-- name    : EffHorizonProphet_gambler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:43:49.436597+00:00
-- url     : https://prove2.me/theorems/d5068306-64d5-4728-9c50-a62114d934df
-- title:
--   The expected reward $\mathbb E_D[X_\tau]$ of a rule
-- statement:
--   The **expected reward** of a rule is
--   $$\mathbb E_D[X_\tau]=\sum_{i=1}^n\mathbb E_D\big[X_i\mathbf 1\{\tau=i\}\big],$$
--   with payoff $0$ when no stage is accepted. It is the expectation of the stopped reward under the sample law, not a closed form; the closed form is a milestone.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Section 3, p.3

import Mathlib
import Definitions.Def_EffHorizonProphet_reward
import Definitions.Def_EffHorizonProphet_stopsAt
import Definitions.Def_EffHorizonProphet_sampleLaw

open MeasureTheory

namespace EffHorizonProphet

open scoped Classical in
/-- The **expected reward of a rule**, `E_D[X_τ] = ∑_{i ∈ [n]} E_D[X_i 1{τ = i}]` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Section 3,
p.3), with payoff `0` when `τ = n + 1`. It is the expectation of the stopped reward under the
product law, not a closed form. -/
noncomputable def gambler {S : ℕ} (γ : ℝ) (L : Fin S → ℕ) (D : Measure ℝ) (ρ : Rule) : ℝ :=
  ∫ ω, ∑ i, (if stopsAt ρ ω i then reward γ L i ω else 0) ∂sampleLaw D L

end EffHorizonProphet


