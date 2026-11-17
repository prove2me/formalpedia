-- Prove2me | Definitions.Def_EffHorizonProphet_Supplement_gamblerG
-- name    : EffHorizonProphet_Supplement_gamblerG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:02:26.897255+00:00
-- url     : https://prove2.me/theorems/6b8eb2e1-e25f-4c2d-b2fb-614f806ad487
-- title:
--   Expected reward of a single-threshold rule, general model
-- statement:
--   For a rule with base threshold $\alpha$ and tie-break $\theta$, $\tau$ is the first stage whose randomized acceptance event holds, and this item is $\mathbb E_D[X_\tau]$ with $X_i=\Gamma_{s-1}Y_i$ and payoff $0$ if no stage accepts.
--
--   **Formalization Note** Acceptance is tested in the base scale ($Y_i$ against $\alpha$, published `stopsAt`). In a phase with $\Gamma_{s-1}=0$ every later reward is also $0$, so stopping there pays the same as never stopping (footnote 5, p.35).
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), A.7, Eq. (49), p.36

import Mathlib
import Definitions.Def_EffHorizonProphet_stopsAt
import Definitions.Def_EffHorizonProphet_sampleLaw
import Definitions.Def_EffHorizonProphet_Supplement_rewardG

open MeasureTheory

namespace EffHorizonProphet.Supplement

open scoped Classical in
/-- The **expected reward of a single-threshold rule in the general model**
`E_D[X_τ] = ∑_i E_D[X_i 1{τ = i}]` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), A.7, p.36, Eq. (49)), with payoff `0` if no stage accepts.

**Formalization Note** As the base mission's `gambler`, with the general scale `Γ`: `τ` is the first
stage whose randomized acceptance event holds (`stopsAt`, tested in the base scale `Y_i` vs `α`).
In a phase with `Γ_{s−1} = 0` every later reward is `0` too, so stopping there pays the same `0` as
never stopping (footnote 5, p.35). -/
noncomputable def gamblerG {S : ℕ} (g : ℕ → ℝ) (L : Fin S → ℕ) (D : Measure ℝ)
    (ρ : Rule) : ℝ :=
  ∫ ω, ∑ i, (if stopsAt ρ ω i then rewardG g L i ω else 0) ∂sampleLaw D L

end EffHorizonProphet.Supplement


