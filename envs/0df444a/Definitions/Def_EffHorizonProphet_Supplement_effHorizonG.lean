-- Prove2me | Definitions.Def_EffHorizonProphet_Supplement_effHorizonG
-- name    : EffHorizonProphet_Supplement_effHorizonG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:00:40.354348+00:00
-- url     : https://prove2.me/theorems/861c934f-6d19-4081-bb2d-e0de6daffd79
-- title:
--   Effective horizon $B_G=\sum_s\Gamma_{s-1}n_s$
-- statement:
--   For phase lengths $n_1,\dots,n_S$, the **effective horizon** of the general model is
--   $$B_G=\sum_{s=1}^{S}\Gamma_{s-1}n_s,$$
--   the effective number of discounted opportunities. The calibration (48) chooses acceptance probability $\tilde a/n=1/B_G$. With a common decay factor it is the published `effHorizon` (sanity file).
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), A.6, p.35

import Mathlib
import Definitions.Def_EffHorizonProphet_Supplement_cumScale

namespace EffHorizonProphet.Supplement

/-- The **effective horizon of the general model** `B_G = ∑_{s=1}^{S} Γ_{s−1} n_s` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), A.6, p.35),
for phase lengths `n_s`. By (48), the calibrated acceptance probability is `ã/n = 1/B_G`.

**Formalization Note** `0`-based phases: `∑_s L s · cumScale g s`, with `L s` the length of Lean phase
`s`. With `g ≡ γ̃` it is the base mission's `effHorizon`. -/
noncomputable def effHorizonG {S : ℕ} (g : ℕ → ℝ) (L : Fin S → ℕ) : ℝ :=
  ∑ s : Fin S, (L s : ℝ) * cumScale g (s : ℕ)

end EffHorizonProphet.Supplement


