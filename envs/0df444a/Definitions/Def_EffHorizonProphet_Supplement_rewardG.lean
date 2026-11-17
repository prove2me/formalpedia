-- Prove2me | Definitions.Def_EffHorizonProphet_Supplement_rewardG
-- name    : EffHorizonProphet_Supplement_rewardG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:01:47.645962+00:00
-- url     : https://prove2.me/theorems/ed4eb1cd-d1e2-45fa-86c9-76e17c398bc1
-- title:
--   Observed reward $X_i=\Gamma_{s-1}Y_i$ of the general model
-- statement:
--   In the general decaying-reward model the reward at stage $i$ of phase $s$ is $X_i=\Gamma_{s-1}Y_i$.
--
--   **Formalization Note** Phases are numbered from $0$; with a common decay factor this is the published `reward` (sanity file).
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Section 3, p.3; A.6, p.35

import Mathlib
import Definitions.Def_EffHorizonProphet_phaseOf
import Definitions.Def_EffHorizonProphet_Supplement_cumScale

namespace EffHorizonProphet.Supplement

/-- The **observed reward of the general model** `X_i = Γ_{s−1} Y_i` for `i ∈ T_s` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Section 3,
p.3; A.6, p.35; A.8, p.39).

**Formalization Note** `0`-based phases: the scale of stage `i` is `cumScale g (phaseOf L i)`. With
`g ≡ γ̃` it is the base mission's `reward γ̃` (see the sanity file). -/
def rewardG {S : ℕ} (g : ℕ → ℝ) (L : Fin S → ℕ) (i : Fin (∑ s, L s))
    (ω : Fin (∑ s, L s) → ℝ × unitInterval) : ℝ :=
  cumScale g (phaseOf L i : ℕ) * (ω i).1

end EffHorizonProphet.Supplement


