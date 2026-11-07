-- Prove2me | Definitions.Def_EffHorizonProphet_Calibrated
-- name    : EffHorizonProphet_Calibrated
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:43:37.299515+00:00
-- url     : https://prove2.me/theorems/a51d2118-fc82-4304-a03e-e3af4f66e88d
-- title:
--   Calibration to the effective horizon: acceptance probability $1/B$
-- statement:
--   A sequence of policies is **calibrated** if, for every $t$ with $B_t\ge1$ and every admissible law $D$, its rule at $D$ has acceptance probability exactly $1/B_t$, where $B_t$ is the effective horizon of the profile $L_t$. This is the policy of Algorithm 1 with the threshold (6), and Remark 5 for atoms.
--
--   **Formalization Note** The guard $B_t\ge1$ excludes small horizons where $1/B_t$ is not a probability. It holds eventually along an asymptotically equal profile.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Eq. (6), p.8; Algorithm 1 and Remark 5, p.9; Remark 16, p.31

import Mathlib
import Definitions.Def_EffHorizonProphet_IsAdmissible
import Definitions.Def_EffHorizonProphet_effHorizon
import Definitions.Def_EffHorizonProphet_acceptProb

open MeasureTheory

namespace EffHorizonProphet

/-- A family of rules is **calibrated to the effective horizon** (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Eq. (6), p.8; Algorithm 1,
Remark 5, p.9; Remark 16, p.31): at every admissible law its acceptance probability is exactly
`a/n = 1/B`.

**Formalization Note** Any threshold and tie-break with acceptance probability `1/B` differ only on
`D`-null sets, so this is the policy of Algorithm 1 with (6) and Remark 5. The guard `1 ≤ B` excludes
small horizons, where `1/B` is not a probability (or `B = 0`); the paper uses `B ≥ 1` in (39), and it
holds eventually along an equal-length profile. -/
def Calibrated {S : ℕ} (γ : ℝ) (L : ℕ → Fin S → ℕ) (π : ℕ → Measure ℝ → Rule) : Prop :=
  ∀ t D, IsAdmissible D → 1 ≤ effHorizon γ (L t) →
    acceptProb D (π t D) = 1 / effHorizon γ (L t)

end EffHorizonProphet


