-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_SizesRows7
-- name    : Formalism_GaussJetBounds_OneLetterGaussJets_SizesRows7
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:37.791436+00:00
-- url     : https://prove2.me/theorems/cd8fc409-cc25-4cf8-84d8-c3ec2ef84ed0
-- title:
--   Sizes Rows7
-- statement:
--   Definitions and structural lemmas for Sizes Rows7, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/SizesRows7.lean

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_MinWeightSumAddCostAbsBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
def SizesSign7 : Prop :=
  ∀ (H : Type) [Fintype H] (c wt wt' : H → ℝ) (k : ℝ), 1 ≤ k → (∀ t, (k - 1) * wt t ≤ c t) →
    (-((k - 1) / 2) * ∑ t, min (wt t) (wt' t)) + (1 / 2) * ∑ t, c t =
        (1 / 2) * ∑ t, (c t - (k - 1) * min (wt t) (wt' t)) ∧
      0 ≤ (-((k - 1) / 2) * ∑ t, min (wt t) (wt' t)) + (1 / 2) * ∑ t, c t
def SizesRows7 : Prop :=
  ∀ (k : ℕ) (N w w' : ℝ), 1 ≤ k → 1 ≤ N →
    (∀ (row : Fin k → ℝ) (rest : ℝ), 4 * k * N ≤ w → (∀ i, w - N - 1 / 2 < row i) → 0 ≤ rest →
      ((k : ℝ) - 1) * w < (∑ i, row i) + rest) ∧
    (∀ (row : Fin (k - 1) → ℝ) (rest first : ℝ), 4 * k * N ≤ w' → (∀ i, w - N < row i) → 0 ≤ rest →
      w' - N - 1 / 2 < first → ((k : ℝ) - 1) * w < (∑ i, row i) + rest + first)
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds


