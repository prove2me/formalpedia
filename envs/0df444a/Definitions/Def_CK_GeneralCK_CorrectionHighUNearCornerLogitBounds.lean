-- Prove2me | Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerLogitBounds
-- name    : CK_GeneralCK_CorrectionHighUNearCornerLogitBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T15:24:54.49519+00:00
-- url     : https://prove2.me/theorems/780e0b10-c4f3-4d7a-9ec3-ffc07df6d767
-- title:
--   Courtade–Kumar proof module `GeneralCK.CorrectionHighUNearCornerLogitBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CorrectionHighUNearCornerLogitBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CorrectionHighUNearCornerLogitBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CorrectionHighUNearCornerLogitBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionHighUNearCornerLogitBounds.lean)

import Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerEntropyBounds

namespace GeneralCK.Correction.HighU

theorem nearCorner_jn_eq_A (t : ℝ) :
    Natural.jn (1 / 2 - t) = 2 * SmallMean.A (2 * t) := by
  unfold Natural.jn SmallMean.A
  have heq : (1 - (1 / 2 - t)) / (1 / 2 - t) = (1 + 2 * t) / (1 - 2 * t) := by
    by_cases ht : t = 1 / 2
    · subst t; norm_num
    · field_simp [show (1 / 2 : ℝ) - t ≠ 0 by intro h; apply ht; linarith,
        show 1 - 2 * t ≠ 0 by intro h; apply ht; linarith]
      <;> ring
  rw [heq]
  ring

theorem nearCorner_jn_enclosure
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 100) :
    4 * t + (16 / 3 : ℝ) * t ^ 3 ≤ Natural.jn (1 / 2 - t) ∧
      Natural.jn (1 / 2 - t) ≤ 4 * t + (667 / 125 : ℝ) * t ^ 3 := by
  have hr0 : 0 ≤ 2 * t := by linarith
  have hr1 : 2 * t < 1 := by linarith
  have ht2 : t ^ 2 ≤ (1 / 10000 : ℝ) := by nlinarith
  have hden : 0 < 3 * (1 - (2 * t) ^ 2) := by nlinarith
  have hl := Real.sum_range_le_log_div hr0 hr1 2
  norm_num [Finset.sum_range_succ] at hl
  have hu := SmallMean.A_upper_sharp hr0 hr1
  have htail : (2 * t) ^ 3 / (3 * (1 - (2 * t) ^ 2)) ≤
      (667 / 250 : ℝ) * t ^ 3 := by
    apply (div_le_iff₀ hden).2
    have hcoef : 0 ≤ (667 / 250 : ℝ) * (3 * (1 - (2 * t) ^ 2)) - 8 := by
      nlinarith only [ht2]
    have hp := mul_nonneg (pow_nonneg ht 3) hcoef
    nlinarith only [hp]
  rw [nearCorner_jn_eq_A]
  constructor
  · unfold SmallMean.A
    nlinarith only [hl]
  · nlinarith only [hu, htail]

/-- The cubic remainder of the second logit retains its cancellation with
the first when the two probabilities coalesce. -/
theorem nearCorner_second_jn_lower
    {t rho : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 100)
    (hr : 0 ≤ rho) (hr1 : rho ≤ 1 / 100) :
    4 * t * (1 - rho) + 4 * t ^ 3 * ((4 / 3 : ℝ) - 4 * rho) ≤
      Natural.jn (1 / 2 - (1 - rho) * t) := by
  have hkt : 0 ≤ (1 - rho) * t := mul_nonneg (by linarith) ht
  have hkt1 : (1 - rho) * t ≤ 1 / 100 := by
    nlinarith only [mul_nonneg hr ht, ht1]
  have hj := (nearCorner_jn_enclosure hkt hkt1).1
  have hpoly : 0 ≤ rho ^ 2 * (3 - rho) :=
    mul_nonneg (sq_nonneg rho) (by linarith)
  have hp := mul_nonneg (pow_nonneg ht 3) hpoly
  nlinarith only [hj, hp]

#print axioms nearCorner_jn_eq_A
#print axioms nearCorner_jn_enclosure
#print axioms nearCorner_second_jn_lower

end GeneralCK.Correction.HighU


