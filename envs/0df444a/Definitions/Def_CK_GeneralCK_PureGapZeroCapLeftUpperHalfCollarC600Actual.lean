-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarC600Actual
-- name    : CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarC600Actual
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T09:06:09.73359+00:00
-- url     : https://prove2.me/theorems/d519a8ab-a38f-4f92-941f-8b467842e627
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarC600Actual` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarC600Actual` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftUpperHalfCollarC600Actual` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftUpperHalfCollarC600Actual (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftUpperHalfCollarC600Actual.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarLogJets
import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarMiddleEta
import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarRadialJet
import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftUpperHalfCollarC600RadialAdapter

-- ===== source module GeneralCK.PureGapZeroCapLeftUpperHalfCollarC600Actual =====
section

/-!
Combination of the four actual-function error estimates for the left-upper
half-collar. The radial-contact estimate is supplied by `RadialJet`.
-/

namespace GeneralCK

private noncomputable def leftUpperHalfActualRadial (z w : ℝ) : ℝ :=
  let h := (H (1 / 2 - z) + H (1 / 2 - w)) / 2
  interiorCost (1 / 2 - z) (1 / 2 - w) +
    2 * F z h - F (z - w) h - eta h + eta (H (1 / 2 - w)) / 2

theorem leftUpper_halfCollar_actual_radial_error {z w : ℝ}
    (hw : 0 ≤ w) (hwz : w ≤ z) (hzmax : z ≤ 1 / 64) :
    |leftUpperHalfActualRadial z w -
      leftUpperHalfCombinedJet z w (Real.log 2)| ≤ 526 * z ^ 6 := by
  have hz : 0 ≤ z := hw.trans hwz
  have hrzw : 0 ≤ z - w := by linarith
  have hrzwz : z - w ≤ z := by linarith
  have hI := leftUpper_interior_half_bias_quartic_remainder hw hwz hzmax
  have hFz := leftUpper_F_half_bias_quartic_remainder
    hw hwz hzmax hz (le_refl z)
  have hFzw := leftUpper_F_half_bias_quartic_remainder
    hw hwz hzmax hrzw hrzwz
  have hM := leftUpper_middle_eta_quartic_remainder hw hwz hzmax
  have hB0 := leftUpper_eta_half_bias_quartic_remainder hw (hwz.trans hzmax)
  have hw6 : w ^ 6 ≤ z ^ 6 := by gcongr
  have hB :
      |eta (H (1 / 2 - w)) / 2 -
        leftUpperHalfEtaBJet w (Real.log 2)| ≤ 25 * z ^ 6 :=
    hB0.trans (by gcongr)
  apply abs_le.mpr
  constructor
  · unfold leftUpperHalfActualRadial leftUpperHalfCombinedJet
    dsimp
    linarith only [(abs_le.mp hI).1, (abs_le.mp hI).2,
      (abs_le.mp hFz).1, (abs_le.mp hFz).2,
      (abs_le.mp hFzw).1, (abs_le.mp hFzw).2,
      (abs_le.mp hM).1, (abs_le.mp hM).2,
      (abs_le.mp hB).1, (abs_le.mp hB).2]
  · unfold leftUpperHalfActualRadial leftUpperHalfCombinedJet
    dsimp
    linarith only [(abs_le.mp hI).1, (abs_le.mp hI).2,
      (abs_le.mp hFz).1, (abs_le.mp hFz).2,
      (abs_le.mp hFzw).1, (abs_le.mp hFzw).2,
      (abs_le.mp hM).1, (abs_le.mp hM).2,
      (abs_le.mp hB).1, (abs_le.mp hB).2]

theorem leftUpper_halfCollar_actual_C600
    {z lambda : ℝ} (hz : 0 < z) (hzmax : z ≤ 1 / 64)
    (hlambda : 0 < lambda) (hlambda1 : lambda < 1) :
    |(interiorCost (1 / 2 - z) (1 / 2 - lambda * z) +
        2 * F (1 / 2 - (1 / 2 - z))
          ((H (1 / 2 - z) + H (1 / 2 - lambda * z)) / 2) -
        F ((1 / 2 - lambda * z) - (1 / 2 - z))
          ((H (1 / 2 - z) + H (1 / 2 - lambda * z)) / 2) -
        eta ((H (1 / 2 - z) + H (1 / 2 - lambda * z)) / 2) +
        eta (H (1 / 2 - lambda * z)) / 2) -
      z ^ 4 * leftUpperQuarticCoefficient (Real.log 2) lambda| ≤
      600 * z ^ 6 := by
  have hw : 0 ≤ lambda * z := (mul_pos hlambda hz).le
  have hwz : lambda * z ≤ z := by
    nlinarith [mul_le_mul_of_nonneg_right hlambda1.le hz.le]
  have h := leftUpper_halfCollar_actual_radial_error hw hwz hzmax
  rw [leftUpperHalfCombinedJet_eq_quartic
    (z := z) (lambda := lambda) (L := Real.log 2) log_two_pos.ne'] at h
  have hz6 : 0 ≤ z ^ 6 := by positivity
  have h600 :
      |leftUpperHalfActualRadial z (lambda * z) -
        z ^ 4 * leftUpperQuarticCoefficient (Real.log 2) lambda| ≤
        600 * z ^ 6 := by
    linarith
  convert h600 using 1 <;> unfold leftUpperHalfActualRadial <;> ring

theorem leftUpper_halfCollar_nonneg_unconditional
    {z lambda : ℝ} (hz : 0 < z) (hzmax : z ≤ 1 / 64)
    (hlambda : 0 < lambda) (hlambda1 : lambda < 1) :
    0 ≤ canonicalPureGap (1 / 2 - z) (1 / 2)
      (H (1 / 2 - z)) (H (1 / 2 - lambda * z)) :=
  leftUpper_halfCollar_nonneg_of_radial_C600 hz hzmax hlambda hlambda1
    (leftUpper_halfCollar_actual_C600 hz hzmax hlambda hlambda1)

/-- The saved coefficient margin is strict on the half-collar, including its
outer face `z=1/64`. -/
theorem leftUpper_halfCollar_positive_unconditional
    {z lambda : ℝ} (hz : 0 < z) (hzmax : z ≤ 1 / 64)
    (hlambda : 0 < lambda) (hlambda1 : lambda < 1) :
    0 < canonicalPureGap (1 / 2 - z) (1 / 2)
      (H (1 / 2 - z)) (H (1 / 2 - lambda * z)) := by
  have ha : 0 < 1 / 2 - z := by linarith
  have hab : 1 / 2 - z < 1 / 2 - lambda * z := by
    nlinarith [mul_lt_mul_of_pos_right hlambda1 hz]
  have hb : 1 / 2 - lambda * z < 1 / 2 := by
    nlinarith [mul_pos hlambda hz]
  have hRad := canonicalPureGap_leftUpper_radial_eq ha hab hb
  have hlow := (abs_le.mp
    (leftUpper_halfCollar_actual_C600 hz hzmax hlambda hlambda1)).1
  have hP := leftUpperQuarticCoefficient_actual_lower lambda
  have hz2 : z ^ 2 ≤ (1 / 64 : ℝ) ^ 2 := by
    have hp : 0 ≤ ((1 / 64 : ℝ) - z) * ((1 / 64 : ℝ) + z) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith only [hp]
  have hsmall : 600 * z ^ 2 < (35 / 48 : ℝ) := by
    nlinarith only [hz2]
  have hcoef :
      0 < leftUpperQuarticCoefficient (Real.log 2) lambda - 600 * z ^ 2 := by
    linarith
  have hquartic :
      0 < z ^ 4 * leftUpperQuarticCoefficient (Real.log 2) lambda -
        600 * z ^ 6 := by
    have hp := mul_pos (pow_pos hz 4) hcoef
    nlinarith only [hp]
  rw [hRad]
  linarith only [hquartic, hlow]

#print axioms leftUpper_halfCollar_actual_radial_error
#print axioms leftUpper_halfCollar_actual_C600
#print axioms leftUpper_halfCollar_nonneg_unconditional
#print axioms leftUpper_halfCollar_positive_unconditional

end GeneralCK

end


