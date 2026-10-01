-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailHighBiasAnchors
-- name    : CK_GeneralCK_PureGapDoubleCapLowTailHighBiasAnchors
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:15:26.888877+00:00
-- url     : https://prove2.me/theorems/d5ef5702-8c85-40e1-87e1-9ffcb0c14911
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapLowTailHighBiasAnchors` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapLowTailHighBiasAnchors` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapLowTailHighBiasAnchors` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapLowTailHighBiasAnchors (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapLowTailHighBiasAnchors.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailHalfGap
import Definitions.Def_CK_GeneralCK_Certificates_MixedConstants

-- ===== source module GeneralCK.PureGapDoubleCapLowTailHighBiasAnchors =====
section

/-! Uniform logarithmic and entropy bounds in the high-bias part of the
double-cap low tail. All constants are exact rationals. -/

namespace GeneralCK

open Certificates.Reflection Reflection

theorem doubleCapLowTail_A_ge_207 {z : ℝ}
    (hz : 49 / 50 ≤ z) (hz1 : z < 1) :
    207 / 100 ≤ SmallMean.A z := by
  have hp : 0 < 1 + z := by linarith
  have hm : 0 < 1 - z := by linarith
  have hRatio : (64 : ℝ) ≤ (1 + z) / (1 - z) := by
    apply (le_div_iff₀ hm).mpr
    nlinarith [hz]
  have hLog := Real.log_le_log (by norm_num : (0 : ℝ) < 64) hRatio
  have hLog64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hLog64] at hLog
  unfold SmallMean.A
  nlinarith [hLog, Certificates.Mixed.log_two_gt_69]

theorem doubleCapLowTail_B_ge_207 {z : ℝ}
    (hz : 49 / 50 ≤ z) (hz1 : z < 1) :
    207 / 100 ≤ biasB z := by
  have hD : 0 < 1 - z * z := by nlinarith
  have hD16 : 1 - z * z ≤ (1 / 16 : ℝ) := by nlinarith [hz]
  have hLog := Real.log_le_log hD hD16
  have hLog16 : Real.log (1 / 16 : ℝ) = -4 * Real.log 2 := by
    rw [show (1 / 16 : ℝ) = ((2 : ℝ) ^ (4 : ℕ))⁻¹ by norm_num,
      Real.log_inv, Real.log_pow]
    norm_num
  rw [hLog16] at hLog
  unfold biasB
  nlinarith [hLog, Certificates.Mixed.log_two_gt_69]

theorem doubleCapLowTail_A_le_B {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z < 1) :
    SmallMean.A z ≤ biasB z := by
  have hp : 0 < 1 + z := by linarith
  have hm : 0 < 1 - z := by linarith
  have hD : 0 < 1 - z * z := by nlinarith
  have hPlus : Real.log (1 + z) ≤ Real.log 2 :=
    Real.log_le_log hp (by linarith)
  have hLogD : Real.log (1 - z * z) =
      Real.log (1 + z) + Real.log (1 - z) := by
    rw [show 1 - z * z = (1 + z) * (1 - z) by ring,
      Real.log_mul hp.ne' hm.ne']
  unfold SmallMean.A biasB
  rw [Real.log_div hp.ne' hm.ne', hLogD]
  linarith only [hPlus]

theorem doubleCapLowTail_E_le_five_fourths_gap_B {z : ℝ}
    (hz : 49 / 50 ≤ z) (hz1 : z < 1) :
    biasE z ≤ (5 / 4) * (1 - z) * biasB z := by
  have hp : 0 < 1 + z := by linarith
  have hm : 0 < 1 - z := by linarith
  have hz0 : 0 ≤ z := by linarith
  have hLog := Real.log_le_sub_one_of_pos
    (div_pos (by norm_num : (0 : ℝ) < 2) hp)
  have hLogTerm : Real.log 2 - Real.log (1 + z) ≤
      (1 - z) / (1 + z) := by
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hp.ne'] at hLog
    have hFrac : 2 / (1 + z) - 1 = (1 - z) / (1 + z) := by
      field_simp [hp.ne']
      ring
    simpa only [hFrac] using hLog
  have hEIdentity : biasE z = (1 - z) * SmallMean.A z +
      (Real.log 2 - Real.log (1 + z)) := by
    unfold biasE SmallMean.A
    rw [Real.log_div hp.ne' hm.ne']
    ring
  have hEUpper : biasE z ≤
      (1 - z) * SmallMean.A z + (1 - z) / (1 + z) := by
    rw [hEIdentity]
    linarith only [hLogTerm]
  have hAB := doubleCapLowTail_A_le_B hz0 hz1
  have hB := doubleCapLowTail_B_ge_207 hz hz1
  have hDen : (4 : ℝ) ≤ (1 + z) * biasB z := by
    have h := mul_le_mul_of_nonneg_left hB hp.le
    nlinarith [h, hz]
  have hFrac : 1 / (1 + z) ≤ biasB z / 4 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [hDen]
  have hAProd := mul_le_mul_of_nonneg_left hAB hm.le
  have hFracProd := mul_le_mul_of_nonneg_left hFrac hm.le
  have hFracProd' : (1 - z) / (1 + z) ≤
      (1 - z) * biasB z / 4 := by
    simpa only [div_eq_mul_inv, one_mul, mul_assoc] using hFracProd
  nlinarith only [hEUpper, hAProd, hFracProd']

#print axioms doubleCapLowTail_A_ge_207
#print axioms doubleCapLowTail_B_ge_207
#print axioms doubleCapLowTail_A_le_B
#print axioms doubleCapLowTail_E_le_five_fourths_gap_B

end GeneralCK

end


