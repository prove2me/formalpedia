-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailHalfGap
-- name    : CK_GeneralCK_PureGapDoubleCapLowTailHalfGap
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:34:52.362297+00:00
-- url     : https://prove2.me/theorems/86470db7-eb6a-426a-9810-7a9393c0f38e
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapLowTailHalfGap` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapLowTailHalfGap` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapLowTailHalfGap` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapLowTailHalfGap (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapLowTailHalfGap.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailYThreeQuarters
import Definitions.Def_CK_GeneralCK_PsiNormalizedLowEntropy

-- ===== source module GeneralCK.PureGapDoubleCapLowTailHalfGap =====
section

/-! A tail entropy comparison keeps the inverse-entropy bias a definite
distance from one. This gap will enter the secant loss estimate. -/

namespace GeneralCK

theorem H_half_m_le_H_two_m_half {m : ℝ}
    (hm : 0 < m) (hm8 : m ≤ 1 / 8) :
    H (m / 2) ≤ H (2 * m) / 2 := by
  have hp : 0 < m / 2 := by positivity
  have hp1 : m / 2 < 1 := by linarith
  have hq : 0 < 2 * m := by linarith
  have hq1 : 2 * m < 1 := by linarith
  have hUpper := H_mul_log_two_le hp hp1
  have hLower := H_mul_log_two_ge hq hq1
  have hInv : (8 : ℝ) ≤ m⁻¹ := by
    have hDiv : (8 : ℝ) ≤ 1 / m :=
      (le_div_iff₀ hm).mpr (by nlinarith [hm8])
    simpa only [one_div] using hDiv
  have hLog := Real.log_le_log (by norm_num : (0 : ℝ) < 8)
    hInv
  have hLogThree : 3 * Real.log 2 ≤ Real.log m⁻¹ := by
    convert hLog using 1
    · rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
      norm_num
  have hHalfLog : Real.log (m / 2)⁻¹ = Real.log m⁻¹ + Real.log 2 := by
    rw [show (m / 2)⁻¹ = 2 * m⁻¹ by field_simp [hm.ne'], Real.log_mul
      (by norm_num : (2 : ℝ) ≠ 0) (inv_ne_zero hm.ne')]
    ring
  have hDoubleLog : Real.log (2 * m)⁻¹ = Real.log m⁻¹ - Real.log 2 := by
    rw [show (2 * m)⁻¹ = m⁻¹ / 2 by field_simp [hm.ne'],
      Real.log_div (inv_ne_zero hm.ne') (by norm_num : (2 : ℝ) ≠ 0)]
  rw [hHalfLog] at hUpper
  rw [hDoubleLog] at hLower
  have hMulLog : 3 * m * Real.log 2 ≤ m * Real.log m⁻¹ := by
    nlinarith [mul_le_mul_of_nonneg_left hLogThree hm.le]
  have hMargin : 0 ≤ m * (1 / 2 - 2 * m) :=
    mul_nonneg hm.le (by linarith [hm8])
  have hResult : H (m / 2) * Real.log 2 ≤
      (H (2 * m) / 2) * Real.log 2 := by
    nlinarith [hUpper, hLower, hMulLog, hMargin]
  by_contra h
  have hStrict : H (2 * m) / 2 < H (m / 2) := lt_of_not_ge h
  have hStrictMul := mul_lt_mul_of_pos_right hStrict log_two_pos'
  linarith only [hResult, hStrictMul]

theorem doubleCapLowTailY_le_one_sub_m {m : ℝ}
    (hm : 0 < m) (hm8 : m ≤ 1 / 8) :
    doubleCapLowTailY m ≤ 1 - m := by
  have hp0 : 0 ≤ H (m / 2) := H_nonneg (by linarith) (by linarith)
  have hp1 : H (m / 2) ≤ 1 := H_le_one (m / 2)
  have hq1 : H (2 * m) / 2 ≤ 1 := by linarith [H_le_one (2 * m)]
  have hInverse := entropyInverse_mono hp0 hq1
    (H_half_m_le_H_two_m_half hm hm8)
  rw [entropyInverse_H_lower (by linarith : 0 ≤ m / 2)
    (by linarith : m / 2 ≤ 1 / 2)] at hInverse
  dsimp [doubleCapLowTailY]
  linarith only [hInverse]

#print axioms H_half_m_le_H_two_m_half
#print axioms doubleCapLowTailY_le_one_sub_m

end GeneralCK

end


