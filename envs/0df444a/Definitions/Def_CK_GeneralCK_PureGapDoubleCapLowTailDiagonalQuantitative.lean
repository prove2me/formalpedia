-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailDiagonalQuantitative
-- name    : CK_GeneralCK_PureGapDoubleCapLowTailDiagonalQuantitative
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T07:03:31.571984+00:00
-- url     : https://prove2.me/theorems/e2fcd412-83c7-43c1-9dd2-0e94314b372b
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapLowTailDiagonalQuantitative` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapLowTailDiagonalQuantitative` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapLowTailDiagonalQuantitative` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapLowTailDiagonalQuantitative (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapLowTailDiagonalQuantitative.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailHighBiasAnchors
import Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailDiagonalBias

-- ===== source module GeneralCK.PureGapDoubleCapLowTailDiagonalQuantitative =====
section

/-! A quantitative coincident-contact slope lower bound in the near-zero
double-cap tail. -/

namespace GeneralCK

open Certificates.Reflection Reflection

theorem doubleCapLowTail_diagonal_slope_ge_four_thirds {y : ℝ}
    (hy : 49 / 50 ≤ y) (hy1 : y < 1) :
    4 / 3 ≤ doubleCapSlopeBiasExpression y y := by
  have hy0 : 0 < y := by linarith
  have hd : 0 < 1 - y := by linarith
  have hD : 0 < 1 - y ^ 2 := by nlinarith
  have hA := doubleCapLowTail_A_ge_207 hy hy1
  have hB := doubleCapLowTail_B_ge_207 hy hy1
  have hApos : 0 < SmallMean.A y := by linarith
  have hBpos : 0 < biasB y := by linarith
  have hDen : 0 < (1 - y ^ 2) * SmallMean.A y * biasB y :=
    mul_pos (mul_pos hD hApos) hBpos
  have hE := doubleCapLowTail_E_le_five_fourths_gap_B hy hy1
  have hNum : 2 * y * biasE y ≤
      (5 / 2) * y * (1 - y) * biasB y := by
    have h := mul_le_mul_of_nonneg_left hE (by linarith : 0 ≤ 2 * y)
    nlinarith only [h]
  have hAProduct : (207 / 100) * (1 + y) ≤
      SmallMean.A y * (1 + y) :=
    mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1 + y)
  have hCoef : (5 / 2) * y ≤
      (2 / 3) * (1 + y) * SmallMean.A y := by
    nlinarith [hAProduct, hy1.le]
  have hScaled := mul_le_mul_of_nonneg_right hCoef
    (mul_nonneg hd.le hBpos.le)
  have hDenBound : (5 / 2) * y * (1 - y) * biasB y ≤
      (2 / 3) * ((1 - y ^ 2) * SmallMean.A y * biasB y) := by
    nlinarith only [hScaled]
  have hFraction : 2 * y * biasE y /
      ((1 - y ^ 2) * SmallMean.A y * biasB y) ≤ 2 / 3 := by
    apply (div_le_iff₀ hDen).mpr
    linarith only [hNum, hDenBound]
  rw [doubleCapSlopeBiasExpression_diagonal hy0 hy1]
  linarith only [hFraction]

#print axioms doubleCapLowTail_diagonal_slope_ge_four_thirds

end GeneralCK

end


