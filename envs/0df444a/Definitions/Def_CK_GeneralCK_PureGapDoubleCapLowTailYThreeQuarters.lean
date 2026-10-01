-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailYThreeQuarters
-- name    : CK_GeneralCK_PureGapDoubleCapLowTailYThreeQuarters
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:24:24.238462+00:00
-- url     : https://prove2.me/theorems/c341c7c1-cff3-4469-ab94-b418f9d8d335
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapLowTailYThreeQuarters` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapLowTailYThreeQuarters` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapLowTailYThreeQuarters` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapLowTailYThreeQuarters (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapLowTailYThreeQuarters.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailDiagonalMarginPositive
import Definitions.Def_CK_GeneralCK_PsiNormalizedLowEntropy

-- ===== source module GeneralCK.PureGapDoubleCapLowTailYThreeQuarters =====
section

/-! An exact eighth-entropy anchor puts the low-tail inverse bias in the
three-quarter region where the diagonal margin has been certified. -/

namespace GeneralCK

theorem H_eighth_gt_half : (1 / 2 : ℝ) < H (1 / 8) := by
  have h := H_mul_log_two_ge (p := (1 / 8 : ℝ)) (by norm_num) (by norm_num)
  have hInv : ((1 / 8 : ℝ)⁻¹) = 2 ^ (3 : ℕ) := by norm_num
  rw [hInv, Real.log_pow] at h
  nlinarith only [h, log_two_upper, log_two_pos]

theorem doubleCapLowTailY_ge_three_quarters {m : ℝ}
    (hm : 0 < m) (hmq : m ≤ 1 / 4) :
    3 / 4 ≤ doubleCapLowTailY m := by
  have hh : 0 ≤ H (2 * m) / 2 := by
    exact div_nonneg (H_nonneg (by linarith) (by linarith)) (by norm_num)
  have hhalf : H (2 * m) / 2 ≤ H (1 / 8) := by
    linarith [H_le_one (2 * m), H_eighth_gt_half]
  have hinv := entropyInverse_mono hh (H_le_one (1 / 8)) hhalf
  rw [entropyInverse_H_lower (by norm_num : (0 : ℝ) ≤ 1 / 8)
    (by norm_num : (1 / 8 : ℝ) ≤ 1 / 2)] at hinv
  dsimp [doubleCapLowTailY]
  linarith only [hinv]

#print axioms H_eighth_gt_half
#print axioms doubleCapLowTailY_ge_three_quarters

end GeneralCK

end


