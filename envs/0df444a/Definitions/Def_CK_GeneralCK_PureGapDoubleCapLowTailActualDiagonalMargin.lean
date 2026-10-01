-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailActualDiagonalMargin
-- name    : CK_GeneralCK_PureGapDoubleCapLowTailActualDiagonalMargin
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:34:44.925983+00:00
-- url     : https://prove2.me/theorems/15beecfc-c2ec-4d04-bc86-3bd6b7093230
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapLowTailActualDiagonalMargin` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapLowTailActualDiagonalMargin` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapLowTailActualDiagonalMargin` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapLowTailActualDiagonalMargin (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapLowTailActualDiagonalMargin.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailYThreeQuarters
import Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailLinearSeparation

-- ===== source module GeneralCK.PureGapDoubleCapLowTailActualDiagonalMargin =====
section

/-! The actual inverse-entropy bias of the low double-cap tail has a
positive coincident-contact margin. Contact displacement remains open. -/

namespace GeneralCK

theorem doubleCapLowTail_actual_diagonal_margin_pos {m : ℝ}
    (hm : 0 < m) (hmq : m ≤ 1 / 4) :
    0 < doubleCapDiagonalMargin (doubleCapLowTailY m) := by
  have hh : 0 < H (2 * m) / 2 :=
    div_pos (H_pos (by linarith) (by linarith)) two_pos
  have hh1 : H (2 * m) / 2 < 1 :=
    (doubleCapLowFloor_lt_entropyCap hm hmq).trans_le (H_le_one m)
  have hy1 : doubleCapLowTailY m < 1 := by
    dsimp [doubleCapLowTailY]
    linarith [entropyInverse_pos hh hh1.le]
  exact doubleCapDiagonalMargin_pos_three_quarters
    (doubleCapLowTailY_ge_three_quarters hm hmq) hy1

#print axioms doubleCapLowTail_actual_diagonal_margin_pos

end GeneralCK

end


