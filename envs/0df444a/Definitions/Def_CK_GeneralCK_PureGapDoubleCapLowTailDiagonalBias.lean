-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailDiagonalBias
-- name    : CK_GeneralCK_PureGapDoubleCapLowTailDiagonalBias
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T02:31:14.17302+00:00
-- url     : https://prove2.me/theorems/b3625b8a-d844-432b-924e-6c18f1887ebd
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapLowTailDiagonalBias` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapLowTailDiagonalBias` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapLowTailDiagonalBias` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapLowTailDiagonalBias (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapLowTailDiagonalBias.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailLinearSeparation
import Definitions.Def_CK_GeneralCK_PureGapDoubleCapOuterSlopeChecker
import Definitions.Def_CK_GeneralCK_SmallMeanCapTailBounds

-- ===== source module GeneralCK.PureGapDoubleCapLowTailDiagonalBias =====
section

/-! Exact cancellation in the double-cap bias expression when the contact
and inverse-entropy biases coincide. This isolates the cost of the true
contact displacement `y-c` in the remaining low-tail sign problem. -/

namespace GeneralCK

open Certificates.Reflection Reflection

theorem doubleCapSlopeBiasExpression_diagonal {y : ℝ}
    (hy : 0 < y) (hy1 : y < 1) :
    doubleCapSlopeBiasExpression y y =
      2 - 2 * y * biasE y /
        ((1 - y ^ 2) * SmallMean.A y * biasB y) := by
  have hgap : 0 < 1 - y ^ 2 := by
    nlinarith [mul_pos (by linarith : 0 < 1 - y)
      (by linarith : 0 < 1 + y)]
  have hAlo := SmallMean.A_ge_linear_cubic hy.le hy1
  have hApos : 0 < SmallMean.A y := by
    have hminor : 0 < y + y ^ 3 / 3 := by
      have hp : 0 < y * (1 + y ^ 2 / 3) :=
        mul_pos hy (by positivity)
      nlinarith only [hp]
    exact hminor.trans_le hAlo
  have hB : 0 < biasB y := biasB_pos_wide (by linarith [hy]) hy1
  have hident := biasB_eq_biasE_add (by linarith [hy]) hy1
  unfold doubleCapSlopeBiasExpression
  field_simp [hgap.ne', hApos.ne', hB.ne']
  nlinarith [hident]

#print axioms doubleCapSlopeBiasExpression_diagonal

end GeneralCK

end


