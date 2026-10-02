-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailSevenSixteenthsValue
-- name    : CK_GeneralCK_PureGapDoubleCapHighTailSevenSixteenthsValue
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T19:06:41.839859+00:00
-- url     : https://prove2.me/theorems/e26fa04f-297f-44c6-8249-a5cfc3574965
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapHighTailSevenSixteenthsValue` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapHighTailSevenSixteenthsValue` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapHighTailSevenSixteenthsValue` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapHighTailSevenSixteenthsValue (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapHighTailSevenSixteenthsValue.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighTailSevenSixteenthsActualSign

-- ===== source module GeneralCK.PureGapDoubleCapHighTailSevenSixteenthsValue =====
section

/-! Direct true endpoint-value consequence of the checked `m≥15/32` slope. -/

namespace GeneralCK

theorem doubleCapHighResidual_nonneg_on_seven_tail {m : ℝ}
    (hm7 : 7 / 16 ≤ m) (hmh : m < 1 / 2) :
    0 ≤ doubleCapHighResidual m := by
  have hm : 0 < m := by linarith
  let h : ℝ := (1 + H (2 * m - 1 / 2)) / 2
  have hh : 0 < h := by
    have hx0 : 0 < 2 * m - 1 / 2 := by linarith
    have hx1 : 2 * m - 1 / 2 < 1 := by linarith
    have hH := H_pos hx0 hx1
    dsimp [h]
    linarith
  have hhCap : h < H m := by
    dsimp [h]
    exact doubleCapHighFloor_lt_entropyCap (by linarith) hmh
  have hh1 : h < 1 := hhCap.trans_le (H_le_one m)
  have hSlope := doubleCapHighSlopeResidual_nonneg_on_seven_tail hm7 hmh
  have hFormula := four_add_deriv_phi_eq_slopeFormula hm hmh hh hh1
  have hResidualEq : 4 + deriv (phi m) h = doubleCapHighSlopeResidual m := by
    simpa only [doubleCapHighSlopeResidual, h] using hFormula
  have hDeriv : -4 ≤ deriv (phi m) h := by
    linarith [hResidualEq, hSlope]
  unfold doubleCapHighResidual
  exact doubleCapEndpointResidual_nonneg_of_slope hm hmh hh hhCap hDeriv

theorem doubleCapHighCapEndpoint_on_seven_tail {m : ℝ}
    (hm7 : 7 / 16 ≤ m) (hmh : m < 1 / 2) :
    phi m (capEntropyFloor m) ≤
      4 * (H m - capEntropyFloor m) := by
  have hm : 0 < m := by linarith
  have hh : 0 < (1 + H (2 * m - 1 / 2)) / 2 := by
    have hx0 : 0 < 2 * m - 1 / 2 := by linarith
    have hx1 : 2 * m - 1 / 2 < 1 := by linarith
    linarith [H_pos hx0 hx1]
  have hh1 : (1 + H (2 * m - 1 / 2)) / 2 ≤ 1 := by
    linarith [H_le_one (2 * m - 1 / 2)]
  have hFloor : capEntropyFloor m =
      (1 + H (2 * m - 1 / 2)) / 2 := by
    unfold capEntropyFloor
    simp only [if_neg (by linarith : ¬ m ≤ (1 / 4 : ℝ))]
  rw [hFloor]
  exact (doubleCap_endpoint_iff_residual_nonneg hm hmh hh hh1).2
    (doubleCapHighResidual_nonneg_on_seven_tail hm7 hmh)

#print axioms doubleCapHighResidual_nonneg_on_seven_tail
#print axioms doubleCapHighCapEndpoint_on_seven_tail

end GeneralCK

end


