-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailActualSign
-- name    : CK_GeneralCK_PureGapDoubleCapLowTailActualSign
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T13:03:42.305344+00:00
-- url     : https://prove2.me/theorems/1278e7c5-d08a-43c8-ae5f-c31fd2b95ed8
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapLowTailActualSign` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapLowTailActualSign` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapLowTailActualSign` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapLowTailActualSign (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapLowTailActualSign.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailActualSecant
import Definitions.Def_CK_GeneralCK_PureGapDoubleCapOuterSlopeChecker

-- ===== source module GeneralCK.PureGapDoubleCapLowTailActualSign =====
section

/-! Unconditional sign of the canonical low-cap slope and endpoint residual
in the near-zero interval. -/

namespace GeneralCK

open Reflection Certificates.Reflection

theorem doubleCapLowTail_actual_bias_slope_nonneg {m : ℝ}
    (hm : 0 < m) (hm100 : m ≤ 1 / 100) :
    0 ≤ doubleCapSlopeBiasExpression
      (doubleCapLowTailY m) (doubleCapLowTailC m) := by
  have hmq : m ≤ 1 / 4 := by linarith
  have hBetween := doubleCapLowTailC_between hm hmq
  have hk : 49 / 50 ≤ 1 - 2 * m := by linarith [hm100]
  have hc : 0 < doubleCapLowTailC m := by linarith [hk, hBetween.1]
  have hcy : doubleCapLowTailC m ≤ doubleCapLowTailY m := hBetween.2.le
  have hyHigh : 49 / 50 ≤ doubleCapLowTailY m := by
    linarith [hk, hBetween.1, hBetween.2]
  have hh : 0 < H (2 * m) / 2 :=
    div_pos (H_pos (by linarith) (by linarith)) two_pos
  have hh1 : H (2 * m) / 2 < 1 :=
    (doubleCapLowFloor_lt_entropyCap hm hmq).trans_le (H_le_one m)
  have hy1 : doubleCapLowTailY m < 1 := by
    dsimp [doubleCapLowTailY]
    linarith [entropyInverse_pos hh hh1.le]
  have hLoss := doubleCapLowTail_actual_secant_le_four_thirds hm hm100
  have hDiag := doubleCapLowTail_diagonal_slope_ge_four_thirds hyHigh hy1
  exact doubleCapSlopeBiasExpression_nonneg_of_secant_loss
    hc hcy hy1 (hLoss.trans hDiag)

theorem doubleCapLowSlopeResidual_nonneg_near_zero {m : ℝ}
    (hm : 0 < m) (hm100 : m ≤ 1 / 100) :
    0 ≤ doubleCapLowSlopeResidual m := by
  have hmq : m ≤ 1 / 4 := by linarith
  have hmh : m < 1 / 2 := by linarith
  let h : ℝ := H (2 * m) / 2
  have hh : 0 < h := by
    dsimp [h]
    exact div_pos (H_pos (by linarith) (by linarith)) two_pos
  have hh1 : h < 1 := by
    dsimp [h]
    exact (doubleCapLowFloor_lt_entropyCap hm hmq).trans_le (H_le_one m)
  have hBias0 := four_add_deriv_phi_eq_slopeBias hm hmh hh hh1
  dsimp only at hBias0
  have hBias : 4 + deriv (phi m) h =
      doubleCapSlopeBiasExpression
        (doubleCapLowTailY m) (doubleCapLowTailC m) := by
    change 4 + deriv (phi m) h =
      doubleCapSlopeBiasExpression
        (1 - 2 * entropyInverse h)
        (regularContact (((1 - 2 * m) / h) / Real.log 2)) at hBias0
    have hyEq : 1 - 2 * entropyInverse h = doubleCapLowTailY m := rfl
    have hcEq : regularContact (((1 - 2 * m) / h) / Real.log 2) =
        doubleCapLowTailC m := by
      simpa only [h] using (doubleCapLowTailC_physical hm hmq).symm
    rw [hyEq, hcEq] at hBias0
    exact hBias0
  have hFormula0 := four_add_deriv_phi_eq_slopeFormula hm hmh hh hh1
  have hFormula : 4 + deriv (phi m) h = doubleCapLowSlopeResidual m := by
    simpa only [doubleCapLowSlopeResidual, h] using hFormula0
  linarith only [hBias, hFormula,
    doubleCapLowTail_actual_bias_slope_nonneg hm hm100]

theorem doubleCapLowResidual_nonneg_near_zero {m : ℝ}
    (hm : 0 < m) (hm100 : m ≤ 1 / 100) :
    0 ≤ doubleCapLowResidual m := by
  have hmq : m ≤ 1 / 4 := by linarith
  have hmh : m < 1 / 2 := by linarith
  let h : ℝ := H (2 * m) / 2
  have hh : 0 < h := by
    dsimp [h]
    exact div_pos (H_pos (by linarith) (by linarith)) two_pos
  have hhCap : h < H m := by
    dsimp [h]
    exact doubleCapLowFloor_lt_entropyCap hm hmq
  have hh1 : h < 1 := hhCap.trans_le (H_le_one m)
  have hFormula0 := four_add_deriv_phi_eq_slopeFormula hm hmh hh hh1
  have hFormula : 4 + deriv (phi m) h = doubleCapLowSlopeResidual m := by
    simpa only [doubleCapLowSlopeResidual, h] using hFormula0
  have hDeriv : -4 ≤ deriv (phi m) h := by
    linarith only [hFormula, doubleCapLowSlopeResidual_nonneg_near_zero hm hm100]
  unfold doubleCapLowResidual
  exact doubleCapEndpointResidual_nonneg_of_slope hm hmh hh hhCap hDeriv

#print axioms doubleCapLowTail_actual_bias_slope_nonneg
#print axioms doubleCapLowSlopeResidual_nonneg_near_zero
#print axioms doubleCapLowResidual_nonneg_near_zero

end GeneralCK

end


