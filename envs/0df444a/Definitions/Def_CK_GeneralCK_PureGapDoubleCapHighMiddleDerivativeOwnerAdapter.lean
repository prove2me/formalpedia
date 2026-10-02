-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighMiddleDerivativeOwnerAdapter
-- name    : CK_GeneralCK_PureGapDoubleCapHighMiddleDerivativeOwnerAdapter
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T19:03:23.146933+00:00
-- url     : https://prove2.me/theorems/2fe2378d-a889-40c4-9d6b-fb15f26fce49
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapHighMiddleDerivativeOwnerAdapter` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapHighMiddleDerivativeOwnerAdapter` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapHighMiddleDerivativeOwnerAdapter` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapHighMiddleDerivativeOwnerAdapter (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapHighMiddleDerivativeOwnerAdapter.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapHighMiddleDerivativeAggregate

-- ===== source module GeneralCK.PureGapDoubleCapHighMiddleDerivativeOwnerAdapter =====
section

/-! Exact high-middle slope owner adapter, conditional only on future
proof-bearing 256 derivative-cell certificates. -/

namespace GeneralCK
open Certificates.Reflection

/-- On the bridge `m ∈ [2/5,7/16]`, the true slope residual follows from
the checked derivative formula, complete grid, and a future Lean replay of
all 256 positivity cells. -/
theorem doubleCapHighSlopeResidual_nonneg_on_bridge_of_256_cells
    (hCells : ∀ i : Fin 256,
      DoubleCapBridgeDerivativeCellCertificate i
        doubleCapBridgeDerivativeExpression)
    {m : ℝ} (hmLo : 2 / 5 ≤ m) (hmHi : m ≤ 7 / 16) :
    0 ≤ doubleCapHighSlopeResidual m := by
  have hm : 0 < m := by linarith
  have hmh : m < 1 / 2 := by linarith
  let x : ℝ := 1 - 2 * m
  let h : ℝ := (1 + H (2 * m - 1 / 2)) / 2
  have hx : x ∈ Set.Icc (1 / 8 : ℝ) (1 / 5 : ℝ) := by
    dsimp [x]
    constructor <;> linarith
  have hx0 : 0 < x := by linarith [hx.1]
  have hx1 : x < 1 / 2 := by linarith [hx.2]
  have hfloorEq : h = doubleCapHighTailFloor x := by
    dsimp [h, x, doubleCapHighTailFloor]
    congr 1
    ring
  have hh : 0 < h := by
    rw [hfloorEq]
    exact doubleCapHighTailFloor_pos hx0 hx1
  have hhCap : h < H m := by
    dsimp [h]
    exact doubleCapHighFloor_lt_entropyCap (by linarith) hmh
  have hh1 : h < 1 := hhCap.trans_le (H_le_one m)
  have hYeq : 1 - 2 * entropyInverse h = doubleCapHighTailY x := by
    rw [hfloorEq]
    rfl
  have hCeq : Reflection.regularContact
      (((1 - 2 * m) / h) / Real.log 2) = doubleCapHighTailC x := by
    rw [hfloorEq]
    unfold doubleCapHighTailC
    congr 1
    dsimp [x]
    field_simp [log_two_pos.ne',
      (doubleCapHighTailFloor_pos hx0 hx1).ne']
  have hBias := doubleCapBridgeSlope_nonneg_of_256_cells hCells hx
  have hSlopeBias := four_add_deriv_phi_eq_slopeBias hm hmh hh hh1
  dsimp only at hSlopeBias
  rw [hYeq, hCeq] at hSlopeBias
  have hSlopeFormula := four_add_deriv_phi_eq_slopeFormula hm hmh hh hh1
  have hResidualEq : 4 + deriv (phi m) h = doubleCapHighSlopeResidual m := by
    simpa only [doubleCapHighSlopeResidual, h] using hSlopeFormula
  dsimp only [doubleCapBridgeSlope] at hBias
  linarith

#print axioms doubleCapHighSlopeResidual_nonneg_on_bridge_of_256_cells

end GeneralCK

end


