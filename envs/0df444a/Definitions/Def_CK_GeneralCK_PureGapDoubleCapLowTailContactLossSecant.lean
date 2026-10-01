-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailContactLossSecant
-- name    : CK_GeneralCK_PureGapDoubleCapLowTailContactLossSecant
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T11:21:03.757257+00:00
-- url     : https://prove2.me/theorems/a5ea25e2-a18c-497a-995d-71b54f59ffbe
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapLowTailContactLossSecant` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapLowTailContactLossSecant` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapLowTailContactLossSecant` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapLowTailContactLossSecant (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapLowTailContactLossSecant.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailContactLossBridge
import Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailRatioIncrement

-- ===== source module GeneralCK.PureGapDoubleCapLowTailContactLossSecant =====
section

/-! An exact secant estimate for the true-contact loss. It uses the
monotonicity of the logarithmic contact bias instead of a derivative upper
bound, and remains meaningful as both contacts approach one. -/

namespace GeneralCK

open Reflection Certificates.Reflection

theorem doubleCapContactGain_secant_upper {c y : ℝ}
    (hc : 0 < c) (hcy : c ≤ y) (hy1 : y < 1) :
    doubleCapContactGain y - doubleCapContactGain c ≤
      (y ^ 2 - c ^ 2) /
        ((1 - y ^ 2) * (1 - c ^ 2) * biasB y) := by
  have hc1 : c < 1 := hcy.trans_lt hy1
  have hy : 0 < y := hc.trans_le hcy
  have hDy : 0 < 1 - y ^ 2 := by nlinarith
  have hDc : 0 < 1 - c ^ 2 := by nlinarith
  have hBc : 0 < biasB c := biasB_pos hc hc1
  have hBy : 0 < biasB y := biasB_pos hy hy1
  have hB : biasB c ≤ biasB y :=
    biasB_strictMonoOn_positive.monotoneOn
      ⟨hc, hc1⟩ ⟨hy, hy1⟩ hcy
  have hDenOrder : (1 - c ^ 2) * biasB c ≤
      (1 - c ^ 2) * biasB y :=
    mul_le_mul_of_nonneg_left hB hDc.le
  have hDenSmall : 0 < (1 - c ^ 2) * biasB c := mul_pos hDc hBc
  have hDenLarge : 0 < (1 - c ^ 2) * biasB y := mul_pos hDc hBy
  have hContact : c ^ 2 / ((1 - c ^ 2) * biasB y) ≤
      c ^ 2 / ((1 - c ^ 2) * biasB c) := by
    apply (div_le_div_iff₀ hDenLarge hDenSmall).mpr
    exact mul_le_mul_of_nonneg_left hDenOrder (sq_nonneg c)
  have hIdentity :
      y ^ 2 / ((1 - y ^ 2) * biasB y) -
        c ^ 2 / ((1 - c ^ 2) * biasB y) =
      (y ^ 2 - c ^ 2) /
        ((1 - y ^ 2) * (1 - c ^ 2) * biasB y) := by
    field_simp [hDy.ne', hDc.ne', hBy.ne']
    ring
  unfold doubleCapContactGain
  rw [← hIdentity]
  linarith [hContact]

theorem doubleCapSlopeBiasExpression_nonneg_of_secant_loss {c y : ℝ}
    (hc : 0 < c) (hcy : c ≤ y) (hy1 : y < 1)
    (hcheck :
      2 * ((y ^ 2 - c ^ 2) /
        ((1 - y ^ 2) * (1 - c ^ 2) * biasB y)) ≤
        doubleCapSlopeBiasExpression y y) :
    0 ≤ doubleCapSlopeBiasExpression y c := by
  have hLoss := doubleCapContactGain_secant_upper hc hcy hy1
  have hIdentity : doubleCapSlopeBiasExpression y c =
      doubleCapSlopeBiasExpression y y -
        2 * (doubleCapContactGain y - doubleCapContactGain c) := by
    unfold doubleCapSlopeBiasExpression doubleCapContactGain
    ring
  rw [hIdentity]
  linarith only [hLoss, hcheck]

#print axioms doubleCapContactGain_secant_upper
#print axioms doubleCapSlopeBiasExpression_nonneg_of_secant_loss

end GeneralCK

end


