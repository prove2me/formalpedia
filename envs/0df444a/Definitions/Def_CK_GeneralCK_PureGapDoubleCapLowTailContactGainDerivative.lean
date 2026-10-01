-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailContactGainDerivative
-- name    : CK_GeneralCK_PureGapDoubleCapLowTailContactGainDerivative
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:14:34.654614+00:00
-- url     : https://prove2.me/theorems/098e0556-257a-4a26-8984-2641450d8b36
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapDoubleCapLowTailContactGainDerivative` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapDoubleCapLowTailContactGainDerivative` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapDoubleCapLowTailContactGainDerivative` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapDoubleCapLowTailContactGainDerivative (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapDoubleCapLowTailContactGainDerivative.lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapLowTailActualDiagonalMargin
import Definitions.Def_CK_GeneralCK_Certificates_MixedConstants

-- ===== source module GeneralCK.PureGapDoubleCapLowTailContactGainDerivative =====
section

/-! Exact derivative of the positive contact contribution to the
double-cap slope. It measures the loss when the contact lies below the
inverse-entropy bias. -/

namespace GeneralCK

open Reflection Certificates.Reflection

noncomputable def doubleCapContactGain (c : ℝ) : ℝ :=
  c ^ 2 / ((1 - c ^ 2) * biasB c)

theorem doubleCapContactGain_hasDerivAt {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    HasDerivAt doubleCapContactGain
      (c * (2 * biasB c - c ^ 2) /
        (((1 - c ^ 2) * biasB c) ^ 2)) c := by
  have hgap : 0 < 1 - c ^ 2 := by nlinarith
  have hB : 0 < biasB c := biasB_pos hc hc1
  have hD : (1 - c ^ 2) * biasB c ≠ 0 := (mul_pos hgap hB).ne'
  have hGap := ((hasDerivAt_id c).pow 2).const_sub 1
  have hDen := hGap.mul (hasDerivAt_biasB (by linarith) hc1)
  have hNum := (hasDerivAt_id c).pow 2
  have hRaw := hNum.div hDen hD
  convert! hRaw using 1
  dsimp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
  field_simp [hD, hgap.ne', hB.ne']
  norm_num
  ring

theorem doubleCapContactGain_deriv_pos {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    0 < deriv doubleCapContactGain c := by
  rw [(doubleCapContactGain_hasDerivAt hc hc1).deriv]
  have hgap : 0 < 1 - c ^ 2 := by nlinarith
  have hB : (69 / 100 : ℝ) < biasB c := by
    have hlog : Real.log (1 - c * c) ≤ 0 :=
      Real.log_nonpos (by nlinarith) (by nlinarith)
    unfold biasB
    linarith [Certificates.Mixed.log_two_gt_69]
  have hnum : 0 < c * (2 * biasB c - c ^ 2) := by
    apply mul_pos hc
    nlinarith [hB]
  exact div_pos hnum (sq_pos_of_pos (mul_pos hgap (by linarith [hB])))

#print axioms doubleCapContactGain_hasDerivAt
#print axioms doubleCapContactGain_deriv_pos

end GeneralCK

end


