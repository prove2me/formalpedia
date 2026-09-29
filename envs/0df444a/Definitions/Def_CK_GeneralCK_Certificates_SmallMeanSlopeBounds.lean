-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_SmallMeanSlopeBounds
-- name    : CK_GeneralCK_Certificates_SmallMeanSlopeBounds
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:29:35.655862+00:00
-- url     : https://prove2.me/theorems/73a6d1c7-15df-4ba3-9089-ac3f9d4c16b4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.SmallMeanSlopeBounds` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.SmallMeanSlopeBounds` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.SmallMeanSlopeBounds` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.SmallMeanSlopeBounds (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/SmallMeanSlopeBounds.lean)

import Definitions.Def_CK_GeneralCK_Certificates_SmallMeanBounds
import Definitions.Def_CK_GeneralCK_ProfileLowerBounds

namespace GeneralCK.Certificates.SmallMean

theorem inverse_bracket {t l u : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hl : 0 ≤ l) (hl' : l ≤ 1/2) (hu : 0 ≤ u) (hu' : u ≤ 1/2)
    (hlo : H l ≤ t) (hhi : t ≤ H u) :
    l ≤ entropyInverse t ∧ entropyInverse t ≤ u := by
  constructor
  · have hm := entropyInverse_mono (H_nonneg hl (by linarith)) ht' hlo
    simpa only [entropyInverse_H_lower hl hl'] using hm
  · have hm := entropyInverse_mono ht (H_le_one u) hhi
    simpa only [entropyInverse_H_lower hu hu'] using hm

theorem slope_upper {t l u j : ℝ} (ht : 0 < t) (ht' : t < 1)
    (hl : 0 < l) (hu : u < 1/2) (hvl : l ≤ entropyInverse (1-t))
    (hvu : entropyInverse (1-t) ≤ u) (hj : j ≤ Real.log ((1-u)/u)) (hj0 : 0 < j) :
    deriv Scalar.P t ≤ 2+(1-2*l)/(l*(1-u)*j) := by
  let v := entropyInverse (1-t)
  have hv : 0 < v := hl.trans_le hvl
  have hv' : v < 1/2 := hvu.trans_lt hu
  have hu0 : 0 < u := hv.trans_le hvu
  have hlo : j ≤ Real.log ((1-v)/v) := by
    apply hj.trans
    apply Real.log_le_log (div_pos (by linarith) hu0)
    apply (div_le_div_iff₀ hu0 hv).2
    linarith
  have hlog : 0 < Real.log ((1-v)/v) := hj0.trans_le hlo
  have huc : 0 < 1-u := by linarith
  have hvc : 0 < 1-v := by linarith
  have hden : 0 < l*(1-u)*j := by positivity
  have hden' : 0 < v*(1-v)*Real.log ((1-v)/v) := by positivity
  have hd : l*(1-u)*j ≤ v*(1-v)*Real.log ((1-v)/v) := by
    exact mul_le_mul (mul_le_mul hvl (by linarith) huc.le hv.le) hlo hj0.le
      (mul_nonneg hv.le hvc.le)
  have hc : 0 ≤ (1-2*l)/(l*(1-u)*j) := by
    apply div_nonneg _ hden.le
    linarith
  have hr : (1-2*v)/(v*(1-v)*Real.log ((1-v)/v)) ≤ (1-2*l)/(l*(1-u)*j) := by
    apply (div_le_iff₀ hden').mpr
    calc
      1-2*v ≤ 1-2*l := by linarith
      _ = ((1-2*l)/(l*(1-u)*j))*(l*(1-u)*j) := (div_mul_cancel₀ _ hden.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hd hc
  rw [Scalar.deriv_P ht ht']
  change 2+(1-2*v)/(Real.log 2*v*(1-v)*J v) ≤ _
  have he : Real.log 2*v*(1-v)*J v = v*(1-v)*Real.log ((1-v)/v) := by
    unfold J
    field_simp [log_two_pos.ne']
  rw [he]
  linarith only [hr]

end GeneralCK.Certificates.SmallMean


