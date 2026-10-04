-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginMixedKClosure
-- name    : CK_GeneralCK_Certificates_E8OriginMixedKClosure
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T13:42:32.410696+00:00
-- url     : https://prove2.me/theorems/80cea379-ab84-40e2-8db7-d9b5cae3d8ce
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginMixedKClosure` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8OriginMixedKClosure` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8OriginMixedKClosure` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginMixedKClosure (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginMixedKClosure.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginMixedKTransfer
import Definitions.Def_CK_GeneralCK_Certificates_E8OriginMixedCertificateFromK

-- ===== source module GeneralCK.Certificates.E8OriginMixedKClosure =====
section

namespace GeneralCK.Certificates.E8OriginMixedKClosure

open E8OriginAnalyticCertificate
open E8OriginPositiveConsumer
open E8OriginMixedDerivativeConsumer
open E8OriginQRealRegularity
open E8OriginRemainder
open E8OriginSourceKExactAssembly
open E8OriginSourceKResidualLower
open E8OriginMixedKTransfer

theorem sourceK_eq_sourceKFormula (s t : ℝ) :
    sourceK s t = sourceKFormula s t := by
  rfl

/-- The exact source polynomial transfers to the analytic mixed derivative
after charging both the order-17 Taylor tail and the finite coefficient-box
error. -/
theorem sourceK_sub_total_error_le_deltaSST
    (cert : QuantitativeCertificate) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hR : s + t ≤ (2 / 25 : ℝ)) :
    sourceK s t -
        ((remainderOverRadiusCubed : ℝ) + coefficientCubicErrorFactor) *
          (s + t) ^ 3 ≤ deltaSST (qReal cert) s t := by
  have htail := mixedKFormula_sub_taylor_le_remainder cert hs ht
    (by simpa [radius] using hR)
  have hcoeff := weighted_taylor_sub_sourceKFormula_le_coefficient cert hs ht
    (by simpa [radius] using hR)
  rw [deltaSST_eq_mixedKFormula_qReal_on_origin cert hs ht hR]
  rw [← sourceK_eq_sourceKFormula] at hcoeff
  rw [abs_le] at htail hcoeff
  linarith

/-- The checked coefficient error is absorbed by the source polynomial's
reserved cubic slack, closing strict positivity on the full origin simplex. -/
theorem deltaSST_qReal_pos_on_origin
    (cert : QuantitativeCertificate) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 < t) (hR : s + t ≤ (2 / 25 : ℝ)) :
    0 < deltaSST (qReal cert) s t := by
  have htransfer := sourceK_sub_total_error_le_deltaSST cert hs ht.le hR
  have hsource := sourceK_lower hs ht.le hR
  have htail :
      (remainderOverRadiusCubed : ℝ) < ((13 / 1000000 : ℚ) : ℝ) :=
    Rat.cast_lt.mpr remainderOverRadiusCubed_lt
  norm_num at htail
  have hcoeff := coefficientCubicErrorFactor_lt
  have hsum : 0 < s + t := by linarith
  have hcube : 0 < (s + t) ^ 3 := pow_pos hsum 3
  nlinarith

/-- Final premise-free E8 origin certificate. -/
theorem mixedDerivativeCertificate_from_sourceK
    (cert : QuantitativeCertificate) :
    MixedDerivativeCertificate (qReal cert) (2 / 25 : ℝ) := by
  apply mixedDerivativeCertificate_of_mixed_pos cert
  intro s t hs ht hR
  exact deltaSST_qReal_pos_on_origin cert hs ht hR

#print axioms sourceK_sub_total_error_le_deltaSST
#print axioms deltaSST_qReal_pos_on_origin
#print axioms mixedDerivativeCertificate_from_sourceK

end GeneralCK.Certificates.E8OriginMixedKClosure

end


