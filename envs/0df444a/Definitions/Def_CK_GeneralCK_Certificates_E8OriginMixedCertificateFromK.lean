-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginMixedCertificateFromK
-- name    : CK_GeneralCK_Certificates_E8OriginMixedCertificateFromK
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T18:31:38.624984+00:00
-- url     : https://prove2.me/theorems/7bf2eec8-8d20-4a4f-a0ae-952e5a77530f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginMixedCertificateFromK` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8OriginMixedCertificateFromK` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8OriginMixedCertificateFromK` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginMixedCertificateFromK (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginMixedCertificateFromK.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKResidualLower

-- ===== source module GeneralCK.Certificates.E8OriginMixedCertificateFromK =====
section

namespace GeneralCK.Certificates.E8OriginMixedCertificateFromK

open E8OriginAnalyticCertificate
open E8OriginPositiveConsumer
open E8OriginMixedDerivativeConsumer
open E8OriginQRealRegularity
open E8OriginRemainder
open E8OriginSourceKExactAssembly
open E8OriginSourceKResidualLower

/-- The exact remaining functional transfer after the 208-coefficient
polynomial replay and retained remainder arithmetic have been discharged. -/
def MixedKTransfer (cert : QuantitativeCertificate) : Prop :=
  ∀ s t : Real, 0 ≤ s → 0 < t → s + t ≤ (2 / 25 : Real) →
    sourceK s t - (remainderOverRadiusCubed : Real) * (s + t) ^ 3 ≤
      deltaSST (qReal cert) s t

theorem mixedDerivativeCertificate_of_K_transfer
    (cert : QuantitativeCertificate) (htransfer : MixedKTransfer cert) :
    MixedDerivativeCertificate (qReal cert) (2 / 25 : Real) := by
  apply mixedDerivativeCertificate_of_mixed_pos cert
  intro s t hs ht hR
  exact (sourceK_sub_remainder_pos hs ht hR).trans_le
    (htransfer s t hs ht hR)

end GeneralCK.Certificates.E8OriginMixedCertificateFromK

end


