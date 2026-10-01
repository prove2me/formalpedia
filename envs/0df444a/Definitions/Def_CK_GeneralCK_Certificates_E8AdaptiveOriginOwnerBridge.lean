-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8AdaptiveOriginOwnerBridge
-- name    : CK_GeneralCK_Certificates_E8AdaptiveOriginOwnerBridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:09:20.013289+00:00
-- url     : https://prove2.me/theorems/c17bf642-0ef4-42f2-94a1-f69ff4a1a37e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8AdaptiveOriginOwnerBridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8AdaptiveOriginOwnerBridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8AdaptiveOriginOwnerBridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8AdaptiveOriginOwnerBridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8AdaptiveOriginOwnerBridge.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8AdaptiveFamily_FullCertificate
import Definitions.Def_CK_GeneralCK_Certificates_E8OriginQRealRegularity

-- ===== source module GeneralCK.Certificates.E8AdaptiveOriginOwnerBridge =====
section

/-!
# E8 adaptive family to origin-owner bridge

The completed adaptive family supplies the quantitative inverse certificate.
The sole remaining origin input is the strict degree-15 mixed-derivative
enclosure used by the retained origin checker.
-/

namespace GeneralCK.Certificates.E8AdaptiveOriginOwnerBridge

open E8OriginAnalyticCertificate
open E8OriginMixedDerivativeConsumer
open E8OriginPositiveConsumer

noncomputable def quantitativeCertificate : QuantitativeCertificate :=
  certificateOfGlobalDerivativeBound
    Generated.E8AdaptiveFamily.FullCertificate.global_derivative_bound

/-- The completed complex-disc certificate discharges inverse existence,
analyticity, real-axis agreement, Taylor coefficients, and the order-17 tail.
Only strict positivity of the explicit mixed derivative remains. -/
theorem originOwner_of_mixed_pos
    (hpos : ∀ s t : ℝ, 0 ≤ s → 0 < t → s + t ≤ (2 / 25 : ℝ) →
      0 < deltaSST (qReal quantitativeCertificate) s t) :
    E8PositiveOn fun s t => s + t ≤ (2 / 25 : ℝ) := by
  apply e8PositiveOn_of_globalDerivativeBound_and_mixedCertificate
    Generated.E8AdaptiveFamily.FullCertificate.global_derivative_bound
  exact E8OriginQRealRegularity.mixedDerivativeCertificate_of_mixed_pos
    quantitativeCertificate hpos

#print axioms originOwner_of_mixed_pos

end GeneralCK.Certificates.E8AdaptiveOriginOwnerBridge

end


