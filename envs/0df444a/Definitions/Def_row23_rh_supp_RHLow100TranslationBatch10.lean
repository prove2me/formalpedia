-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100TranslationBatch10
-- name    : row23_rh_supp_RHLow100TranslationBatch10
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:52:36.339477+00:00
-- url     : https://prove2.me/theorems/9b2259f0-0bba-4f2f-b677-e081b1f53c59
-- title:
--   Row 23 RH support: RHLow100TranslationBatch10
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_TaoFivePrimes_RH14To100TranslationInterface
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace RHLow100Translation
theorem row80 : CertifiedLiteralTranslation.checkRecord ⟨80, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨80, by decide⟩) = true := by
  decide +kernel
theorem row81 : CertifiedLiteralTranslation.checkRecord ⟨81, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨81, by decide⟩) = true := by
  decide +kernel
theorem row82 : CertifiedLiteralTranslation.checkRecord ⟨82, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨82, by decide⟩) = true := by
  decide +kernel
theorem row83 : CertifiedLiteralTranslation.checkRecord ⟨83, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨83, by decide⟩) = true := by
  decide +kernel
theorem row84 : CertifiedLiteralTranslation.checkRecord ⟨84, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨84, by decide⟩) = true := by
  decide +kernel
theorem row85 : CertifiedLiteralTranslation.checkRecord ⟨85, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨85, by decide⟩) = true := by
  decide +kernel
end RHLow100Translation
#print axioms RHLow100Translation.row80
#print axioms RHLow100Translation.row81
#print axioms RHLow100Translation.row82
#print axioms RHLow100Translation.row83
#print axioms RHLow100Translation.row84
#print axioms RHLow100Translation.row85


