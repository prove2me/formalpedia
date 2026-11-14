-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100TranslationBatch01
-- name    : row23_rh_supp_RHLow100TranslationBatch01
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:52:00.237435+00:00
-- url     : https://prove2.me/theorems/e932aff0-8d8d-49c1-a9f6-ead4f40708a3
-- title:
--   Row 23 RH support: RHLow100TranslationBatch01
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
theorem row08 : CertifiedLiteralTranslation.checkRecord ⟨8, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨8, by decide⟩) = true := by
  decide +kernel
theorem row09 : CertifiedLiteralTranslation.checkRecord ⟨9, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨9, by decide⟩) = true := by
  decide +kernel
theorem row10 : CertifiedLiteralTranslation.checkRecord ⟨10, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨10, by decide⟩) = true := by
  decide +kernel
theorem row11 : CertifiedLiteralTranslation.checkRecord ⟨11, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨11, by decide⟩) = true := by
  decide +kernel
theorem row12 : CertifiedLiteralTranslation.checkRecord ⟨12, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨12, by decide⟩) = true := by
  decide +kernel
theorem row13 : CertifiedLiteralTranslation.checkRecord ⟨13, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨13, by decide⟩) = true := by
  decide +kernel
theorem row14 : CertifiedLiteralTranslation.checkRecord ⟨14, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨14, by decide⟩) = true := by
  decide +kernel
theorem row15 : CertifiedLiteralTranslation.checkRecord ⟨15, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨15, by decide⟩) = true := by
  decide +kernel
end RHLow100Translation
#print axioms RHLow100Translation.row08
#print axioms RHLow100Translation.row09
#print axioms RHLow100Translation.row10
#print axioms RHLow100Translation.row11
#print axioms RHLow100Translation.row12
#print axioms RHLow100Translation.row13
#print axioms RHLow100Translation.row14
#print axioms RHLow100Translation.row15


