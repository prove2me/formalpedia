-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100TranslationBatch08
-- name    : row23_rh_supp_RHLow100TranslationBatch08
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:52:32.905842+00:00
-- url     : https://prove2.me/theorems/65e286a9-6156-4622-bad5-d2855e899241
-- title:
--   Row 23 RH support: RHLow100TranslationBatch08
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
theorem row64 : CertifiedLiteralTranslation.checkRecord ⟨64, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨64, by decide⟩) = true := by
  decide +kernel
theorem row65 : CertifiedLiteralTranslation.checkRecord ⟨65, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨65, by decide⟩) = true := by
  decide +kernel
theorem row66 : CertifiedLiteralTranslation.checkRecord ⟨66, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨66, by decide⟩) = true := by
  decide +kernel
theorem row67 : CertifiedLiteralTranslation.checkRecord ⟨67, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨67, by decide⟩) = true := by
  decide +kernel
theorem row68 : CertifiedLiteralTranslation.checkRecord ⟨68, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨68, by decide⟩) = true := by
  decide +kernel
theorem row69 : CertifiedLiteralTranslation.checkRecord ⟨69, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨69, by decide⟩) = true := by
  decide +kernel
theorem row70 : CertifiedLiteralTranslation.checkRecord ⟨70, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨70, by decide⟩) = true := by
  decide +kernel
theorem row71 : CertifiedLiteralTranslation.checkRecord ⟨71, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨71, by decide⟩) = true := by
  decide +kernel
end RHLow100Translation
#print axioms RHLow100Translation.row64
#print axioms RHLow100Translation.row65
#print axioms RHLow100Translation.row66
#print axioms RHLow100Translation.row67
#print axioms RHLow100Translation.row68
#print axioms RHLow100Translation.row69
#print axioms RHLow100Translation.row70
#print axioms RHLow100Translation.row71


