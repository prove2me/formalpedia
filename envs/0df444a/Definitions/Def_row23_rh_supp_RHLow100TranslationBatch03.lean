-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100TranslationBatch03
-- name    : row23_rh_supp_RHLow100TranslationBatch03
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:52:11.075353+00:00
-- url     : https://prove2.me/theorems/58cde804-70b3-4766-8109-e85f7f87e5b9
-- title:
--   Row 23 RH support: RHLow100TranslationBatch03
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
theorem row24 : CertifiedLiteralTranslation.checkRecord ⟨24, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨24, by decide⟩) = true := by
  decide +kernel
theorem row25 : CertifiedLiteralTranslation.checkRecord ⟨25, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨25, by decide⟩) = true := by
  decide +kernel
theorem row26 : CertifiedLiteralTranslation.checkRecord ⟨26, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨26, by decide⟩) = true := by
  decide +kernel
theorem row27 : CertifiedLiteralTranslation.checkRecord ⟨27, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨27, by decide⟩) = true := by
  decide +kernel
theorem row28 : CertifiedLiteralTranslation.checkRecord ⟨28, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨28, by decide⟩) = true := by
  decide +kernel
theorem row29 : CertifiedLiteralTranslation.checkRecord ⟨29, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨29, by decide⟩) = true := by
  decide +kernel
theorem row30 : CertifiedLiteralTranslation.checkRecord ⟨30, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨30, by decide⟩) = true := by
  decide +kernel
theorem row31 : CertifiedLiteralTranslation.checkRecord ⟨31, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨31, by decide⟩) = true := by
  decide +kernel
end RHLow100Translation
#print axioms RHLow100Translation.row24
#print axioms RHLow100Translation.row25
#print axioms RHLow100Translation.row26
#print axioms RHLow100Translation.row27
#print axioms RHLow100Translation.row28
#print axioms RHLow100Translation.row29
#print axioms RHLow100Translation.row30
#print axioms RHLow100Translation.row31


