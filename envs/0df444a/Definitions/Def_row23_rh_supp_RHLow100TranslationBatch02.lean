-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100TranslationBatch02
-- name    : row23_rh_supp_RHLow100TranslationBatch02
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:52:05.062866+00:00
-- url     : https://prove2.me/theorems/d9f45d3e-9e92-48cd-922c-283ee46ebb39
-- title:
--   Row 23 RH support: RHLow100TranslationBatch02
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
theorem row16 : CertifiedLiteralTranslation.checkRecord ⟨16, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨16, by decide⟩) = true := by
  decide +kernel
theorem row17 : CertifiedLiteralTranslation.checkRecord ⟨17, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨17, by decide⟩) = true := by
  decide +kernel
theorem row18 : CertifiedLiteralTranslation.checkRecord ⟨18, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨18, by decide⟩) = true := by
  decide +kernel
theorem row19 : CertifiedLiteralTranslation.checkRecord ⟨19, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨19, by decide⟩) = true := by
  decide +kernel
theorem row20 : CertifiedLiteralTranslation.checkRecord ⟨20, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨20, by decide⟩) = true := by
  decide +kernel
theorem row21 : CertifiedLiteralTranslation.checkRecord ⟨21, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨21, by decide⟩) = true := by
  decide +kernel
theorem row22 : CertifiedLiteralTranslation.checkRecord ⟨22, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨22, by decide⟩) = true := by
  decide +kernel
theorem row23 : CertifiedLiteralTranslation.checkRecord ⟨23, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨23, by decide⟩) = true := by
  decide +kernel
end RHLow100Translation
#print axioms RHLow100Translation.row16
#print axioms RHLow100Translation.row17
#print axioms RHLow100Translation.row18
#print axioms RHLow100Translation.row19
#print axioms RHLow100Translation.row20
#print axioms RHLow100Translation.row21
#print axioms RHLow100Translation.row22
#print axioms RHLow100Translation.row23


