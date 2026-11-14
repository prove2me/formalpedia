-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100TranslationBatch04
-- name    : row23_rh_supp_RHLow100TranslationBatch04
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:52:10.493765+00:00
-- url     : https://prove2.me/theorems/82d9a4d5-13b1-468f-9780-a8e34c2de848
-- title:
--   Row 23 RH support: RHLow100TranslationBatch04
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
theorem row32 : CertifiedLiteralTranslation.checkRecord ⟨32, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨32, by decide⟩) = true := by
  decide +kernel
theorem row33 : CertifiedLiteralTranslation.checkRecord ⟨33, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨33, by decide⟩) = true := by
  decide +kernel
theorem row34 : CertifiedLiteralTranslation.checkRecord ⟨34, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨34, by decide⟩) = true := by
  decide +kernel
theorem row35 : CertifiedLiteralTranslation.checkRecord ⟨35, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨35, by decide⟩) = true := by
  decide +kernel
theorem row36 : CertifiedLiteralTranslation.checkRecord ⟨36, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨36, by decide⟩) = true := by
  decide +kernel
theorem row37 : CertifiedLiteralTranslation.checkRecord ⟨37, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨37, by decide⟩) = true := by
  decide +kernel
theorem row38 : CertifiedLiteralTranslation.checkRecord ⟨38, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨38, by decide⟩) = true := by
  decide +kernel
theorem row39 : CertifiedLiteralTranslation.checkRecord ⟨39, by decide⟩
    (CertifiedLiteralTranslation.recordAt ⟨39, by decide⟩) = true := by
  decide +kernel
end RHLow100Translation
#print axioms RHLow100Translation.row32
#print axioms RHLow100Translation.row33
#print axioms RHLow100Translation.row34
#print axioms RHLow100Translation.row35
#print axioms RHLow100Translation.row36
#print axioms RHLow100Translation.row37
#print axioms RHLow100Translation.row38
#print axioms RHLow100Translation.row39


