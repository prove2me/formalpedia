-- Prove2me | Definitions.Def_row23_translation_serial_08_20261114
-- name    : row23_translation_serial_08_20261114
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T23:14:17.987201+00:00
-- url     : https://prove2.me/theorems/18e363d5-5718-4886-bb57-c1d700504639
-- title:
--   Serial low-height translation certificates 08
-- statement:
--   A finite group of kernel-checked translation certificates for the low-height zeta-zero verification. The serial dependency orders compilation of the certified groups; it adds no mathematical assumption.
-- source:
--   Finite interval-arithmetic certificate used in the row-23 Dusart Table 1 proof reduction, P. Dusart, Ramanujan J. 45 (2018), pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_translation_serial_07_20261114
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


