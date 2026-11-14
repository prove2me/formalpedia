-- Prove2me | Definitions.Def_row23_translation_serial_10_20261114
-- name    : row23_translation_serial_10_20261114
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T23:19:54.829207+00:00
-- url     : https://prove2.me/theorems/c30f4a78-de22-4f9d-982b-19cc1ab4f817
-- title:
--   Serial low-height translation certificates 10
-- statement:
--   A finite group of kernel-checked translation certificates for the low-height zeta-zero verification. The serial dependency orders compilation of the certified groups; it adds no mathematical assumption.
-- source:
--   Finite interval-arithmetic certificate used in the row-23 Dusart Table 1 proof reduction, P. Dusart, Ramanujan J. 45 (2018), pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_translation_serial_09_20261114
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


