-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100TranslationAll
-- name    : row23_rh_supp_RHLow100TranslationAll
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T19:40:01.57454+00:00
-- url     : https://prove2.me/theorems/d4bea2fd-da32-4808-b8a3-3da361080915
-- title:
--   Row 23 RH support: RHLow100TranslationAll
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Mathlib.Tactic.FinCases
import Definitions.Def_row23_translation_serial_10_20261114
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RHLow100Translation
theorem all_rows (i : Fin 86) : CertifiedLiteralTranslation.checkRecord i
    (CertifiedLiteralTranslation.recordAt i) = true := by
  fin_cases i
  · exact row00
  · exact row01
  · exact row02
  · exact row03
  · exact row04
  · exact row05
  · exact row06
  · exact row07
  · exact row08
  · exact row09
  · exact row10
  · exact row11
  · exact row12
  · exact row13
  · exact row14
  · exact row15
  · exact row16
  · exact row17
  · exact row18
  · exact row19
  · exact row20
  · exact row21
  · exact row22
  · exact row23
  · exact row24
  · exact row25
  · exact row26
  · exact row27
  · exact row28
  · exact row29
  · exact row30
  · exact row31
  · exact row32
  · exact row33
  · exact row34
  · exact row35
  · exact row36
  · exact row37
  · exact row38
  · exact row39
  · exact row40
  · exact row41
  · exact row42
  · exact row43
  · exact row44
  · exact row45
  · exact row46
  · exact row47
  · exact row48
  · exact row49
  · exact row50
  · exact row51
  · exact row52
  · exact row53
  · exact row54
  · exact row55
  · exact row56
  · exact row57
  · exact row58
  · exact row59
  · exact row60
  · exact row61
  · exact row62
  · exact row63
  · exact row64
  · exact row65
  · exact row66
  · exact row67
  · exact row68
  · exact row69
  · exact row70
  · exact row71
  · exact row72
  · exact row73
  · exact row74
  · exact row75
  · exact row76
  · exact row77
  · exact row78
  · exact row79
  · exact row80
  · exact row81
  · exact row82
  · exact row83
  · exact row84
  · exact row85
end RHLow100Translation
#print axioms RHLow100Translation.all_rows


