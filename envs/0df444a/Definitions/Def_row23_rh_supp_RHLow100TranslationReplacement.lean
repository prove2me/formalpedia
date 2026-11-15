-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100TranslationReplacement
-- name    : row23_rh_supp_RHLow100TranslationReplacement
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T19:41:20.144053+00:00
-- url     : https://prove2.me/theorems/0c96d798-4e62-4b51-9d34-55163db21bd0
-- title:
--   Row 23 RH support: RHLow100TranslationReplacement
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLow100TranslationAll
set_option autoImplicit false

theorem TaoFivePrimes.rh14to100_translation_checks (i : Fin 86) :
    CertifiedLiteralTranslation.checkRecord i (CertifiedLiteralTranslation.recordAt i) = true :=
  RHLow100Translation.all_rows i

#print axioms TaoFivePrimes.rh14to100_translation_checks


