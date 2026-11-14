-- Prove2me | Definitions.Def_row23_rh_supp_RHLow100ThetaReplacement
-- name    : row23_rh_supp_RHLow100ThetaReplacement
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:54:28.148554+00:00
-- url     : https://prove2.me/theorems/a47dec0a-92ed-4a7c-9da0-6c36e146372f
-- title:
--   Row 23 RH support: RHLow100ThetaReplacement
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLow100ThetaAll
set_option autoImplicit false

theorem TaoFivePrimes.rh14to100_theta_checks (i : Fin 16) (n : Fin 8)
    (ha : CertifiedThetaPoints.active i n) :
    CertifiedJetRecords.checkRecord i n (CertifiedJetRecords.recordAt i n) = true :=
  RHLow100Theta.all_records i n ha

#print axioms TaoFivePrimes.rh14to100_theta_checks


