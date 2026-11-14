-- Prove2me | Definitions.Def_row23_rh_supp_RH65000NewBandCertificate
-- name    : row23_rh_supp_RH65000NewBandCertificate
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:17:56.004205+00:00
-- url     : https://prove2.me/theorems/c26903c4-926c-46e3-a27b-4926d8d5332f
-- title:
--   Row 23 RH support: RH65000NewBandCertificate
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_sample_batch_0001_20261114
import Definitions.Def_row23_rh_sample_batch_0002_20261114
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH65000NewBand

def samples : List RS5.Sample := [sample65000p25, sample65000q2, sample65000q3, sample65000q4, sample65000q5, sample65000q6, sample65000q7, sample65000q8, sample65000q9, sample65000q10, sample65000q11, sample65000q12, sample65000q13, sample65000q14, sample65000q15, sample65000q16]

/-- All sample checks and height orderings for the new band. -/
theorem band_checked : RS5.bandOK samples = true := by
  simp only [samples, RS5.bandOK, RS5.bandAux,
    sample65000p25_checked,
    sample65000q2_checked,
    sample65000q3_checked,
    sample65000q4_checked,
    sample65000q5_checked,
    sample65000q6_checked,
    sample65000q7_checked,
    sample65000q8_checked,
    sample65000q9_checked,
    sample65000q10_checked,
    sample65000q11_checked,
    sample65000q12_checked,
    sample65000q13_checked,
    sample65000q14_checked,
    sample65000q15_checked,
    sample65000q16_checked, Bool.true_and, Bool.and_true]
  decide

/-- The sample signs give the exact number of adjacent sign changes. -/
theorem sign_changes : RS5.chgBy RS5.Sample.pos samples = 5 := by
  decide

end RH65000NewBand
#print axioms RH65000NewBand.band_checked
#print axioms RH65000NewBand.sign_changes


