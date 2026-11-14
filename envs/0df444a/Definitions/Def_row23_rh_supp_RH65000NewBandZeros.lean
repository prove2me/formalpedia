-- Prove2me | Definitions.Def_row23_rh_supp_RH65000NewBandZeros
-- name    : row23_rh_supp_RH65000NewBandZeros
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:19:35.776975+00:00
-- url     : https://prove2.me/theorems/0364755c-7d9e-4d29-a45f-fd87be38db27
-- title:
--   Row 23 RH support: RH65000NewBandZeros
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RH65000NewBandFullCertificate
import Theorems.Thm_RS5_bandZeros_of_ok
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH65000NewBand

/-- Six distinct critical-line zeros lie beyond the checked zero-free slab. -/
theorem six_line_zeros :
    RS5.BandZeros ((65000 : ℝ) + 25 / 8192) (65004 : ℝ) 6 := by
  have h := RS5.bandZeros_of_ok sample65000q0 [sample65000p25, sample65000q2, sample65000q3, sample65000q4, sample65000q5, sample65000q6, sample65000q7, sample65000q8, sample65000q9, sample65000q10, sample65000q11, sample65000q12, sample65000q13, sample65000q14, sample65000q15, sample65000q16]
    (by simpa only [fullSamples, samples] using full_band_checked)
  have hlo : RS5.Sample.t sample65000q0 = (65000 : ℝ) + 25 / 8192 := by
    norm_num [RS5.Sample.t, sample65000q0]
  have hhi : RS5.Sample.t (RS5.lastOf sample65000q0 [sample65000p25, sample65000q2, sample65000q3, sample65000q4, sample65000q5, sample65000q6, sample65000q7, sample65000q8, sample65000q9, sample65000q10, sample65000q11, sample65000q12, sample65000q13, sample65000q14, sample65000q15, sample65000q16]) = (65004 : ℝ) := by
    norm_num [RS5.Sample.t, RS5.lastOf, sample65000q16]
  change RS5.BandZeros (RS5.Sample.t sample65000q0)
    (RS5.Sample.t (RS5.lastOf sample65000q0 [sample65000p25, sample65000q2, sample65000q3, sample65000q4, sample65000q5, sample65000q6, sample65000q7, sample65000q8, sample65000q9, sample65000q10, sample65000q11, sample65000q12, sample65000q13, sample65000q14, sample65000q15, sample65000q16]))
    (RS5.chgBy RS5.Sample.pos fullSamples) at h
  rw [hlo, hhi, full_sign_changes] at h
  exact h

end RH65000NewBand
#print axioms RH65000NewBand.six_line_zeros


