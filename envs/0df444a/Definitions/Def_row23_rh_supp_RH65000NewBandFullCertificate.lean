-- Prove2me | Definitions.Def_row23_rh_supp_RH65000NewBandFullCertificate
-- name    : row23_rh_supp_RH65000NewBandFullCertificate
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:18:26.707227+00:00
-- url     : https://prove2.me/theorems/0ba8d7f7-d888-454e-bc66-8fe5dc9d2cff
-- title:
--   Row 23 RH support: RH65000NewBandFullCertificate
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_sample_batch_0001_20261114
import Definitions.Def_row23_rh_supp_RH65000NewBandCertificate
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH65000NewBand

def fullSamples : List RS5.Sample := sample65000q0 :: samples

/-- The extra endpoint sample and the existing band checks fit together. -/
theorem full_band_checked : RS5.bandOK fullSamples = true := by
  change (RS5.sampleOK sample65000q0 && RS5.ltH sample65000q0 sample65000p25 &&
    RS5.bandAux [sample65000q2, sample65000q3, sample65000q4, sample65000q5, sample65000q6, sample65000q7, sample65000q8, sample65000q9, sample65000q10, sample65000q11, sample65000q12, sample65000q13, sample65000q14, sample65000q15, sample65000q16] sample65000p25) = true
  have hprev : RS5.bandAux [sample65000q2, sample65000q3, sample65000q4, sample65000q5, sample65000q6, sample65000q7, sample65000q8, sample65000q9, sample65000q10, sample65000q11, sample65000q12, sample65000q13, sample65000q14, sample65000q15, sample65000q16] sample65000p25 = true := by
    simpa only [samples, RS5.bandOK] using band_checked
  simp only [Bool.and_eq_true]
  exact ⟨⟨sample65000q0_checked, by decide⟩, hprev⟩

/-- The full band has six verified adjacent sign changes. -/
theorem full_sign_changes : RS5.chgBy RS5.Sample.pos fullSamples = 6 := by
  decide

end RH65000NewBand
#print axioms RH65000NewBand.full_band_checked
#print axioms RH65000NewBand.full_sign_changes


