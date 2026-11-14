-- Prove2me | Definitions.Def_row23_rh_supp_RH65008BandZeros
-- name    : row23_rh_supp_RH65008BandZeros
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:19:21.639296+00:00
-- url     : https://prove2.me/theorems/d9206d3b-2b71-4814-b660-9c5c988726f3
-- title:
--   Row 23 RH support: RH65008BandZeros
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_sample_batch_0002_20261114
import Theorems.Thm_RS5_bandZeros_of_ok
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH65008NewBand
open RH65000NewBand
def samples : List RS5.Sample := [sample65000q16, sample65000q17, sample65000q18, sample65000q19, sample65000q20, sample65000q21, sample65000q22, sample65000q23, sample65000q24, sample65000q25, sample65000q26, sample65000q27, sample65000q28, sample65000q29, sample65000q30, sample65000q31, sample65000q32]

theorem band_checked : RS5.bandOK samples = true := by
  simp only [samples, RS5.bandOK, RS5.bandAux,
    sample65000q16_checked,
    sample65000q17_checked,
    sample65000q18_checked,
    sample65000q19_checked,
    sample65000q20_checked,
    sample65000q21_checked,
    sample65000q22_checked,
    sample65000q23_checked,
    sample65000q24_checked,
    sample65000q25_checked,
    sample65000q26_checked,
    sample65000q27_checked,
    sample65000q28_checked,
    sample65000q29_checked,
    sample65000q30_checked,
    sample65000q31_checked,
    sample65000q32_checked,
    Bool.true_and, Bool.and_true]
  decide

theorem sign_changes : RS5.chgBy RS5.Sample.pos samples = 6 := by
  decide

theorem six_line_zeros : RS5.BandZeros (65004 : ℝ) (65008 : ℝ) 6 := by
  have h := RS5.bandZeros_of_ok sample65000q16 [sample65000q17, sample65000q18, sample65000q19, sample65000q20, sample65000q21, sample65000q22, sample65000q23, sample65000q24, sample65000q25, sample65000q26, sample65000q27, sample65000q28, sample65000q29, sample65000q30, sample65000q31, sample65000q32]
    (by simpa only [samples] using band_checked)
  have hlo : RS5.Sample.t sample65000q16 = (65004 : ℝ) := by
    norm_num [RS5.Sample.t, sample65000q16]
  have hhi : RS5.Sample.t (RS5.lastOf sample65000q16 [sample65000q17, sample65000q18, sample65000q19, sample65000q20, sample65000q21, sample65000q22, sample65000q23, sample65000q24, sample65000q25, sample65000q26, sample65000q27, sample65000q28, sample65000q29, sample65000q30, sample65000q31, sample65000q32]) = (65008 : ℝ) := by
    norm_num [RS5.Sample.t, RS5.lastOf, sample65000q32]
  change RS5.BandZeros (RS5.Sample.t sample65000q16)
    (RS5.Sample.t (RS5.lastOf sample65000q16 [sample65000q17, sample65000q18, sample65000q19, sample65000q20, sample65000q21, sample65000q22, sample65000q23, sample65000q24, sample65000q25, sample65000q26, sample65000q27, sample65000q28, sample65000q29, sample65000q30, sample65000q31, sample65000q32]))
    (RS5.chgBy RS5.Sample.pos samples) at h
  rw [hlo, hhi, sign_changes] at h
  exact h
end RH65008NewBand
#print axioms RH65008NewBand.band_checked
#print axioms RH65008NewBand.sign_changes
#print axioms RH65008NewBand.six_line_zeros


