-- Prove2me | Definitions.Def_row23_rh_supp_RH65012BandZeros
-- name    : row23_rh_supp_RH65012BandZeros
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:18:40.399882+00:00
-- url     : https://prove2.me/theorems/4fb2da07-45b8-463a-a28b-ffdac3d8601e
-- title:
--   Row 23 RH support: RH65012BandZeros
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_sample_batch_0002_20261114
import Definitions.Def_row23_rh_sample_batch_0003_20261114
import Theorems.Thm_RS5_bandZeros_of_ok
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH65012NewBand
open RH65000NewBand
def samples : List RS5.Sample := [sample65000q32, sample65000q33, sample65000q34, sample65000q35, sample65000q36, sample65000q37, sample65000q38, sample65000q39, sample65000q40, sample65000q41, sample65000q42, sample65000q43, sample65000q44, sample65000q45, sample65000q46, sample65000q47, sample65000q48]
theorem band_checked : RS5.bandOK samples = true := by
  simp only [samples, RS5.bandOK, RS5.bandAux,
    sample65000q32_checked,
    sample65000q33_checked,
    sample65000q34_checked,
    sample65000q35_checked,
    sample65000q36_checked,
    sample65000q37_checked,
    sample65000q38_checked,
    sample65000q39_checked,
    sample65000q40_checked,
    sample65000q41_checked,
    sample65000q42_checked,
    sample65000q43_checked,
    sample65000q44_checked,
    sample65000q45_checked,
    sample65000q46_checked,
    sample65000q47_checked,
    sample65000q48_checked,
    Bool.true_and, Bool.and_true]
  decide
theorem sign_changes : RS5.chgBy RS5.Sample.pos samples = 6 := by
  decide
theorem line_zeros : RS5.BandZeros (65008 : ℝ) (65012 : ℝ) 6 := by
  have h := RS5.bandZeros_of_ok sample65000q32 [sample65000q33, sample65000q34, sample65000q35, sample65000q36, sample65000q37, sample65000q38, sample65000q39, sample65000q40, sample65000q41, sample65000q42, sample65000q43, sample65000q44, sample65000q45, sample65000q46, sample65000q47, sample65000q48]
    (by simpa only [samples] using band_checked)
  have hlo : RS5.Sample.t sample65000q32 = (65008 : ℝ) := by
    norm_num [RS5.Sample.t, sample65000q32]
  have hhi : RS5.Sample.t (RS5.lastOf sample65000q32 [sample65000q33, sample65000q34, sample65000q35, sample65000q36, sample65000q37, sample65000q38, sample65000q39, sample65000q40, sample65000q41, sample65000q42, sample65000q43, sample65000q44, sample65000q45, sample65000q46, sample65000q47, sample65000q48]) = (65012 : ℝ) := by
    norm_num [RS5.Sample.t, RS5.lastOf, sample65000q48]
  change RS5.BandZeros (RS5.Sample.t sample65000q32)
    (RS5.Sample.t (RS5.lastOf sample65000q32 [sample65000q33, sample65000q34, sample65000q35, sample65000q36, sample65000q37, sample65000q38, sample65000q39, sample65000q40, sample65000q41, sample65000q42, sample65000q43, sample65000q44, sample65000q45, sample65000q46, sample65000q47, sample65000q48]))
    (RS5.chgBy RS5.Sample.pos samples) at h
  rw [hlo, hhi, sign_changes] at h
  exact h
end RH65012NewBand
#print axioms RH65012NewBand.band_checked
#print axioms RH65012NewBand.sign_changes
#print axioms RH65012NewBand.line_zeros


