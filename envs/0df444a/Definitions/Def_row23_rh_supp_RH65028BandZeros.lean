-- Prove2me | Definitions.Def_row23_rh_supp_RH65028BandZeros
-- name    : row23_rh_supp_RH65028BandZeros
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:18:57.593721+00:00
-- url     : https://prove2.me/theorems/2842e82a-e185-4d5e-8654-246400c9b4be
-- title:
--   Row 23 RH support: RH65028BandZeros
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_sample_batch_0003_20261114
import Definitions.Def_row23_rh_sample_batch_0004_20261114
import Definitions.Def_row23_rh_sample_batch_0032_20261114
import Definitions.Def_row23_rh_sample_batch_0005_20261114
import Theorems.Thm_RS5_bandZeros_of_ok
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH65028NewBand
open RH65000NewBand
def samples : List RS5.Sample := [sample65000q48, sample65000q49, sample65000q50, sample65000q51, sample65000q52, sample65000q53, sample65000q54, sample65000q55, sample65000q56, sample65000q57, sample65000q58, sample65000q59, sample65000q60, sample65000q61, sample65000q62, sample65000q63, sample65000q64, sample65000q65, sample65000q66, sample65000q67, sample65000q68, sample65000q69, sample65000q70, sample65000q71, sample65000q72, sample65000q73, sample65000q74, sample65000q75, sample65000q76, sample65000q77, sample65000q78, sample65000q79, sample65000q80, sample65000q81, sample65000q82, sample65000q83, sample65000q84, sample65000q85, sample65000q86, sample65000q87, sample65000q88, sample65000q89, sample65000q90, sample65000q91, sample65000q92, sample65000q990, sample65000q93, sample65000q94, sample65000q95, sample65000q96, sample65000q97, sample65000q98, sample65000q99, sample65000q100, sample65000q101, sample65000q102, sample65000q103, sample65000q104, sample65000q105, sample65000q106, sample65000q107, sample65000q108, sample65000q109, sample65000q110, sample65000q111, sample65000q112]
theorem band_checked : RS5.bandOK samples = true := by
  simp only [samples, RS5.bandOK, RS5.bandAux,
    sample65000q48_checked,
    sample65000q49_checked,
    sample65000q50_checked,
    sample65000q51_checked,
    sample65000q52_checked,
    sample65000q53_checked,
    sample65000q54_checked,
    sample65000q55_checked,
    sample65000q56_checked,
    sample65000q57_checked,
    sample65000q58_checked,
    sample65000q59_checked,
    sample65000q60_checked,
    sample65000q61_checked,
    sample65000q62_checked,
    sample65000q63_checked,
    sample65000q64_checked,
    sample65000q65_checked,
    sample65000q66_checked,
    sample65000q67_checked,
    sample65000q68_checked,
    sample65000q69_checked,
    sample65000q70_checked,
    sample65000q71_checked,
    sample65000q72_checked,
    sample65000q73_checked,
    sample65000q74_checked,
    sample65000q75_checked,
    sample65000q76_checked,
    sample65000q77_checked,
    sample65000q78_checked,
    sample65000q79_checked,
    sample65000q80_checked,
    sample65000q81_checked,
    sample65000q82_checked,
    sample65000q83_checked,
    sample65000q84_checked,
    sample65000q85_checked,
    sample65000q86_checked,
    sample65000q87_checked,
    sample65000q88_checked,
    sample65000q89_checked,
    sample65000q90_checked,
    sample65000q91_checked,
    sample65000q92_checked,
    sample65000q990_checked,
    sample65000q93_checked,
    sample65000q94_checked,
    sample65000q95_checked,
    sample65000q96_checked,
    sample65000q97_checked,
    sample65000q98_checked,
    sample65000q99_checked,
    sample65000q100_checked,
    sample65000q101_checked,
    sample65000q102_checked,
    sample65000q103_checked,
    sample65000q104_checked,
    sample65000q105_checked,
    sample65000q106_checked,
    sample65000q107_checked,
    sample65000q108_checked,
    sample65000q109_checked,
    sample65000q110_checked,
    sample65000q111_checked,
    sample65000q112_checked,
    Bool.true_and, Bool.and_true]
  decide
theorem sign_changes : RS5.chgBy RS5.Sample.pos samples = 24 := by
  decide
theorem line_zeros : RS5.BandZeros (65012 : ℝ) (65028 : ℝ) 24 := by
  have h := RS5.bandZeros_of_ok sample65000q48 [sample65000q49, sample65000q50, sample65000q51, sample65000q52, sample65000q53, sample65000q54, sample65000q55, sample65000q56, sample65000q57, sample65000q58, sample65000q59, sample65000q60, sample65000q61, sample65000q62, sample65000q63, sample65000q64, sample65000q65, sample65000q66, sample65000q67, sample65000q68, sample65000q69, sample65000q70, sample65000q71, sample65000q72, sample65000q73, sample65000q74, sample65000q75, sample65000q76, sample65000q77, sample65000q78, sample65000q79, sample65000q80, sample65000q81, sample65000q82, sample65000q83, sample65000q84, sample65000q85, sample65000q86, sample65000q87, sample65000q88, sample65000q89, sample65000q90, sample65000q91, sample65000q92, sample65000q990, sample65000q93, sample65000q94, sample65000q95, sample65000q96, sample65000q97, sample65000q98, sample65000q99, sample65000q100, sample65000q101, sample65000q102, sample65000q103, sample65000q104, sample65000q105, sample65000q106, sample65000q107, sample65000q108, sample65000q109, sample65000q110, sample65000q111, sample65000q112]
    (by simpa only [samples] using band_checked)
  have hlo : RS5.Sample.t sample65000q48 = (65012 : ℝ) := by
    norm_num [RS5.Sample.t, sample65000q48]
  have hhi : RS5.Sample.t (RS5.lastOf sample65000q48 [sample65000q49, sample65000q50, sample65000q51, sample65000q52, sample65000q53, sample65000q54, sample65000q55, sample65000q56, sample65000q57, sample65000q58, sample65000q59, sample65000q60, sample65000q61, sample65000q62, sample65000q63, sample65000q64, sample65000q65, sample65000q66, sample65000q67, sample65000q68, sample65000q69, sample65000q70, sample65000q71, sample65000q72, sample65000q73, sample65000q74, sample65000q75, sample65000q76, sample65000q77, sample65000q78, sample65000q79, sample65000q80, sample65000q81, sample65000q82, sample65000q83, sample65000q84, sample65000q85, sample65000q86, sample65000q87, sample65000q88, sample65000q89, sample65000q90, sample65000q91, sample65000q92, sample65000q990, sample65000q93, sample65000q94, sample65000q95, sample65000q96, sample65000q97, sample65000q98, sample65000q99, sample65000q100, sample65000q101, sample65000q102, sample65000q103, sample65000q104, sample65000q105, sample65000q106, sample65000q107, sample65000q108, sample65000q109, sample65000q110, sample65000q111, sample65000q112]) = (65028 : ℝ) := by
    norm_num [RS5.Sample.t, RS5.lastOf, sample65000q112]
  change RS5.BandZeros (RS5.Sample.t sample65000q48)
    (RS5.Sample.t (RS5.lastOf sample65000q48 [sample65000q49, sample65000q50, sample65000q51, sample65000q52, sample65000q53, sample65000q54, sample65000q55, sample65000q56, sample65000q57, sample65000q58, sample65000q59, sample65000q60, sample65000q61, sample65000q62, sample65000q63, sample65000q64, sample65000q65, sample65000q66, sample65000q67, sample65000q68, sample65000q69, sample65000q70, sample65000q71, sample65000q72, sample65000q73, sample65000q74, sample65000q75, sample65000q76, sample65000q77, sample65000q78, sample65000q79, sample65000q80, sample65000q81, sample65000q82, sample65000q83, sample65000q84, sample65000q85, sample65000q86, sample65000q87, sample65000q88, sample65000q89, sample65000q90, sample65000q91, sample65000q92, sample65000q990, sample65000q93, sample65000q94, sample65000q95, sample65000q96, sample65000q97, sample65000q98, sample65000q99, sample65000q100, sample65000q101, sample65000q102, sample65000q103, sample65000q104, sample65000q105, sample65000q106, sample65000q107, sample65000q108, sample65000q109, sample65000q110, sample65000q111, sample65000q112]))
    (RS5.chgBy RS5.Sample.pos samples) at h
  rw [hlo, hhi, sign_changes] at h
  exact h
end RH65028NewBand
#print axioms RH65028NewBand.band_checked
#print axioms RH65028NewBand.sign_changes
#print axioms RH65028NewBand.line_zeros


