-- Prove2me | Definitions.Def_row23_rh_supp_RH65044BandZeros
-- name    : row23_rh_supp_RH65044BandZeros
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:19:00.560973+00:00
-- url     : https://prove2.me/theorems/510ccc81-8c57-469b-8003-a4aa6c61512c
-- title:
--   Row 23 RH support: RH65044BandZeros
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_sample_batch_0005_20261114
import Definitions.Def_row23_rh_sample_batch_0006_20261114
import Definitions.Def_row23_rh_sample_batch_0007_20261114
import Theorems.Thm_RS5_bandZeros_of_ok
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace RH65044NewBand
open RH65000NewBand
def samples : List RS5.Sample := [sample65000q112, sample65000q113, sample65000q114, sample65000q115, sample65000q116, sample65000q117, sample65000q118, sample65000q119, sample65000q120, sample65000q121, sample65000q122, sample65000q123, sample65000q124, sample65000q125, sample65000q126, sample65000q127, sample65000q128, sample65000q129, sample65000q130, sample65000q131, sample65000q132, sample65000q133, sample65000q134, sample65000q135, sample65000q136, sample65000q137, sample65000q138, sample65000q139, sample65000q140, sample65000q141, sample65000q142, sample65000q143, sample65000q144, sample65000q145, sample65000q146, sample65000q147, sample65000q148, sample65000q149, sample65000q150, sample65000q151, sample65000q152, sample65000q153, sample65000q154, sample65000q155, sample65000q156, sample65000q157, sample65000q158, sample65000q159, sample65000q160, sample65000q161, sample65000q162, sample65000q163, sample65000q164, sample65000q165, sample65000q166, sample65000q167, sample65000q168, sample65000q169, sample65000q170, sample65000q171, sample65000q172, sample65000q173, sample65000q174, sample65000q175, sample65000q176]
theorem band_checked : RS5.bandOK samples = true := by
  simp only [samples, RS5.bandOK, RS5.bandAux,
    sample65000q112_checked,
    sample65000q113_checked,
    sample65000q114_checked,
    sample65000q115_checked,
    sample65000q116_checked,
    sample65000q117_checked,
    sample65000q118_checked,
    sample65000q119_checked,
    sample65000q120_checked,
    sample65000q121_checked,
    sample65000q122_checked,
    sample65000q123_checked,
    sample65000q124_checked,
    sample65000q125_checked,
    sample65000q126_checked,
    sample65000q127_checked,
    sample65000q128_checked,
    sample65000q129_checked,
    sample65000q130_checked,
    sample65000q131_checked,
    sample65000q132_checked,
    sample65000q133_checked,
    sample65000q134_checked,
    sample65000q135_checked,
    sample65000q136_checked,
    sample65000q137_checked,
    sample65000q138_checked,
    sample65000q139_checked,
    sample65000q140_checked,
    sample65000q141_checked,
    sample65000q142_checked,
    sample65000q143_checked,
    sample65000q144_checked,
    sample65000q145_checked,
    sample65000q146_checked,
    sample65000q147_checked,
    sample65000q148_checked,
    sample65000q149_checked,
    sample65000q150_checked,
    sample65000q151_checked,
    sample65000q152_checked,
    sample65000q153_checked,
    sample65000q154_checked,
    sample65000q155_checked,
    sample65000q156_checked,
    sample65000q157_checked,
    sample65000q158_checked,
    sample65000q159_checked,
    sample65000q160_checked,
    sample65000q161_checked,
    sample65000q162_checked,
    sample65000q163_checked,
    sample65000q164_checked,
    sample65000q165_checked,
    sample65000q166_checked,
    sample65000q167_checked,
    sample65000q168_checked,
    sample65000q169_checked,
    sample65000q170_checked,
    sample65000q171_checked,
    sample65000q172_checked,
    sample65000q173_checked,
    sample65000q174_checked,
    sample65000q175_checked,
    sample65000q176_checked,
    Bool.true_and, Bool.and_true]
  decide
theorem sign_changes : RS5.chgBy RS5.Sample.pos samples = 23 := by
  decide
theorem line_zeros : RS5.BandZeros (65028 : ℝ) (65044 : ℝ) 23 := by
  have h := RS5.bandZeros_of_ok sample65000q112 [sample65000q113, sample65000q114, sample65000q115, sample65000q116, sample65000q117, sample65000q118, sample65000q119, sample65000q120, sample65000q121, sample65000q122, sample65000q123, sample65000q124, sample65000q125, sample65000q126, sample65000q127, sample65000q128, sample65000q129, sample65000q130, sample65000q131, sample65000q132, sample65000q133, sample65000q134, sample65000q135, sample65000q136, sample65000q137, sample65000q138, sample65000q139, sample65000q140, sample65000q141, sample65000q142, sample65000q143, sample65000q144, sample65000q145, sample65000q146, sample65000q147, sample65000q148, sample65000q149, sample65000q150, sample65000q151, sample65000q152, sample65000q153, sample65000q154, sample65000q155, sample65000q156, sample65000q157, sample65000q158, sample65000q159, sample65000q160, sample65000q161, sample65000q162, sample65000q163, sample65000q164, sample65000q165, sample65000q166, sample65000q167, sample65000q168, sample65000q169, sample65000q170, sample65000q171, sample65000q172, sample65000q173, sample65000q174, sample65000q175, sample65000q176]
    (by simpa only [samples] using band_checked)
  have hlo : RS5.Sample.t sample65000q112 = (65028 : ℝ) := by
    norm_num [RS5.Sample.t, sample65000q112]
  have hhi : RS5.Sample.t (RS5.lastOf sample65000q112 [sample65000q113, sample65000q114, sample65000q115, sample65000q116, sample65000q117, sample65000q118, sample65000q119, sample65000q120, sample65000q121, sample65000q122, sample65000q123, sample65000q124, sample65000q125, sample65000q126, sample65000q127, sample65000q128, sample65000q129, sample65000q130, sample65000q131, sample65000q132, sample65000q133, sample65000q134, sample65000q135, sample65000q136, sample65000q137, sample65000q138, sample65000q139, sample65000q140, sample65000q141, sample65000q142, sample65000q143, sample65000q144, sample65000q145, sample65000q146, sample65000q147, sample65000q148, sample65000q149, sample65000q150, sample65000q151, sample65000q152, sample65000q153, sample65000q154, sample65000q155, sample65000q156, sample65000q157, sample65000q158, sample65000q159, sample65000q160, sample65000q161, sample65000q162, sample65000q163, sample65000q164, sample65000q165, sample65000q166, sample65000q167, sample65000q168, sample65000q169, sample65000q170, sample65000q171, sample65000q172, sample65000q173, sample65000q174, sample65000q175, sample65000q176]) = (65044 : ℝ) := by
    norm_num [RS5.Sample.t, RS5.lastOf, sample65000q176]
  change RS5.BandZeros (RS5.Sample.t sample65000q112)
    (RS5.Sample.t (RS5.lastOf sample65000q112 [sample65000q113, sample65000q114, sample65000q115, sample65000q116, sample65000q117, sample65000q118, sample65000q119, sample65000q120, sample65000q121, sample65000q122, sample65000q123, sample65000q124, sample65000q125, sample65000q126, sample65000q127, sample65000q128, sample65000q129, sample65000q130, sample65000q131, sample65000q132, sample65000q133, sample65000q134, sample65000q135, sample65000q136, sample65000q137, sample65000q138, sample65000q139, sample65000q140, sample65000q141, sample65000q142, sample65000q143, sample65000q144, sample65000q145, sample65000q146, sample65000q147, sample65000q148, sample65000q149, sample65000q150, sample65000q151, sample65000q152, sample65000q153, sample65000q154, sample65000q155, sample65000q156, sample65000q157, sample65000q158, sample65000q159, sample65000q160, sample65000q161, sample65000q162, sample65000q163, sample65000q164, sample65000q165, sample65000q166, sample65000q167, sample65000q168, sample65000q169, sample65000q170, sample65000q171, sample65000q172, sample65000q173, sample65000q174, sample65000q175, sample65000q176]))
    (RS5.chgBy RS5.Sample.pos samples) at h
  rw [hlo, hhi, sign_changes] at h
  exact h
end RH65044NewBand
#print axioms RH65044NewBand.band_checked
#print axioms RH65044NewBand.sign_changes
#print axioms RH65044NewBand.line_zeros


