-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8ElementaryCoeff13_part01
-- name    : CK_GeneralCK_Certificates_E8ElementaryCoeff13_part01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T15:48:16.635271+00:00
-- url     : https://prove2.me/theorems/16facb49-2bbe-41c6-ab76-733a7cb6af79
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8ElementaryCoeff13 (part 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8ElementaryCoeff13 (part 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8ElementaryCoeff13 (part 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8ElementaryCoeff13 (part 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8ElementaryCoeff13 (part 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ElementaryCoeff13_part01_q01

namespace GeneralCK.Certificates.E8ElementaryCoeff13
open E8AnalyticGerm Reflection.ComplexEntropy E8AnalyticInverseRecurrence
open E8NormalizedCoeff5 E8NormalizedCoeff7 E8ElementaryCoeff5
private theorem one_mem_slit : (1 : ℂ) ∈ Complex.slitPlane := by
  simpa using (Complex.mem_slitPlane_of_norm_lt_one (z := (0 : ℂ)) (by norm_num))

private theorem analytic_log_add :
    AnalyticAt ℂ (fun z : ℂ => Complex.log (1 + z)) 0 := by
  exact (analyticAt_const.add analyticAt_id).clog (by simpa using one_mem_slit)

private theorem analytic_log_sub :
    AnalyticAt ℂ (fun z : ℂ => Complex.log (1 - z)) 0 := by
  exact (analyticAt_const.sub analyticAt_id).clog (by simpa using one_mem_slit)

/-- Same statement as the source's `coeff_log_one_sub_sq_twelve`. The source proves it by expanding
the composed series with `simp` (about 190 s); here `log (1 - z^2) = log (1 - z) + log (1 + z)` near
`0` reduces it to the two coefficient formulas `coeff_clog_one_sub` and `coeff_clog_one_add`. -/
theorem coeff_log_one_sub_sq_twelve_priv :
    coeff (fun z : ℂ => Complex.log (1 - z ^ 2)) 12 = -1 / 6 := by
  have harg : ∀ w : ℂ, 0 < w.re → w.arg ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    intro w hw
    have h := (Complex.abs_arg_lt_pi_div_two_iff).2 (Or.inl hw)
    exact ⟨by linarith [(abs_lt.1 h).1], (abs_lt.1 h).2⟩
  have hev : (fun z : ℂ => Complex.log (1 - z ^ 2)) =ᶠ[nhds 0]
      ((fun z : ℂ => Complex.log (1 - z)) + (fun z : ℂ => Complex.log (1 + z))) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with z hz
    have hz' : ‖z‖ < 1 / 2 := by simpa using hz
    have hre : |z.re| < 1 / 2 := lt_of_le_of_lt (Complex.abs_re_le_norm z) hz'
    have h1 : 0 < (1 - z).re := by simp; linarith [(abs_lt.1 hre).2]
    have h2 : 0 < (1 + z).re := by simp; linarith [(abs_lt.1 hre).1]
    have hne1 : (1 - z) ≠ 0 := fun h => by simp [h] at h1
    have hne2 : (1 + z) ≠ 0 := fun h => by simp [h] at h2
    have a1 := harg _ h1; have a2 := harg _ h2
    simp only [Pi.add_apply]
    rw [show (1 : ℂ) - z ^ 2 = (1 - z) * (1 + z) by ring]
    exact Complex.log_mul hne1 hne2 ⟨by linarith [a1.1, a2.1], by linarith [a1.2, a2.2]⟩
  rw [coeff_congr hev, coeff_add _ _ analytic_log_sub analytic_log_add]
  have a := coeff_clog_one_sub 11
  have b := coeff_clog_one_add 11
  norm_num at a b
  rw [a, b]; norm_num

end GeneralCK.Certificates.E8ElementaryCoeff13


