-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8ElementaryCoeff7
-- name    : CK_GeneralCK_Certificates_E8ElementaryCoeff7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:33:13.572986+00:00
-- url     : https://prove2.me/theorems/cb692033-532d-4aab-b434-e0be0b583f19
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8ElementaryCoeff7` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8ElementaryCoeff7` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8ElementaryCoeff7` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8ElementaryCoeff7 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8ElementaryCoeff7.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8NormalizedCoeff7

-- ===== source module GeneralCK.Certificates.E8ElementaryCoeff7 =====
section

/-! Exact elementary Taylor coefficients at orders six and seven. -/

namespace GeneralCK.Certificates.E8ElementaryCoeff7

open E8AnalyticGerm Reflection.ComplexEntropy
open E8AnalyticInverseRecurrence E8NormalizedCoeff5 E8NormalizedCoeff7
open E8ElementaryCoeff5

private theorem one_mem_slit : (1 : ℂ) ∈ Complex.slitPlane := by
  simpa using (Complex.mem_slitPlane_of_norm_lt_one (z := (0 : ℂ)) (by norm_num))

private theorem analytic_log_add :
    AnalyticAt ℂ (fun z : ℂ => Complex.log (1 + z)) 0 := by
  exact (analyticAt_const.add analyticAt_id).clog (by simpa using one_mem_slit)

private theorem analytic_log_sub :
    AnalyticAt ℂ (fun z : ℂ => Complex.log (1 - z)) 0 := by
  exact (analyticAt_const.sub analyticAt_id).clog (by simpa using one_mem_slit)

private theorem coeff_sq (n : ℕ) :
    coeff (fun z : ℂ => z ^ 2) n = if n = 2 then 1 else 0 := by
  rw [coeff, iteratedDeriv_fun_pow_zero]
  split <;> simp_all

theorem coeff_atanhExt_seven : coeff atanhExt 7 = 1 / 7 := by
  have h := coeff_atanhExt 6
  norm_num at h ⊢
  exact h

private theorem coeff_log_one_sub_sq_six :
    coeff (fun z : ℂ => Complex.log (1 - z ^ 2)) 6 = -1 / 3 := by
  have h := coeff_comp (fun z : ℂ => Complex.log (1 - z))
    (fun z : ℂ => z ^ 2) analytic_log_sub (analyticAt_id.pow 2) (by simp) 6
  change coeff (((fun z : ℂ => Complex.log (1 - z)) ∘ fun z : ℂ => z ^ 2)) 6 = -1 / 3
  rw [h]
  simp [composeCoeff, powCoeff, Finset.sum_range_succ, coeff_sq,
    coeff_clog_one_sub]
  norm_num

theorem coeff_biasBExt_six : coeff biasBExt 6 = 1 / 6 := by
  rw [show biasBExt = fun z : ℂ => (Real.log 2 : ℂ) -
      (fun w : ℂ => Complex.log (1 - w ^ 2)) z / 2 by rfl,
    coeff_const_sub _ _ 6 (by norm_num), coeff_div_const,
    coeff_log_one_sub_sq_six]
  ring

private theorem coeff_one_add (n : ℕ) :
    coeff (fun z : ℂ => 1 + z) n =
      if n = 0 then 1 else if n = 1 then 1 else 0 := by
  rcases n with (_ | _ | n) <;>
    simp [coeff, iteratedDeriv_succ', iteratedDeriv_const]

private theorem coeff_one_sub (n : ℕ) :
    coeff (fun z : ℂ => 1 - z) n =
      if n = 0 then 1 else if n = 1 then -1 else 0 := by
  rcases n with (_ | _ | n) <;>
    simp [coeff, iteratedDeriv_succ', iteratedDeriv_const]

theorem coeff_entropyExt_six : coeff entropyExt 6 = -1 / 30 := by
  let lp : ℂ → ℂ := fun z => Complex.log (1 + z)
  let lm : ℂ → ℂ := fun z => Complex.log (1 - z)
  have hp := coeff_mul_six (fun z : ℂ => 1 + z) lp
    (analyticAt_const.add analyticAt_id) analytic_log_add
  have hm := coeff_mul_six (fun z : ℂ => 1 - z) lm
    (analyticAt_const.sub analyticAt_id) analytic_log_sub
  change coeff (fun z : ℂ => (1 + z) * lp z) 6 = _ at hp
  change coeff (fun z : ℂ => (1 - z) * lm z) 6 = _ at hm
  have hs := coeff_add (fun z : ℂ => (1 + z) * lp z)
    (fun z : ℂ => (1 - z) * lm z)
    ((analyticAt_const.add analyticAt_id).mul analytic_log_add)
    ((analyticAt_const.sub analyticAt_id).mul analytic_log_sub) 6
  rw [show entropyExt = fun z : ℂ => (Real.log 2 : ℂ) -
      (((fun w : ℂ => (1 + w) * lp w) z +
        (fun w : ℂ => (1 - w) * lm w) z) / 2) by funext z; rfl,
    coeff_const_sub _ _ 6 (by norm_num), coeff_div_const]
  change -(coeff (((fun z : ℂ => (1 + z) * lp z) +
      (fun z : ℂ => (1 - z) * lm z))) 6 / 2) = -1 / 30
  rw [hs, hp, hm]
  simp [lp, lm, coeff_one_add, coeff_one_sub, coeff_clog_one_add,
    coeff_clog_one_sub]
  norm_num

end GeneralCK.Certificates.E8ElementaryCoeff7

end


