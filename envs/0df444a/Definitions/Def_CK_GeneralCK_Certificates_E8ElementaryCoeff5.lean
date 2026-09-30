-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8ElementaryCoeff5
-- name    : CK_GeneralCK_Certificates_E8ElementaryCoeff5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:20:53.992787+00:00
-- url     : https://prove2.me/theorems/b04e4c6a-eebf-425f-a4df-88678a1a8f35
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8ElementaryCoeff5` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8ElementaryCoeff5` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8ElementaryCoeff5` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8ElementaryCoeff5 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8ElementaryCoeff5.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8NormalizedCoeff5

-- ===== source module GeneralCK.Certificates.E8ElementaryCoeff5 =====
section

/-! Exact elementary Taylor coefficients entering the E8 parametrization. -/

namespace GeneralCK.Certificates.E8ElementaryCoeff5

open E8AnalyticGerm Reflection.ComplexEntropy
open E8NormalizedCoeff5
open E8AnalyticInverseRecurrence

private theorem one_mem_slit : (1 : ℂ) ∈ Complex.slitPlane := by
  simpa using (Complex.mem_slitPlane_of_norm_lt_one (z := (0 : ℂ)) (by norm_num))

theorem coeff_clog_one_add (n : ℕ) :
    coeff (fun z : ℂ => Complex.log (1 + z)) (n + 1) = (-1 : ℂ) ^ n / (n + 1) := by
  have hs := congrFun (iteratedDeriv_comp_const_add (n + 1) Complex.log 1) 0
  simp only [add_zero] at hs
  rw [iteratedDeriv_succ_log one_mem_slit] at hs
  rw [coeff, hs]
  norm_num [Nat.factorial_succ]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hn]

theorem coeff_clog_one_sub (n : ℕ) :
    coeff (fun z : ℂ => Complex.log (1 - z)) (n + 1) = -1 / (n + 1) := by
  have hs := congrFun (iteratedDeriv_comp_const_sub (n + 1) Complex.log 1) 0
  simp only [sub_zero] at hs
  rw [iteratedDeriv_succ_log one_mem_slit] at hs
  simp only [smul_eq_mul] at hs
  rw [coeff, hs]
  norm_num [Nat.factorial_succ]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hn]
  rw [← pow_add, show n + 1 + n = 2 * n + 1 by omega, pow_add, pow_mul]
  norm_num

private theorem analytic_log_add :
    AnalyticAt ℂ (fun z : ℂ => Complex.log (1 + z)) 0 := by
  exact (analyticAt_const.add analyticAt_id).clog (by simpa using one_mem_slit)

private theorem analytic_log_sub :
    AnalyticAt ℂ (fun z : ℂ => Complex.log (1 - z)) 0 := by
  exact (analyticAt_const.sub analyticAt_id).clog (by simpa using one_mem_slit)

theorem coeff_atanhExt (n : ℕ) :
    coeff atanhExt (n + 1) = (((-1 : ℂ) ^ n) + 1) / (2 * (n + 1)) := by
  rw [show atanhExt = fun z : ℂ =>
      ((fun w : ℂ => Complex.log (1 + w)) z -
        (fun w : ℂ => Complex.log (1 - w)) z) / 2 by rfl,
    coeff_div_const,
    show (fun z : ℂ => Complex.log (1 + z) - Complex.log (1 - z)) =
      (fun z : ℂ => Complex.log (1 + z)) -
        (fun z : ℂ => Complex.log (1 - z)) by rfl,
    coeff_sub _ _ analytic_log_add analytic_log_sub,
    coeff_clog_one_add, coeff_clog_one_sub]
  field_simp
  ring

theorem coeff_atanhExt_one : coeff atanhExt 1 = 1 := by
  simpa using coeff_atanhExt 0

theorem coeff_atanhExt_three : coeff atanhExt 3 = 1 / 3 := by
  have h := coeff_atanhExt 2
  norm_num at h ⊢
  exact h

theorem coeff_atanhExt_five : coeff atanhExt 5 = 1 / 5 := by
  have h := coeff_atanhExt 4
  norm_num at h ⊢
  exact h

private theorem coeff_sq (n : ℕ) : coeff (fun z : ℂ => z ^ 2) n = if n = 2 then 1 else 0 := by
  rw [coeff, iteratedDeriv_fun_pow_zero]
  split <;> simp_all

private theorem coeff_log_one_sub_sq_two :
    coeff (fun z : ℂ => Complex.log (1 - z ^ 2)) 2 = -1 := by
  have h := coeff_comp (fun z : ℂ => Complex.log (1 - z)) (fun z : ℂ => z ^ 2)
    analytic_log_sub (analyticAt_id.pow 2) (by simp) 2
  change coeff (((fun z : ℂ => Complex.log (1 - z)) ∘ fun z : ℂ => z ^ 2)) 2 = -1
  rw [h]
  simp [composeCoeff, powCoeff, Finset.sum_range_succ, coeff_sq,
    coeff_clog_one_sub]

private theorem coeff_log_one_sub_sq_four :
    coeff (fun z : ℂ => Complex.log (1 - z ^ 2)) 4 = -1 / 2 := by
  have h := coeff_comp (fun z : ℂ => Complex.log (1 - z)) (fun z : ℂ => z ^ 2)
    analytic_log_sub (analyticAt_id.pow 2) (by simp) 4
  change coeff (((fun z : ℂ => Complex.log (1 - z)) ∘ fun z : ℂ => z ^ 2)) 4 = -1 / 2
  rw [h]
  simp [composeCoeff, powCoeff, Finset.sum_range_succ, coeff_sq,
    coeff_clog_one_sub]
  norm_num

theorem coeff_biasBExt_two : coeff biasBExt 2 = 1 / 2 := by
  rw [show biasBExt = fun z : ℂ => (Real.log 2 : ℂ) -
      (fun w : ℂ => Complex.log (1 - w ^ 2)) z / 2 by rfl,
    coeff_const_sub _ _ 2 (by norm_num), coeff_div_const,
    coeff_log_one_sub_sq_two]
  ring

theorem coeff_biasBExt_four : coeff biasBExt 4 = 1 / 4 := by
  rw [show biasBExt = fun z : ℂ => (Real.log 2 : ℂ) -
      (fun w : ℂ => Complex.log (1 - w ^ 2)) z / 2 by rfl,
    coeff_const_sub _ _ 4 (by norm_num), coeff_div_const,
    coeff_log_one_sub_sq_four]
  ring

private theorem coeff_one_add (n : ℕ) :
    coeff (fun z : ℂ => 1 + z) n = if n = 0 then 1 else if n = 1 then 1 else 0 := by
  rcases n with (_ | _ | n) <;>
    simp [coeff, iteratedDeriv_succ', iteratedDeriv_const]

private theorem coeff_one_sub (n : ℕ) :
    coeff (fun z : ℂ => 1 - z) n = if n = 0 then 1 else if n = 1 then -1 else 0 := by
  rcases n with (_ | _ | n) <;>
    simp [coeff, iteratedDeriv_succ', iteratedDeriv_const]

theorem coeff_entropyExt_zero : coeff entropyExt 0 = (Real.log 2 : ℂ) := by
  simp [coeff, entropyExt, iteratedDeriv_zero]

theorem coeff_entropyExt_two : coeff entropyExt 2 = -1 / 2 := by
  let lp : ℂ → ℂ := fun z => Complex.log (1 + z)
  let lm : ℂ → ℂ := fun z => Complex.log (1 - z)
  have hp := coeff_mul_two (fun z : ℂ => 1 + z) lp
    (analyticAt_const.add analyticAt_id) analytic_log_add
  have hm := coeff_mul_two (fun z : ℂ => 1 - z) lm
    (analyticAt_const.sub analyticAt_id) analytic_log_sub
  change coeff (fun z : ℂ => (1 + z) * lp z) 2 = _ at hp
  change coeff (fun z : ℂ => (1 - z) * lm z) 2 = _ at hm
  have hs := coeff_add ((fun z : ℂ => (1 + z) * lp z))
    (fun z : ℂ => (1 - z) * lm z)
    ((analyticAt_const.add analyticAt_id).mul analytic_log_add)
    ((analyticAt_const.sub analyticAt_id).mul analytic_log_sub) 2
  rw [show entropyExt = fun z : ℂ => (Real.log 2 : ℂ) -
      (((fun w : ℂ => (1 + w) * lp w) z + (fun w : ℂ => (1 - w) * lm w) z) / 2) by
        funext z; rfl,
    coeff_const_sub _ _ 2 (by norm_num), coeff_div_const]
  change -(coeff (((fun z : ℂ => (1 + z) * lp z) +
      (fun z : ℂ => (1 - z) * lm z))) 2 / 2) = -1 / 2
  rw [hs, hp, hm]
  simp [lp, lm, coeff_one_add, coeff_one_sub, coeff_clog_one_add,
    coeff_clog_one_sub]
  norm_num

theorem coeff_entropyExt_four : coeff entropyExt 4 = -1 / 12 := by
  let lp : ℂ → ℂ := fun z => Complex.log (1 + z)
  let lm : ℂ → ℂ := fun z => Complex.log (1 - z)
  have hp := coeff_mul_four (fun z : ℂ => 1 + z) lp
    (analyticAt_const.add analyticAt_id) analytic_log_add
  have hm := coeff_mul_four (fun z : ℂ => 1 - z) lm
    (analyticAt_const.sub analyticAt_id) analytic_log_sub
  change coeff (fun z : ℂ => (1 + z) * lp z) 4 = _ at hp
  change coeff (fun z : ℂ => (1 - z) * lm z) 4 = _ at hm
  have hs := coeff_add ((fun z : ℂ => (1 + z) * lp z))
    (fun z : ℂ => (1 - z) * lm z)
    ((analyticAt_const.add analyticAt_id).mul analytic_log_add)
    ((analyticAt_const.sub analyticAt_id).mul analytic_log_sub) 4
  rw [show entropyExt = fun z : ℂ => (Real.log 2 : ℂ) -
      (((fun w : ℂ => (1 + w) * lp w) z + (fun w : ℂ => (1 - w) * lm w) z) / 2) by
        funext z; rfl,
    coeff_const_sub _ _ 4 (by norm_num), coeff_div_const]
  change -(coeff (((fun z : ℂ => (1 + z) * lp z) +
      (fun z : ℂ => (1 - z) * lm z))) 4 / 2) = -1 / 12
  rw [hs, hp, hm]
  simp [lp, lm, coeff_one_add, coeff_one_sub, coeff_clog_one_add,
    coeff_clog_one_sub]
  norm_num

end GeneralCK.Certificates.E8ElementaryCoeff5

end


