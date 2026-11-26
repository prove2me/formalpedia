-- Prove2me | solution 1 for Arxiv1811_00800.eq6_poisson_enhancement
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:37:41.353601+00:00
-- url     : https://prove2.me/submissions/b6f4681c-e80d-4ea0-a138-5eedcc489699

import Mathlib
import Definitions.Def_Arxiv1811_00800_Basic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Complex
open scoped Nat

open Arxiv1811_00800 in
theorem solution (beta : NNReal) (alpha : ℝ) :
    loopEnhancement (fun n => (poissonMeasure beta).real {n}) alpha =
      poissonEnhancement beta alpha := by
  set θ : ℝ := 4 * Real.pi * alpha with hθ
  set r : NNReal := beta
  have h1 : HasSum (fun n : ℕ => ((Real.exp (-(r:ℝ)) * (r:ℝ) ^ n / n ! : ℝ) : ℂ) *
      Complex.exp (((n * θ : ℝ) : ℂ) * I)) (Complex.exp (((r:ℝ):ℂ) * (Complex.exp ((θ:ℂ) * I) - 1))) := by
    have := (NormedSpace.expSeries_div_hasSum_exp (((r:ℝ):ℂ) * Complex.exp ((θ:ℂ) * I))).mul_left
      ((Real.exp (-(r:ℝ)) : ℝ) : ℂ)
    have e1 : (fun n : ℕ => ((Real.exp (-(r:ℝ)) * (r:ℝ) ^ n / n ! : ℝ) : ℂ) *
        Complex.exp (((n * θ : ℝ) : ℂ) * I)) = fun i : ℕ => ((Real.exp (-(r:ℝ)) : ℝ) : ℂ) *
        ((((r:ℝ):ℂ) * Complex.exp ((θ:ℂ) * I)) ^ i / (i ! : ℂ)) := by
      funext a
      push_cast
      rw [mul_pow, ← Complex.exp_nat_mul]
      ring_nf
    have e2 : Complex.exp (((r:ℝ):ℂ) * (Complex.exp ((θ:ℂ) * I) - 1)) =
        ((Real.exp (-(r:ℝ)) : ℝ) : ℂ) * NormedSpace.exp (((r:ℝ):ℂ) * Complex.exp ((θ:ℂ) * I)) := by
      rw [← congrFun Complex.exp_eq_exp_ℂ, Complex.ofReal_exp, ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [e1, e2]; exact this
  have h2 := Complex.reCLM.hasSum h1
  simp only [Complex.reCLM_apply, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re] at h2
  have h3 := (hasSum_one_poissonMeasure r).add h2
  unfold loopEnhancement poissonEnhancement
  rw [← h3.tsum_eq]
  congr 1
  funext n
  show (poissonMeasure r).real {n} * _ = _
  rw [poissonMeasure_real_singleton]
  have : (4 * Real.pi * n * alpha) = n * θ := by rw [hθ]; ring
  rw [this]; ring
