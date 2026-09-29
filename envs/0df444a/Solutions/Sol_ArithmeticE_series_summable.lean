-- Prove2me | solution 1 for ArithmeticE.series_summable
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T15:53:40.845606+00:00
-- url     : https://prove2.me/submissions/4328d23f-d780-48b4-a1c5-d77efebf9d54

import Definitions.Def_rationalEArithmetic
open ArithmeticE
namespace EulerEConvergence
lemma summable_of_arithmetic (f : PowerSeries ℂ) (hf : RationalSeriesArithmetic f) (z : ℂ) :
    Summable (fun n : ℕ => PowerSeries.coeff n f * z^n) := by
  obtain ⟨a,ha,C,hC,hbound,hden⟩ := hf
  refine ((Real.summable_pow_div_factorial (C*‖z‖)).mul_left C).of_norm_bounded ?_
  intro n
  have he : PowerSeries.coeff n f = (a n:ℂ)/(n.factorial:ℂ) := by
    apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero n)).mpr
    simpa [mul_comm] using ha n
  rw [he,norm_mul,norm_div,norm_pow,Complex.norm_ratCast,Complex.norm_natCast]
  calc |(a n:ℝ)|/(n.factorial:ℝ)*‖z‖^n ≤ C^(n+1)/(n.factorial:ℝ)*‖z‖^n := by gcongr; exact hbound n
    _ = C*((C*‖z‖)^n/(n.factorial:ℝ)) := by rw [mul_pow,pow_succ]; ring
end EulerEConvergence


theorem solution (f : PowerSeries ℂ) (hf : RationalSeriesArithmetic f) (z : ℂ) :
    Summable (fun n : ℕ => PowerSeries.coeff n f * z^n) := by
  exact EulerEConvergence.summable_of_arithmetic f hf z

#print axioms solution
