-- Prove2me | solution 1 for ArbEcon.cpow_term
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:38:42.189212+00:00
-- url     : https://prove2.me/submissions/5f14963c-73bb-40f9-8c5f-5fbca235222d

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRS_Arithmetic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.IntervalCases
/-  Probes/ArbEconomics_Sound.lean -- soundness of the Nat-only zeta evaluator (ArbEconomics_Eval).

    Every function of `ArbEconomics_Eval` is shown to produce a TRUE enclosure:
      * `logInc`   : `S <= (log m - log (m-1)) 2^P <= S + K + T`
                     (Mathlib `Real.hasSum_pow_div_log_of_abs_lt_one`, `abs_log_sub_add_sum_range_le`);
      * `termOf`   : `Rlo <= 2^P / sqrt m <= Rhi` for ANY Newton iterate (two-sided validation);
      * `trig`     : cos/sin balls of `theta` from the (pi/2)-reduction, the Horner scheme
                     (Mathlib `Complex.exp_bound`) and the quadrant rotation;
      * `step`/`run` : the loop invariant `Inv` (log bracket + Re/Im balls of the partial zeta sum).

    The main theorem `run_sound` turns a kernel-checked chunk equation
    `St.beq (run cfg L s) s' = true` into `Inv n s -> Inv (n + L) s'`.

    conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
-/










open Real Finset

namespace ArbEcon

/-! ## A. floor division / shifts, cast to ℝ -/











/-! The evaluator calls the kernel primitives directly; these `rfl` lemmas translate them back to
    notation for the proofs. -/










/-! ## B. the log increment -/











/-! ## C. the square-root bracket -/



/-! ## D. the theta interval -/



/-! ## E. Horner: real recursion, closed form, fixed-point error -/


















/-! ## F. Taylor remainders for cos / sin through `Complex.exp_bound` -/





/-! ## G. cos / sin of theta: reduction, Taylor core, rotation -/


























/-! ## H. the zeta term, the term product, one step, the run -/

theorem inv_sqrt_eq (m : ℕ) (hm : 0 < m) :
    Real.exp (-(1 / 2) * Real.log m) = 1 / Real.sqrt m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  calc Real.exp (-(1 / 2) * Real.log m) = (Real.exp ((1 / 2) * Real.log m))⁻¹ := by
        rw [← Real.exp_neg]; ring_nf
    _ = (Real.sqrt m)⁻¹ := by rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hm0]; ring_nf
    _ = 1 / Real.sqrt m := (one_div _).symm





















end ArbEcon


/-  Probes/ArbEconomics_Sound.lean -- soundness of the Nat-only zeta evaluator (ArbEconomics_Eval).

    Every function of `ArbEconomics_Eval` is shown to produce a TRUE enclosure:
      * `logInc`   : `S <= (log m - log (m-1)) 2^P <= S + K + T`
                     (Mathlib `Real.hasSum_pow_div_log_of_abs_lt_one`, `abs_log_sub_add_sum_range_le`);
      * `termOf`   : `Rlo <= 2^P / sqrt m <= Rhi` for ANY Newton iterate (two-sided validation);
      * `trig`     : cos/sin balls of `theta` from the (pi/2)-reduction, the Horner scheme
                     (Mathlib `Complex.exp_bound`) and the quadrant rotation;
      * `step`/`run` : the loop invariant `Inv` (log bracket + Re/Im balls of the partial zeta sum).

    The main theorem `run_sound` turns a kernel-checked chunk equation
    `St.beq (run cfg L s) s' = true` into `Inv n s -> Inv (n + L) s'`.

    conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
-/










open Real Finset

section
namespace ArbEcon
end ArbEcon
open ArbEcon

/-! ## A. floor division / shifts, cast to ℝ -/











/-! The evaluator calls the kernel primitives directly; these `rfl` lemmas translate them back to
    notation for the proofs. -/










/-! ## B. the log increment -/











/-! ## C. the square-root bracket -/



/-! ## D. the theta interval -/



/-! ## E. Horner: real recursion, closed form, fixed-point error -/


















/-! ## F. Taylor remainders for cos / sin through `Complex.exp_bound` -/





/-! ## G. cos / sin of theta: reduction, Taylor core, rotation -/


























/-! ## H. the zeta term, the term product, one step, the run -/




theorem solution (m : ℕ) (hm : 0 < m) (t : ℝ) :
    ((m : ℂ) ^ (-((1 : ℂ) / 2 + (t : ℂ) * Complex.I))).re = 1 / Real.sqrt m * Real.cos (t * Real.log m) ∧
    ((m : ℂ) ^ (-((1 : ℂ) / 2 + (t : ℂ) * Complex.I))).im = -(1 / Real.sqrt m * Real.sin (t * Real.log m)) := by
  have hnpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hne : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hhalf : (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have hlog : Complex.log (m : ℂ) = (Real.log m : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hnpos.le]
  have hre : (((Real.log m : ℝ) : ℂ) * -(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
      = -(1 / 2) * Real.log m := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.neg_im, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]; ring
  have him : (((Real.log m : ℝ) : ℂ) * -(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im
      = -(t * Real.log m) := by
    simp only [Complex.mul_im, Complex.neg_re, Complex.add_re, Complex.neg_im, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.I_re, Complex.I_im]; ring
  rw [Complex.cpow_def_of_ne_zero hne, hlog, hhalf]
  constructor
  · rw [Complex.exp_re, hre, him, Real.cos_neg, inv_sqrt_eq m hm]
  · rw [Complex.exp_im, hre, him, Real.sin_neg, inv_sqrt_eq m hm]; ring
