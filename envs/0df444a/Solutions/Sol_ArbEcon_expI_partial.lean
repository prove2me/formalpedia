-- Prove2me | solution 1 for ArbEcon.expI_partial
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:38:47.402072+00:00
-- url     : https://prove2.me/submissions/8fd771c9-dbc7-4114-9c9b-1aeefe318112

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


theorem solution (u : ℝ) : ∀ K : ℕ,
    ∑ m ∈ range (2 * K), ((u : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)
      = ((∑ j ∈ range K, (-1) ^ j * (u ^ 2) ^ j / ((2 * j).factorial : ℝ) : ℝ) : ℂ)
        + ((u * ∑ j ∈ range K, (-1) ^ j * (u ^ 2) ^ j / ((2 * j + 1).factorial : ℝ) : ℝ) : ℂ)
          * Complex.I := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, sum_range_succ, mul_add]
    have hI2 : ((u : ℂ) * Complex.I) ^ (2 * K) = ((-1) ^ K * (u ^ 2) ^ K : ℝ) := by
      rw [pow_mul, mul_pow, Complex.I_sq]; push_cast; ring
    have hI3 : ((u : ℂ) * Complex.I) ^ (2 * K + 1) = ((-1) ^ K * (u ^ 2) ^ K * u : ℝ) * Complex.I := by
      rw [pow_succ, hI2]; push_cast; ring
    rw [hI2, hI3]
    push_cast
    ring
