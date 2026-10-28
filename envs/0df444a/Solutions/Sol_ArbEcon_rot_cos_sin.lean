-- Prove2me | solution 1 for ArbEcon.rot_cos_sin
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:39:46.873009+00:00
-- url     : https://prove2.me/submissions/3163ad8b-644e-4254-ba6c-6a8f7afd0dea

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





/-! ## G. cos / sin of theta: reduction, Taylor core, rotation -/

















theorem solution (φ : ℝ) (k : ℕ) :
    (k % 4 = 0 → Real.cos (φ + k * (π / 2)) = Real.cos φ ∧ Real.sin (φ + k * (π / 2)) = Real.sin φ) ∧
    (k % 4 = 1 → Real.cos (φ + k * (π / 2)) = -Real.sin φ ∧ Real.sin (φ + k * (π / 2)) = Real.cos φ) ∧
    (k % 4 = 2 → Real.cos (φ + k * (π / 2)) = -Real.cos φ ∧ Real.sin (φ + k * (π / 2)) = -Real.sin φ) ∧
    (k % 4 = 3 → Real.cos (φ + k * (π / 2)) = Real.sin φ ∧ Real.sin (φ + k * (π / 2)) = -Real.cos φ) := by
  have hk : (k : ℝ) * (π / 2) = ((k % 4 : ℕ) : ℝ) * (π / 2) + ((k / 4 : ℕ) : ℝ) * (2 * π) := by
    have := Nat.mod_add_div k 4
    have hR : (k : ℝ) = ((k % 4 : ℕ) : ℝ) + 4 * ((k / 4 : ℕ) : ℝ) := by exact_mod_cast this.symm
    rw [hR]; ring
  have base : ∀ j : ℕ, Real.cos (φ + k * (π / 2)) = Real.cos (φ + (k % 4 : ℕ) * (π / 2)) ∧
      Real.sin (φ + k * (π / 2)) = Real.sin (φ + (k % 4 : ℕ) * (π / 2)) := by
    intro _
    rw [hk, ← add_assoc]
    exact ⟨Real.cos_add_nat_mul_two_pi _ _, Real.sin_add_nat_mul_two_pi _ _⟩
  obtain ⟨hc, hs⟩ := base 0
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [hc, hs, h]
  · simp
  · push_cast; rw [one_mul, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]; simp
  · push_cast
    rw [show (2 : ℝ) * (π / 2) = π by ring, Real.cos_add_pi, Real.sin_add_pi]; simp
  · push_cast
    rw [show φ + (3 : ℝ) * (π / 2) = (φ + π) + π / 2 by ring, Real.cos_add_pi_div_two,
      Real.sin_add_pi_div_two, Real.sin_add_pi, Real.cos_add_pi]; simp
