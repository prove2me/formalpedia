-- Prove2me | solution 1 for ArbEcon.cos_sin_taylor
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:39:46.882701+00:00
-- url     : https://prove2.me/submissions/2389d3ce-e47c-4562-b1be-0a022d79ea8c

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
import Theorems.Thm_ArbEcon_expI_partial
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






theorem hornerR_cos (w : ℝ) : ∀ (K : ℕ) (h : ℝ),
    hornerR w ((divList fcos K).map (fun d : ℕ => (d : ℝ))) h
      = (∑ j ∈ range K, (-1) ^ j * w ^ j / ((2 * j).factorial : ℝ))
        + (-1) ^ K * w ^ K / ((2 * K).factorial : ℝ) * h := by
  intro K
  induction K with
  | zero => intro h; simp [divList, hornerR]
  | succ K ih =>
    intro h
    simp only [divList, List.map_cons]
    show hornerR w (((fcos (K + 1) : ℕ) : ℝ) :: (divList fcos K).map (fun d : ℕ => (d : ℝ))) h = _
    simp only [hornerR]
    rw [ih, sum_range_succ]
    have hf : ((fcos (K + 1) : ℕ) : ℝ) = (2 * K + 1) * (2 * K + 2) := by
      simp only [fcos]; push_cast
      rw [show 2 * (K + 1) - 1 = 2 * K + 1 by omega]; push_cast; ring
    rw [hf]
    have hfac : ((2 * (K + 1)).factorial : ℝ) = ((2 * K).factorial : ℝ) * ((2 * K + 1) * (2 * K + 2)) := by
      rw [show 2 * (K + 1) = (2 * K + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    rw [hfac]
    have h1 : ((2 * K).factorial : ℝ) ≠ 0 := by positivity
    have h2 : ((2 : ℝ) * K + 1) * (2 * K + 2) ≠ 0 := by positivity
    field_simp
    ring

theorem hornerR_sin (w : ℝ) : ∀ (K : ℕ) (h : ℝ),
    hornerR w ((divList fsin K).map (fun d : ℕ => (d : ℝ))) h
      = (∑ j ∈ range K, (-1) ^ j * w ^ j / ((2 * j + 1).factorial : ℝ))
        + (-1) ^ K * w ^ K / ((2 * K + 1).factorial : ℝ) * h := by
  intro K
  induction K with
  | zero => intro h; simp [divList, hornerR]
  | succ K ih =>
    intro h
    simp only [divList, List.map_cons]
    show hornerR w (((fsin (K + 1) : ℕ) : ℝ) :: (divList fsin K).map (fun d : ℕ => (d : ℝ))) h = _
    simp only [hornerR]
    rw [ih, sum_range_succ]
    have hf : ((fsin (K + 1) : ℕ) : ℝ) = (2 * K + 2) * (2 * K + 3) := by
      simp only [fsin]; push_cast; ring
    rw [hf]
    have hfac : ((2 * (K + 1) + 1).factorial : ℝ)
        = ((2 * K + 1).factorial : ℝ) * ((2 * K + 2) * (2 * K + 3)) := by
      rw [show 2 * (K + 1) + 1 = (2 * K + 1 + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    rw [hfac]
    have h1 : ((2 * K + 1).factorial : ℝ) ≠ 0 := by positivity
    have h2 : ((2 : ℝ) * K + 2) * (2 * K + 3) ≠ 0 := by positivity
    field_simp
    ring









/-! ## F. Taylor remainders for cos / sin through `Complex.exp_bound` -/





/-! ## G. cos / sin of theta: reduction, Taylor core, rotation -/


























/-! ## H. the zeta term, the term product, one step, the run -/























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




theorem solution (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (K : ℕ) :
    |Real.cos u - hornerR (u ^ 2) ((divList fcos K).map (fun d : ℕ => (d : ℝ))) 1|
      ≤ u ^ (2 * K + 2) * (((2 * K + 2).succ : ℝ) * (((2 * K + 2).factorial : ℝ) * (2 * K + 2 : ℕ))⁻¹) ∧
    |Real.sin u - u * hornerR (u ^ 2) ((divList fsin K).map (fun d : ℕ => (d : ℝ))) 1|
      ≤ u ^ (2 * K + 2) * (((2 * K + 2).succ : ℝ) * (((2 * K + 2).factorial : ℝ) * (2 * K + 2 : ℕ))⁻¹) := by
  have hn : 0 < 2 * K + 2 := by omega
  have hx : ‖(u : ℂ) * Complex.I‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
    exact hu1
  have hb := Complex.exp_bound hx hn
  have hnorm : ‖(u : ℂ) * Complex.I‖ = u := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
  rw [hnorm, show 2 * K + 2 = 2 * (K + 1) by ring, expI_partial u (K + 1)] at hb
  rw [show 2 * (K + 1) = 2 * K + 2 by ring] at hb
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin] at hb
  -- closed forms of the two Horner values
  have hc : hornerR (u ^ 2) ((divList fcos K).map (fun d : ℕ => (d : ℝ))) 1
      = ∑ j ∈ range (K + 1), (-1) ^ j * (u ^ 2) ^ j / ((2 * j).factorial : ℝ) := by
    rw [hornerR_cos, sum_range_succ, mul_one]
  have hs : hornerR (u ^ 2) ((divList fsin K).map (fun d : ℕ => (d : ℝ))) 1
      = ∑ j ∈ range (K + 1), (-1) ^ j * (u ^ 2) ^ j / ((2 * j + 1).factorial : ℝ) := by
    rw [hornerR_sin, sum_range_succ, mul_one]
  rw [hc, hs]
  set A := ∑ j ∈ range (K + 1), (-1) ^ j * (u ^ 2) ^ j / ((2 * j).factorial : ℝ)
  set B := u * ∑ j ∈ range (K + 1), (-1) ^ j * (u ^ 2) ^ j / ((2 * j + 1).factorial : ℝ)
  have e : (Real.cos u : ℂ) + (Real.sin u : ℂ) * Complex.I - ((A : ℂ) + (B : ℂ) * Complex.I)
      = ((Real.cos u - A : ℝ) : ℂ) + ((Real.sin u - B : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [e] at hb
  constructor
  · have := Complex.abs_re_le_norm (((Real.cos u - A : ℝ) : ℂ) + ((Real.sin u - B : ℝ) : ℂ) * Complex.I)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero] at this
    exact le_trans this hb
  · have := Complex.abs_im_le_norm (((Real.cos u - A : ℝ) : ℂ) + ((Real.sin u - B : ℝ) : ℂ) * Complex.I)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, mul_one, mul_zero, zero_add, add_zero] at this
    exact le_trans this hb
