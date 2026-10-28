-- Prove2me | solution 1 for ArbEcon.sqrt_bracket
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:40:42.219796+00:00
-- url     : https://prove2.me/submissions/ec5dad83-a04a-426e-a5a7-55bebafb2aec

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

theorem natdiv_le (a b : ℕ) : ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b := Nat.cast_div_le

theorem lt_natdiv_add_one (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b < ((a / b : ℕ) : ℝ) + 1 := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_lt_iff₀ hbR]
  have h1 : a < (a / b + 1) * b := by
    have := Nat.lt_div_mul_add (a := a) hb
    nlinarith [this]
  have h2 : ((a : ℕ) : ℝ) < (((a / b + 1) * b : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h2
  linarith





theorem two_pow_pos' (P : ℕ) : (0 : ℝ) < (2 : ℝ) ^ P := by positivity

/-! The evaluator calls the kernel primitives directly; these `rfl` lemmas translate them back to
    notation for the proofs. -/










/-! ## B. the log increment -/











/-! ## C. the square-root bracket -/



/-! ## D. the theta interval -/



/-! ## E. Horner: real recursion, closed form, fixed-point error -/


















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


theorem solution (P m g : ℕ) (hm : 1 ≤ m) :
    ((Bool.rec 0 (Bool.rec (Nat.div (2 ^ (2 * P)) (Nat.mul m g)) g
        (Nat.ble (Nat.mul (Nat.mul g g) m) (2 ^ (2 * P)))) (Nat.ble 1 g) : ℕ) : ℝ)
        ≤ (2 : ℝ) ^ P / Real.sqrt m ∧
    (2 : ℝ) ^ P / Real.sqrt m ≤ ((Bool.rec (2 ^ P) (Bool.rec g
        (Nat.add (Nat.div (2 ^ (2 * P)) (Nat.mul m g)) 1)
        (Nat.ble (Nat.mul (Nat.mul g g) m) (2 ^ (2 * P)))) (Nat.ble 1 g) : ℕ) : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hsq : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  have hP : (0 : ℝ) < 2 ^ P := two_pow_pos' P
  have hsqm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt (le_of_lt hm0)
  have h1m : (1 : ℝ) ≤ Real.sqrt m := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by exact_mod_cast hm)
  set X := (2 : ℝ) ^ P / Real.sqrt m with hX
  have hX0 : 0 < X := by positivity
  have hXs : X * Real.sqrt m = 2 ^ P := by rw [hX]; field_simp
  have hXX : X * X * m = ((2 : ℝ) ^ P) ^ 2 := by
    have : (X * Real.sqrt m) * (X * Real.sqrt m) = X * X * (Real.sqrt m * Real.sqrt m) := by ring
    rw [hsqm, hXs] at this; rw [← this]; ring
  have hoS : (((2 ^ (2 * P) : ℕ)) : ℝ) = ((2 : ℝ) ^ P) ^ 2 := by push_cast; ring
  cases hpos : Nat.ble 1 g with
  | false =>
    constructor
    · exact le_of_lt (by simpa using hX0)
    · push_cast
      rw [hX, div_le_iff₀ hsq]; nlinarith
  | true =>
    have hg1 : 1 ≤ g := Nat.le_of_ble_eq_true hpos
    have hg0 : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
    have hmg : 0 < m * g := Nat.mul_pos (by omega) (by omega)
    have hq_le : ((Nat.div (2 ^ (2 * P)) (Nat.mul m g) : ℕ) : ℝ) ≤ ((2 : ℝ) ^ P) ^ 2 / ((m : ℝ) * g) := by
      have := natdiv_le (2 ^ (2 * P)) (m * g); rw [hoS] at this; push_cast at this; exact this
    have hq_lt : ((2 : ℝ) ^ P) ^ 2 / ((m : ℝ) * g) < ((Nat.div (2 ^ (2 * P)) (Nat.mul m g) : ℕ) : ℝ) + 1 := by
      have := lt_natdiv_add_one (2 ^ (2 * P)) (m * g) hmg; rw [hoS] at this; push_cast at this
      exact this
    have hkey : ((2 : ℝ) ^ P) ^ 2 / ((m : ℝ) * g) = X * X / g := by
      rw [← hXX]; field_simp
    cases hb : Nat.ble (Nat.mul (Nat.mul g g) m) (2 ^ (2 * P)) with
    | true =>
      have hle : g * g * m ≤ 2 ^ (2 * P) := Nat.le_of_ble_eq_true hb
      have hleR : (g : ℝ) * g * m ≤ ((2 : ℝ) ^ P) ^ 2 := by
        have : ((g * g * m : ℕ) : ℝ) ≤ ((2 ^ (2 * P) : ℕ) : ℝ) := by exact_mod_cast hle
        rw [hoS] at this; push_cast at this; exact this
      have hgX : (g : ℝ) ≤ X := by
        by_contra hcon; have hcon := lt_of_not_ge hcon
        have : X * X * m < (g : ℝ) * g * m := by
          have := mul_lt_mul'' hcon hcon (le_of_lt hX0) (le_of_lt hX0); nlinarith
        linarith
      constructor
      · exact hgX
      · push_cast
        have : X ≤ X * X / g := by rw [le_div_iff₀ hg0]; nlinarith
        linarith [hkey ▸ hq_lt]
    | false =>
      have hgt : ¬ (g * g * m ≤ 2 ^ (2 * P)) := by
        intro h; have h2 := Nat.ble_eq_true_of_le h
        have h3 : Nat.ble (Nat.mul (Nat.mul g g) m) (2 ^ (2 * P)) = true := h2
        rw [h3] at hb; exact Bool.noConfusion hb
      have hgtR : ((2 : ℝ) ^ P) ^ 2 < (g : ℝ) * g * m := by
        have : ((2 ^ (2 * P) : ℕ) : ℝ) < ((g * g * m : ℕ) : ℝ) := by exact_mod_cast (Nat.lt_of_not_le hgt)
        rw [hoS] at this; push_cast at this; exact this
      have hXg : X < (g : ℝ) := by
        by_contra hcon; have hcon := le_of_not_gt hcon
        have : (g : ℝ) * g * m ≤ X * X * m := by
          have := mul_le_mul hcon hcon (le_of_lt hg0) (le_of_lt hX0); nlinarith
        linarith
      constructor
      · have : X * X / g ≤ X := by rw [div_le_iff₀ hg0]; nlinarith
        linarith [hkey ▸ hq_le]
      · exact le_of_lt hXg
