-- Prove2me | solution 1 for ArbEcon.phi_ball
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:39:35.767859+00:00
-- url     : https://prove2.me/submissions/fc649967-d8c8-4e48-8139-7e49b6223ea1

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

theorem shr_eq (a d : ℕ) : Nat.shiftRight a d = a / 2 ^ d := Nat.shiftRight_eq_div_pow a d





/-! The evaluator calls the kernel primitives directly; these `rfl` lemmas translate them back to
    notation for the proofs. -/
@[simp] theorem p_add (a b : ℕ) : Nat.add a b = a + b := rfl
@[simp] theorem p_mul (a b : ℕ) : Nat.mul a b = a * b := rfl
@[simp] theorem p_sub (a b : ℕ) : Nat.sub a b = a - b := rfl


@[simp] theorem p_shr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
@[simp] theorem p_shl (a b : ℕ) : Nat.shiftLeft a b = a <<< b := rfl

/-- `⌊a / 2^d⌋ ≤ a / 2^d < ⌊a / 2^d⌋ + 1` over ℝ. -/
theorem shr_bounds (a d : ℕ) :
    ((Nat.shiftRight a d : ℕ) : ℝ) ≤ (a : ℝ) / 2 ^ d ∧ (a : ℝ) / 2 ^ d < (Nat.shiftRight a d : ℝ) + 1 := by
  rw [shr_eq]
  have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
  have e : ((2 ^ d : ℕ) : ℝ) = (2 : ℝ) ^ d := by push_cast; ring
  constructor
  · have := natdiv_le a (2 ^ d); rw [e] at this; exact this
  · have := lt_natdiv_add_one a (2 ^ d) hpos; rw [e] at this; exact this

/-! ## B. the log increment -/











/-! ## C. the square-root bracket -/



/-! ## D. the theta interval -/



/-! ## E. Horner: real recursion, closed form, fixed-point error -/


















/-! ## F. Taylor remainders for cos / sin through `Complex.exp_bound` -/





/-! ## G. cos / sin of theta: reduction, Taylor core, rotation -/



@[simp] theorem sgn_true : sgn true = 1 := rfl
@[simp] theorem sgn_false : sgn false = -1 := rfl





















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





/-! ## G. cos / sin of theta: reduction, Taylor core, rotation -/











theorem solution (P hp rp k thlo thhi : ℕ) (θ : ℝ)
    (hlo : (thlo : ℝ) ≤ θ * 2 ^ P) (hhi : θ * 2 ^ P ≤ thhi)
    (hpi : |Real.pi / 2 * 2 ^ P - hp| ≤ rp) :
    |(θ - k * (Real.pi / 2)) * 2 ^ P
        - sgn (Nat.ble (Nat.shiftLeft (Nat.mul k hp) 1) (Nat.add thlo thhi))
          * ((Nat.shiftRight (Bool.rec (Nat.sub (Nat.shiftLeft (Nat.mul k hp) 1) (Nat.add thlo thhi))
              (Nat.sub (Nat.add thlo thhi) (Nat.shiftLeft (Nat.mul k hp) 1))
              (Nat.ble (Nat.shiftLeft (Nat.mul k hp) 1) (Nat.add thlo thhi))) 1 : ℕ) : ℝ)|
      ≤ ((Nat.add (Nat.add (Nat.shiftRight (Nat.sub thhi thlo) 1) (Nat.mul k rp)) 2 : ℕ) : ℝ) := by
  have hle : thlo ≤ thhi := by exact_mod_cast le_trans hlo hhi
  have hk : |(k : ℝ) * (Real.pi / 2) * 2 ^ P - k * hp| ≤ k * rp := by
    have : (k : ℝ) * (Real.pi / 2) * 2 ^ P - k * hp = k * (Real.pi / 2 * 2 ^ P - hp) := by ring
    rw [this, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k)]
    exact mul_le_mul_of_nonneg_left hpi (by positivity)
  obtain ⟨hw1, hw2⟩ := shr_bounds (thhi - thlo) 1
  have hsubc : (((thhi - thlo : ℕ)) : ℝ) = (thhi : ℝ) - thlo := by rw [Nat.cast_sub hle]
  rw [hsubc, pow_one] at hw1 hw2
  simp only [p_add, p_mul, p_sub, p_shr, p_shl, Nat.shiftLeft_eq, pow_one] at *
  set M1 := thlo + thhi with hM1
  set M2 := k * hp * 2 with hM2
  have hcenter : |θ * 2 ^ P - ((thlo : ℝ) + thhi) / 2| ≤ ((thhi : ℝ) - thlo) / 2 := by
    rw [abs_le]; constructor <;> linarith
  cases hb : Nat.ble M2 M1 with
  | true =>
    have hM : M2 ≤ M1 := Nat.le_of_ble_eq_true hb
    obtain ⟨m1, m2⟩ := shr_bounds (M1 - M2) 1
    have hc : (((M1 - M2 : ℕ)) : ℝ) = (M1 : ℝ) - M2 := by rw [Nat.cast_sub hM]
    rw [hc, pow_one] at m1 m2
    simp only [p_shr] at m1 m2
    simp only [sgn_true, one_mul]
    push_cast [hM1, hM2] at m1 m2 ⊢
    rw [abs_le] at hk ⊢
    constructor <;> nlinarith [hk.1, hk.2, hcenter, abs_le.mp hcenter, hw1, hw2, m1, m2]
  | false =>
    have hM : M1 < M2 := Nat.lt_of_not_le (fun h => by
      have := Nat.ble_eq_true_of_le h; rw [this] at hb; exact Bool.noConfusion hb)
    obtain ⟨m1, m2⟩ := shr_bounds (M2 - M1) 1
    have hc : (((M2 - M1 : ℕ)) : ℝ) = (M2 : ℝ) - M1 := by rw [Nat.cast_sub (le_of_lt hM)]
    rw [hc, pow_one] at m1 m2
    simp only [p_shr] at m1 m2
    simp only [sgn_false, neg_one_mul, sub_neg_eq_add]
    push_cast [hM1, hM2] at m1 m2 ⊢
    rw [abs_le] at hk ⊢
    constructor <;> nlinarith [hk.1, hk.2, hcenter, abs_le.mp hcenter, hw1, hw2, m1, m2]
