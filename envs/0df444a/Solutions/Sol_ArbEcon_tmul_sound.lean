-- Prove2me | solution 1 for ArbEcon.tmul_sound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:40:46.395875+00:00
-- url     : https://prove2.me/submissions/076b1302-a96c-4384-b7ed-65574f8525ca

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



theorem two_pow_pos' (P : ℕ) : (0 : ℝ) < (2 : ℝ) ^ P := by positivity

/-! The evaluator calls the kernel primitives directly; these `rfl` lemmas translate them back to
    notation for the proofs. -/
@[simp] theorem p_add (a b : ℕ) : Nat.add a b = a + b := rfl
@[simp] theorem p_mul (a b : ℕ) : Nat.mul a b = a * b := rfl
@[simp] theorem p_sub (a b : ℕ) : Nat.sub a b = a - b := rfl


@[simp] theorem p_shr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl


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






theorem abs_sgn (b : Bool) : |sgn b| = 1 := by cases b <;> simp [sgn]



















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


























/-! ## H. the zeta term, the term product, one step, the run -/






theorem solution (P Rlo Rhi vm vr : ℕ) (vs : Bool) (x v : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hRlo : (Rlo : ℝ) ≤ x * 2 ^ P) (hRhi : x * 2 ^ P ≤ Rhi)
    (hv : |v * 2 ^ P - sgn vs * vm| ≤ vr) (hvm : vm ≤ 2 ^ P) :
    |x * v * 2 ^ P - sgn vs * ((Nat.shiftRight (Nat.mul Rhi vm) P : ℕ) : ℝ)|
      ≤ ((Nat.add (Nat.add (Nat.shiftRight (Nat.mul Rhi vr) P) (Nat.sub Rhi Rlo)) 2 : ℕ) : ℝ) := by
  have hP : (0 : ℝ) < 2 ^ P := two_pow_pos' P
  have hle : Rlo ≤ Rhi := by exact_mod_cast le_trans hRlo hRhi
  obtain ⟨a1, a2⟩ := shr_bounds (Rhi * vm) P
  obtain ⟨b1, b2⟩ := shr_bounds (Rhi * vr) P
  simp only [p_add, p_mul, p_sub, p_shr] at a1 a2 b1 b2 ⊢
  push_cast [Nat.cast_sub hle]
  have hvmR : (vm : ℝ) ≤ 2 ^ P := by exact_mod_cast hvm
  set T := (((Rhi * vm) >>> P : ℕ) : ℝ)
  set U := (((Rhi * vr) >>> P : ℕ) : ℝ)
  -- decomposition
  have e : x * v * 2 ^ P - sgn vs * T
      = x * (v * 2 ^ P - sgn vs * vm) + sgn vs * (vm * (x * 2 ^ P - Rhi) / 2 ^ P)
        + sgn vs * ((Rhi : ℝ) * vm / 2 ^ P - T) := by
    field_simp; ring
  rw [e]
  have t1 : |x * (v * 2 ^ P - sgn vs * vm)| ≤ U + 1 := by
    rw [abs_mul, abs_of_nonneg hx0]
    have : x * |v * 2 ^ P - sgn vs * vm| ≤ x * vr := mul_le_mul_of_nonneg_left hv hx0
    have hxr : x * (vr : ℝ) ≤ (Rhi : ℝ) * vr / 2 ^ P := by
      rw [le_div_iff₀ hP]; nlinarith [(by positivity : (0 : ℝ) ≤ vr)]
    push_cast at b2
    linarith
  have t2 : |sgn vs * (vm * (x * 2 ^ P - Rhi) / 2 ^ P)| ≤ (Rhi : ℝ) - Rlo := by
    rw [abs_mul, abs_sgn, one_mul, abs_div, abs_of_pos hP, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ vm),
      div_le_iff₀ hP]
    have : |x * 2 ^ P - Rhi| ≤ (Rhi : ℝ) - Rlo := by rw [abs_le]; constructor <;> linarith
    have hRR : (0 : ℝ) ≤ (Rhi : ℝ) - Rlo := by linarith
    nlinarith [abs_nonneg (x * 2 ^ P - Rhi)]
  have t3 : |sgn vs * ((Rhi : ℝ) * vm / 2 ^ P - T)| ≤ 1 := by
    rw [abs_mul, abs_sgn, one_mul, abs_le]
    push_cast at a1 a2
    constructor <;> linarith
  calc |x * (v * 2 ^ P - sgn vs * vm) + sgn vs * (vm * (x * 2 ^ P - Rhi) / 2 ^ P)
          + sgn vs * ((Rhi : ℝ) * vm / 2 ^ P - T)|
      ≤ |x * (v * 2 ^ P - sgn vs * vm)| + |sgn vs * (vm * (x * 2 ^ P - Rhi) / 2 ^ P)|
          + |sgn vs * ((Rhi : ℝ) * vm / 2 ^ P - T)| := by
        have := abs_add_le (x * (v * 2 ^ P - sgn vs * vm) + sgn vs * (vm * (x * 2 ^ P - Rhi) / 2 ^ P))
          (sgn vs * ((Rhi : ℝ) * vm / 2 ^ P - T))
        have := abs_add_le (x * (v * 2 ^ P - sgn vs * vm)) (sgn vs * (vm * (x * 2 ^ P - Rhi) / 2 ^ P))
        linarith
    _ ≤ (U + 1) + ((Rhi : ℝ) - Rlo) + 1 := by linarith
    _ = U + ((Rhi : ℝ) - Rlo) + 2 := by ring
