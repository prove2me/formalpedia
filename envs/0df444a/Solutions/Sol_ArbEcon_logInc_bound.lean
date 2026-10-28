-- Prove2me | solution 1 for ArbEcon.logInc_bound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:39:31.003566+00:00
-- url     : https://prove2.me/submissions/d0509b5b-5e08-44c8-a83f-d17b9be1e896

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







/-- The real series value: `-log (1 - 1/m) = log m - log (m-1)`. -/
theorem log_sub_log_pred (m : ℕ) (hm : 2 ≤ m) :
    Real.log m - Real.log ((m : ℝ) - 1) = -Real.log (1 - 1 / (m : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have : (1 : ℝ) - 1 / m = ((m : ℝ) - 1) / m := by field_simp
  rw [this, Real.log_div (ne_of_gt hm1) (ne_of_gt hm0)]
  ring



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










theorem solution (P m : ℕ) (hm : 2 ≤ m) (r : ℕ × ℕ × ℕ) (hr : LogSpec (2 ^ P) m r) :
    (r.1 : ℝ) ≤ (Real.log m - Real.log ((m : ℝ) - 1)) * 2 ^ P ∧
    (Real.log m - Real.log ((m : ℝ) - 1)) * 2 ^ P
      ≤ (r.1 : ℝ) + r.2.1 + ((2 ^ (P + 1) / r.2.2 : ℕ) + 1) := by
  obtain ⟨hS, hpw⟩ := hr
  set K := r.2.1 with hK
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  set x : ℝ := 1 / (m : ℝ) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 / 2 := by rw [hx]; rw [div_le_div_iff₀ hm0 (by norm_num)]; linarith
  have habs : |x| < 1 := by rw [abs_of_pos hx0]; linarith
  have hP : (0 : ℝ) < 2 ^ P := two_pow_pos' P
  rw [log_sub_log_pred m hm]
  -- the real partial sum and its relation to the floors
  set sr : ℝ := ∑ i ∈ range K, x ^ (i + 1) / (i + 1) with hsr
  have hterm : ∀ i : ℕ, (2 : ℝ) ^ P * (x ^ (i + 1) / (i + 1))
      = ((2 ^ P : ℕ) : ℝ) / ((m ^ (i + 1) * (i + 1) : ℕ) : ℝ) := by
    intro i
    rw [hx, div_pow, one_pow]; push_cast; field_simp
  have hden : ∀ i : ℕ, 0 < m ^ (i + 1) * (i + 1) := fun i => by positivity
  have hlo_sum : (r.1 : ℝ) ≤ 2 ^ P * sr := by
    rw [hS, hsr, mul_sum]; push_cast
    apply sum_le_sum; intro i _
    rw [hterm i]
    have := natdiv_le (2 ^ P) (m ^ (i + 1) * (i + 1))
    push_cast at this ⊢; exact this
  have hhi_sum : 2 ^ P * sr ≤ (r.1 : ℝ) + K := by
    rw [hS, hsr, mul_sum]; push_cast
    have : ∑ i ∈ range K, (2 : ℝ) ^ P * (x ^ (i + 1) / (i + 1))
        ≤ ∑ i ∈ range K, (((2 ^ P / (m ^ (i + 1) * (i + 1)) : ℕ) : ℝ) + 1) := by
      apply sum_le_sum; intro i _
      rw [hterm i]
      exact le_of_lt (lt_natdiv_add_one _ _ (hden i))
    rw [sum_add_distrib] at this
    simpa using this
  -- lower bound: nonneg series dominates its partial sums
  have hsum := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have hlow : sr ≤ -Real.log (1 - x) := by
    rw [hsr]
    apply sum_le_hasSum (range K) _ hsum
    intro i _; positivity
  -- upper bound: the Mathlib tail estimate
  have htail := Real.abs_log_sub_add_sum_range_le habs K
  rw [abs_of_pos hx0] at htail
  have hup : -Real.log (1 - x) ≤ sr + x ^ (K + 1) / (1 - x) := by
    have := (abs_le.mp htail).1; rw [← hsr] at this; linarith
  have htailU : (2 : ℝ) ^ P * (x ^ (K + 1) / (1 - x))
      ≤ (((2 ^ (P + 1) / r.2.2 : ℕ) : ℝ) + 1) := by
    have hpwpos : 0 < r.2.2 := by rw [hpw]; positivity
    have h1 : (2 : ℝ) ^ P * (x ^ (K + 1) / (1 - x)) ≤ ((2 ^ (P + 1) : ℕ) : ℝ) / (r.2.2 : ℝ) := by
      have hmK : (0 : ℝ) < (m : ℝ) ^ K := by positivity
      have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
      have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm0
      have hm1ne : (m : ℝ) - 1 ≠ 0 := ne_of_gt hm1
      have e1 : x ^ (K + 1) / (1 - x) = 1 / ((m : ℝ) ^ K * ((m : ℝ) - 1)) := by
        rw [hx, show (1 : ℝ) - 1 / m = ((m : ℝ) - 1) / m by field_simp, div_pow, one_pow,
          div_div_eq_mul_div, pow_succ]
        field_simp
      have e2 : ((2 ^ (P + 1) : ℕ) : ℝ) / (r.2.2 : ℝ) = 2 * 2 ^ P / ((m : ℝ) ^ K * m) := by
        rw [hpw]; push_cast; ring
      rw [e1, e2, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have hmm : (m : ℝ) ≤ 2 * ((m : ℝ) - 1) := by linarith
      have := mul_le_mul_of_nonneg_left hmm (le_of_lt (mul_pos hP hmK))
      nlinarith [this]
    exact le_trans h1 (le_of_lt (lt_natdiv_add_one _ _ hpwpos))
  constructor
  · nlinarith [hlo_sum, hlow, hP]
  · have := mul_le_mul_of_nonneg_left hup (le_of_lt hP)
    nlinarith [hhi_sum, htailU, this]
