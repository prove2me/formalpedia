-- Prove2me | solution 1 for ArbEcon.horner_err
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:38:42.27287+00:00
-- url     : https://prove2.me/submissions/51a2d4d7-9a2c-44c6-a2f2-f5af3e249eb9

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



/-! ## D. the theta interval -/



/-! ## E. Horner: real recursion, closed form, fixed-point error -/

















theorem solution (one wN : ℕ) (w : ℝ) (hone : 0 < one) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hwlo : (wN : ℝ) ≤ one * w) (hwhi : (one : ℝ) * w < wN + 1) (hwN : wN ≤ one) :
    ∀ (L : List ℕ) (hN : ℕ) (hR : ℝ), (∀ d ∈ L, 2 ≤ d) → hN ≤ one → 0 ≤ hR → hR ≤ 1 →
      |(hN : ℝ) - one * hR| ≤ 3 →
      horner one wN (L.map (fun d : ℕ => one * d)) hN ≤ one ∧
      0 ≤ hornerR w (L.map (fun d : ℕ => (d : ℝ))) hR ∧ hornerR w (L.map (fun d : ℕ => (d : ℝ))) hR ≤ 1 ∧
      |(horner one wN (L.map (fun d : ℕ => one * d)) hN : ℝ)
        - one * hornerR w (L.map (fun d : ℕ => (d : ℝ))) hR| ≤ 3 := by
  intro L
  induction L with
  | nil =>
    intro hN hR _ hN1 hR0 hR1 herr
    exact ⟨hN1, hR0, hR1, herr⟩
  | cons d L ih =>
    intro hN hR hL hN1 hR0 hR1 herr
    have hd : 2 ≤ d := hL d (by simp)
    have hL' : ∀ d' ∈ L, 2 ≤ d' := fun d' hd' => hL d' (by simp [hd'])
    have honeR : (0 : ℝ) < one := by exact_mod_cast hone
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hd0 : (0 : ℝ) < d := by linarith
    -- the next Nat and real accumulators
    set Q := wN * hN / (one * d) with hQ
    have hQle : Q ≤ one := by
      rw [hQ]
      apply Nat.div_le_of_le_mul
      have : wN * hN ≤ one * one := Nat.mul_le_mul hwN hN1
      calc wN * hN ≤ one * one := this
        _ ≤ one * d * one := by nlinarith
    have hstepN : horner one wN ((d :: L).map (fun d : ℕ => one * d)) hN
        = horner one wN (L.map (fun d : ℕ => one * d)) (one - Q) := rfl
    have hstepR : hornerR w ((d :: L).map (fun d : ℕ => (d : ℝ))) hR
        = hornerR w (L.map (fun d : ℕ => (d : ℝ))) (1 - w * hR / d) := rfl
    rw [hstepN, hstepR]
    apply ih (one - Q) (1 - w * hR / d) hL' (Nat.sub_le _ _)
    · -- 0 ≤ 1 - w hR / d
      have : w * hR / d ≤ 1 / 2 := by
        rw [div_le_iff₀ hd0]; nlinarith
      linarith
    · have : 0 ≤ w * hR / d := by positivity
      linarith
    · -- the error recursion
      have hcast : ((one - Q : ℕ) : ℝ) = (one : ℝ) - Q := by
        rw [Nat.cast_sub hQle]
      rw [hcast]
      have hQlo : (Q : ℝ) ≤ (wN : ℝ) * hN / (one * d) := by
        have := natdiv_le (wN * hN) (one * d); push_cast at this; exact this
      have hQhi : (wN : ℝ) * hN / (one * d) < Q + 1 := by
        have := lt_natdiv_add_one (wN * hN) (one * d) (Nat.mul_pos hone (by omega))
        push_cast at this; exact this
      have hmain : |(one : ℝ) * w * hR / d - (wN : ℝ) * hN / (one * d)| ≤ 2 := by
        have e : (one : ℝ) * w * hR / d - (wN : ℝ) * hN / (one * d)
            = (((one : ℝ) * w - wN) * hR + (wN / one) * (one * hR - hN)) / d := by
          field_simp; ring
        rw [e, abs_div, abs_of_pos hd0, div_le_iff₀ hd0]
        have h1 : |((one : ℝ) * w - wN) * hR| ≤ 1 := by
          rw [abs_mul, abs_of_nonneg hR0]
          have : |(one : ℝ) * w - wN| ≤ 1 := by rw [abs_le]; constructor <;> linarith
          nlinarith [abs_nonneg ((one : ℝ) * w - wN)]
        have h2 : |((wN : ℝ) / one) * (one * hR - hN)| ≤ 3 := by
          rw [abs_mul]
          have hw' : |(wN : ℝ) / one| ≤ 1 := by
            rw [abs_of_nonneg (by positivity), div_le_one honeR]; exact_mod_cast hwN
          have : |(one : ℝ) * hR - hN| ≤ 3 := by rw [abs_sub_comm]; exact herr
          nlinarith [abs_nonneg ((wN : ℝ) / one), abs_nonneg ((one : ℝ) * hR - hN)]
        calc |((one : ℝ) * w - wN) * hR + (wN / one) * (one * hR - hN)|
            ≤ |((one : ℝ) * w - wN) * hR| + |(wN / one) * (one * hR - hN)| := abs_add_le _ _
          _ ≤ 4 := by linarith
          _ ≤ 2 * d := by linarith
      rw [abs_le] at hmain ⊢
      constructor
      · have : (one : ℝ) - Q - one * (1 - w * hR / d) = one * w * hR / d - Q := by ring
        rw [this]; linarith [hmain.1, hQlo]
      · have : (one : ℝ) - Q - one * (1 - w * hR / d) = one * w * hR / d - Q := by ring
        rw [this]; linarith [hmain.2, hQhi]
