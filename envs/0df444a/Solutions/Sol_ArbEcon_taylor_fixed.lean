-- Prove2me | solution 1 for ArbEcon.taylor_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:40:52.334801+00:00
-- url     : https://prove2.me/submissions/a85f4cf6-3cba-42ae-8cac-0d9eca3b900d

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
import Theorems.Thm_ArbEcon_cos_sin_taylor
import Theorems.Thm_ArbEcon_horner_err
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

@[simp] theorem p_mul (a b : ℕ) : Nat.mul a b = a * b := rfl



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










theorem fcos_ge (k : ℕ) (hk : 1 ≤ k) : 2 ≤ fcos k := by
  simp only [fcos]
  have : 1 ≤ 2 * k - 1 := by omega
  have : 2 ≤ 2 * k := by omega
  nlinarith

theorem fsin_ge (k : ℕ) (hk : 1 ≤ k) : 2 ≤ fsin k := by
  simp only [fsin]; nlinarith

theorem divList_mem {f : ℕ → ℕ} (hf : ∀ k, 1 ≤ k → 2 ≤ f k) : ∀ K, ∀ d ∈ divList f K, 2 ≤ d := by
  intro K
  induction K with
  | zero => intro d hd; simp [divList] at hd
  | succ K ih =>
    intro d hd
    simp only [divList, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact hf _ (by omega)
    · exact ih d hd



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





/-! ## G. cos / sin of theta: reduction, Taylor core, rotation -/















theorem solution (P K mag tau : ℕ) (hmag : mag * 16 ≤ 13 * 2 ^ P)
    (htau : (2 : ℝ) ^ P * taylorBnd K ≤ tau) :
    let one := 2 ^ P
    let w := Nat.shiftRight (Nat.mul mag mag) P
    let C := horner one w ((divList fcos K).map (fun d : ℕ => one * d)) one
    let S0 := Nat.shiftRight (Nat.mul mag (horner one w ((divList fsin K).map (fun d : ℕ => one * d)) one)) P
    |(C : ℝ) - 2 ^ P * Real.cos ((mag : ℝ) / 2 ^ P)| ≤ 3 + tau ∧
    |(S0 : ℝ) - 2 ^ P * Real.sin ((mag : ℝ) / 2 ^ P)| ≤ 4 + tau ∧ C ≤ one ∧ S0 ≤ one := by
  intro one w C S0
  have hP : (0 : ℝ) < 2 ^ P := two_pow_pos' P
  have hone : 0 < one := Nat.two_pow_pos P
  have honeR : ((one : ℕ) : ℝ) = (2 : ℝ) ^ P := by show ((2 ^ P : ℕ) : ℝ) = _; push_cast; ring
  set u : ℝ := (mag : ℝ) / 2 ^ P with hu
  have hu0 : 0 ≤ u := by positivity
  have hmagR : (mag : ℝ) * 16 ≤ 13 * 2 ^ P := by exact_mod_cast hmag
  have hu1 : u ≤ 13 / 16 := by rw [hu, div_le_iff₀ hP]; linarith
  have humag : (mag : ℝ) = u * 2 ^ P := by rw [hu]; field_simp
  -- w = floor(one * u^2)
  obtain ⟨w1, w2⟩ := shr_bounds (mag * mag) P
  have hwlo : (w : ℝ) ≤ (one : ℝ) * u ^ 2 := by
    rw [honeR]; have : ((mag * mag : ℕ) : ℝ) / 2 ^ P = 2 ^ P * u ^ 2 := by
      push_cast; rw [humag]; field_simp
    rw [← this]; exact w1
  have hwhi : (one : ℝ) * u ^ 2 < w + 1 := by
    rw [honeR]; have : ((mag * mag : ℕ) : ℝ) / 2 ^ P = 2 ^ P * u ^ 2 := by
      push_cast; rw [humag]; field_simp
    rw [← this]; exact w2
  have hwN : w ≤ one := by
    have : (w : ℝ) ≤ one := by
      calc (w : ℝ) ≤ one * u ^ 2 := hwlo
        _ ≤ one * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith
        _ = one := by ring
    exact_mod_cast this
  have hu21 : u ^ 2 ≤ 1 := by nlinarith
  have hbnd : u ^ (2 * K + 2) * (((2 * K + 2).succ : ℝ) * (((2 * K + 2).factorial : ℝ) * (2 * K + 2 : ℕ))⁻¹)
      ≤ taylorBnd K := by
    unfold taylorBnd
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ hu0 hu1 _
  obtain ⟨tc, ts⟩ := cos_sin_taylor u hu0 (by linarith) K
  -- cos
  have hc := horner_err one w (u ^ 2) hone (by positivity) hu21 hwlo hwhi hwN
    (divList fcos K) one 1 (divList_mem fcos_ge K) le_rfl (by norm_num) le_rfl (by simp)
  -- sin
  have hs := horner_err one w (u ^ 2) hone (by positivity) hu21 hwlo hwhi hwN
    (divList fsin K) one 1 (divList_mem fsin_ge K) le_rfl (by norm_num) le_rfl (by simp)
  obtain ⟨hcle, _, _, hcerr⟩ := hc
  obtain ⟨hsle, hs0, hs1, hserr⟩ := hs
  set Hc := hornerR (u ^ 2) ((divList fcos K).map (fun d : ℕ => (d : ℝ))) 1
  set Hs := hornerR (u ^ 2) ((divList fsin K).map (fun d : ℕ => (d : ℝ))) 1
  set G := horner one w ((divList fsin K).map (fun d : ℕ => one * d)) one
  rw [honeR] at hcerr hserr
  refine ⟨?_, ?_, hcle, ?_⟩
  · -- |C - one cos u| ≤ |C - one Hc| + one |Hc - cos u|
    have h1 : |(2 : ℝ) ^ P * Hc - 2 ^ P * Real.cos u| ≤ tau := by
      rw [← mul_sub, abs_mul, abs_of_pos hP, abs_sub_comm]
      calc 2 ^ P * |Real.cos u - Hc| ≤ 2 ^ P * taylorBnd K :=
            mul_le_mul_of_nonneg_left (le_trans tc hbnd) (le_of_lt hP)
        _ ≤ tau := htau
    calc |(C : ℝ) - 2 ^ P * Real.cos u|
        ≤ |(C : ℝ) - 2 ^ P * Hc| + |(2 : ℝ) ^ P * Hc - 2 ^ P * Real.cos u| := abs_sub_le _ _ _
      _ ≤ 3 + tau := by linarith
  · -- S0 = floor(mag G / one)
    obtain ⟨s1, s2⟩ := shr_bounds (mag * G) P
    have hGR : (G : ℝ) ≤ 2 ^ P := by rw [← honeR]; exact_mod_cast hsle
    have e1 : ((mag * G : ℕ) : ℝ) / 2 ^ P = u * G := by push_cast; rw [humag]; field_simp
    rw [e1] at s1 s2
    have h1 : |(S0 : ℝ) - u * G| ≤ 1 := by
      show |((Nat.shiftRight (Nat.mul mag G) P : ℕ) : ℝ) - u * G| ≤ 1
      simp only [p_mul] at s1 s2 ⊢
      rw [abs_le]; constructor <;> linarith
    have h2 : |u * G - 2 ^ P * (u * Hs)| ≤ 3 := by
      have : u * G - 2 ^ P * (u * Hs) = u * ((G : ℝ) - 2 ^ P * Hs) := by ring
      rw [this, abs_mul, abs_of_nonneg hu0]
      nlinarith [abs_nonneg ((G : ℝ) - 2 ^ P * Hs)]
    have h3 : |(2 : ℝ) ^ P * (u * Hs) - 2 ^ P * Real.sin u| ≤ tau := by
      rw [← mul_sub, abs_mul, abs_of_pos hP, abs_sub_comm]
      calc 2 ^ P * |Real.sin u - u * Hs| ≤ 2 ^ P * taylorBnd K :=
            mul_le_mul_of_nonneg_left (le_trans ts hbnd) (le_of_lt hP)
        _ ≤ tau := htau
    calc |(S0 : ℝ) - 2 ^ P * Real.sin u|
        ≤ |(S0 : ℝ) - u * G| + |u * G - 2 ^ P * (u * Hs)| + |(2 : ℝ) ^ P * (u * Hs) - 2 ^ P * Real.sin u| := by
          have := abs_sub_le (S0 : ℝ) (u * G) (2 ^ P * Real.sin u)
          have := abs_sub_le (u * G) (2 ^ P * (u * Hs)) (2 ^ P * Real.sin u)
          linarith
      _ ≤ 4 + tau := by linarith
  · -- S0 ≤ one
    show Nat.shiftRight (Nat.mul mag G) P ≤ one
    simp only [p_mul, p_shr, Nat.shiftRight_eq_div_pow]
    apply Nat.div_le_of_le_mul
    have hmo : mag ≤ one := by
      have : mag * 16 ≤ one * 16 := by simp only [one]; omega
      omega
    calc mag * G ≤ one * one := Nat.mul_le_mul hmo hsle
      _ = 2 ^ P * one := rfl
