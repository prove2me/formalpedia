-- Prove2me | solution 1 for ArbEcon.trig_sound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:42:12.474235+00:00
-- url     : https://prove2.me/submissions/e0d83e5c-6f12-4fea-8422-dab2940cade8

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
import Theorems.Thm_ArbEcon_phi_ball
import Theorems.Thm_ArbEcon_rot_cos_sin
import Theorems.Thm_ArbEcon_taylor_fixed
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









theorem two_pow_pos' (P : ℕ) : (0 : ℝ) < (2 : ℝ) ^ P := by positivity

/-! The evaluator calls the kernel primitives directly; these `rfl` lemmas translate them back to
    notation for the proofs. -/
@[simp] theorem p_add (a b : ℕ) : Nat.add a b = a + b := rfl



@[simp] theorem p_mod (a b : ℕ) : Nat.mod a b = a % b := rfl





/-! ## B. the log increment -/











/-! ## C. the square-root bracket -/



/-! ## D. the theta interval -/



/-! ## E. Horner: real recursion, closed form, fixed-point error -/


















/-! ## F. Taylor remainders for cos / sin through `Complex.exp_bound` -/





/-! ## G. cos / sin of theta: reduction, Taylor core, rotation -/



@[simp] theorem sgn_true : sgn true = 1 := rfl
@[simp] theorem sgn_false : sgn false = -1 := rfl
theorem sgn_not (b : Bool) : sgn (!b) = -sgn b := by cases b <;> simp [sgn]
theorem abs_sgn (b : Bool) : |sgn b| = 1 := by cases b <;> simp [sgn]











theorem rotate_sound (P : ℕ) (φ : ℝ) (k : ℕ) (C rc S0 rs : ℕ) (sy : Bool)
    (hc : |Real.cos φ * 2 ^ P - C| ≤ rc) (hs : |Real.sin φ * 2 ^ P - sgn sy * S0| ≤ rs) :
    SBall P (Real.cos (φ + k * (π / 2)))
      (rotate (Nat.beq (Nat.mod (Nat.mod k 4) 2) 1) (Nat.ble 2 (Nat.mod k 4)) C rc S0 sy rs).cm
      (rotate (Nat.beq (Nat.mod (Nat.mod k 4) 2) 1) (Nat.ble 2 (Nat.mod k 4)) C rc S0 sy rs).cs
      (rotate (Nat.beq (Nat.mod (Nat.mod k 4) 2) 1) (Nat.ble 2 (Nat.mod k 4)) C rc S0 sy rs).cr ∧
    SBall P (Real.sin (φ + k * (π / 2)))
      (rotate (Nat.beq (Nat.mod (Nat.mod k 4) 2) 1) (Nat.ble 2 (Nat.mod k 4)) C rc S0 sy rs).sm
      (rotate (Nat.beq (Nat.mod (Nat.mod k 4) 2) 1) (Nat.ble 2 (Nat.mod k 4)) C rc S0 sy rs).ss
      (rotate (Nat.beq (Nat.mod (Nat.mod k 4) 2) 1) (Nat.ble 2 (Nat.mod k 4)) C rc S0 sy rs).sr ∧
    (rotate (Nat.beq (Nat.mod (Nat.mod k 4) 2) 1) (Nat.ble 2 (Nat.mod k 4)) C rc S0 sy rs).cm ≤ max C S0 ∧
    (rotate (Nat.beq (Nat.mod (Nat.mod k 4) 2) 1) (Nat.ble 2 (Nat.mod k 4)) C rc S0 sy rs).sm ≤ max C S0 := by
  obtain ⟨r0, r1, r2, r3⟩ := rot_cos_sin φ k
  have hj : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  simp only [p_mod]
  unfold SBall
  generalize hjj : k % 4 = j at *
  interval_cases j
  · obtain ⟨e1, e2⟩ := r0 rfl
    refine ⟨?_, ?_, le_max_left _ _, le_max_right _ _⟩
    · show |Real.cos (φ + k * (π / 2)) * 2 ^ P - sgn true * C| ≤ rc
      rw [e1, sgn_true, one_mul]; exact hc
    · show |Real.sin (φ + k * (π / 2)) * 2 ^ P - sgn sy * S0| ≤ rs
      rw [e2]; exact hs
  · obtain ⟨e1, e2⟩ := r1 rfl
    refine ⟨?_, ?_, le_max_right _ _, le_max_left _ _⟩
    · show |Real.cos (φ + k * (π / 2)) * 2 ^ P - sgn (!sy) * S0| ≤ rs
      rw [e1, sgn_not, show -Real.sin φ * 2 ^ P - -sgn sy * S0 = -(Real.sin φ * 2 ^ P - sgn sy * S0) by ring,
        abs_neg]; exact hs
    · show |Real.sin (φ + k * (π / 2)) * 2 ^ P - sgn true * C| ≤ rc
      rw [e2, sgn_true, one_mul]; exact hc
  · obtain ⟨e1, e2⟩ := r2 rfl
    refine ⟨?_, ?_, le_max_left _ _, le_max_right _ _⟩
    · show |Real.cos (φ + k * (π / 2)) * 2 ^ P - sgn false * C| ≤ rc
      rw [e1, sgn_false, show -Real.cos φ * 2 ^ P - -1 * (C : ℝ) = -(Real.cos φ * 2 ^ P - C) by ring,
        abs_neg]; exact hc
    · show |Real.sin (φ + k * (π / 2)) * 2 ^ P - sgn (!sy) * S0| ≤ rs
      rw [e2, sgn_not, show -Real.sin φ * 2 ^ P - -sgn sy * S0 = -(Real.sin φ * 2 ^ P - sgn sy * S0) by ring,
        abs_neg]; exact hs
  · obtain ⟨e1, e2⟩ := r3 rfl
    refine ⟨?_, ?_, le_max_right _ _, le_max_left _ _⟩
    · show |Real.cos (φ + k * (π / 2)) * 2 ^ P - sgn sy * S0| ≤ rs
      rw [e1]; exact hs
    · show |Real.sin (φ + k * (π / 2)) * 2 ^ P - sgn false * C| ≤ rc
      rw [e2, sgn_false, show -Real.cos φ * 2 ^ P - -1 * (C : ℝ) = -(Real.cos φ * 2 ^ P - C) by ring,
        abs_neg]; exact hc







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
























theorem solution (c : Cfg) (t : ℝ) (K : ℕ) (hv : Valid c t K) (θ : ℝ) (thlo thhi : ℕ)
    (hlo : (thlo : ℝ) ≤ θ * 2 ^ c.P) (hhi : θ * 2 ^ c.P ≤ thhi) :
    TrigOK c.P θ (trig c thlo thhi) := by
  have hP : (0 : ℝ) < 2 ^ c.P := two_pow_pos' c.P
  set k := Nat.div (Nat.add thlo c.hph) c.hp with hk
  set φ := θ - k * (Real.pi / 2) with hφ
  have hθ : θ = φ + k * (Real.pi / 2) := by rw [hφ]; ring
  have hball := phi_ball c.P c.hp c.rp k thlo thhi θ hlo hhi hv.pi_ball
  rw [← hφ] at hball
  set pos := Nat.ble (Nat.shiftLeft (Nat.mul k c.hp) 1) (Nat.add thlo thhi) with hpos
  set mag := Nat.shiftRight (Bool.rec (Nat.sub (Nat.shiftLeft (Nat.mul k c.hp) 1) (Nat.add thlo thhi))
              (Nat.sub (Nat.add thlo thhi) (Nat.shiftLeft (Nat.mul k c.hp) 1)) pos) 1 with hmag
  set rphi := Nat.add (Nat.add (Nat.shiftRight (Nat.sub thhi thlo) 1) (Nat.mul k c.rp)) 2 with hrphi
  have htrig : trig c thlo thhi = Bool.rec
      (rotate (Nat.beq (Nat.mod (Nat.mod k 4) 2) 1) (Nat.ble 2 (Nat.mod k 4)) 0 c.one 0 pos c.one)
      (rotate (Nat.beq (Nat.mod (Nat.mod k 4) 2) 1) (Nat.ble 2 (Nat.mod k 4))
        (c.hc (Nat.shiftRight (Nat.mul mag mag) c.P)) (Nat.add (Nat.add 3 c.tau) rphi)
        (Nat.shiftRight (Nat.mul mag (c.hs (Nat.shiftRight (Nat.mul mag mag) c.P))) c.P) pos
        (Nat.add (Nat.add 4 c.tau) rphi))
      (Nat.ble mag c.umax) := rfl
  rw [htrig]
  -- Lipschitz transfer from the center `sgn pos * u` to `phi`
  set u : ℝ := (mag : ℝ) / 2 ^ c.P with hu
  have hdist : |φ - sgn pos * u| * 2 ^ c.P ≤ rphi := by
    have : (φ - sgn pos * u) * 2 ^ c.P = φ * 2 ^ c.P - sgn pos * mag := by
      rw [hu]; field_simp
    rw [show |φ - sgn pos * u| * 2 ^ c.P = |(φ - sgn pos * u) * 2 ^ c.P| by
      rw [abs_mul, abs_of_pos hP], this]; exact hball
  have hcosφ : |Real.cos φ - Real.cos u| * 2 ^ c.P ≤ rphi := by
    have hcu : Real.cos (sgn pos * u) = Real.cos u := by
      cases pos <;> simp [sgn]
    rw [← hcu]
    exact le_trans (mul_le_mul_of_nonneg_right (Real.abs_cos_sub_cos_le _ _) (le_of_lt hP)) hdist
  have hsinφ : |Real.sin φ - sgn pos * Real.sin u| * 2 ^ c.P ≤ rphi := by
    have hsu : Real.sin (sgn pos * u) = sgn pos * Real.sin u := by
      cases pos <;> simp [sgn]
    rw [← hsu]
    exact le_trans (mul_le_mul_of_nonneg_right (Real.abs_sin_sub_sin_le _ _) (le_of_lt hP)) hdist
  cases hbr : Nat.ble mag c.umax with
  | false =>
    -- fallback: magnitudes 0, radii 2^P
    have hc0 : |Real.cos φ * 2 ^ c.P - ((0 : ℕ) : ℝ)| ≤ (c.one : ℝ) := by
      rw [hv.one_eq]; push_cast
      rw [sub_zero, abs_mul, abs_of_pos hP]
      exact mul_le_of_le_one_left (le_of_lt hP) (Real.abs_cos_le_one _)
    have hs0 : |Real.sin φ * 2 ^ c.P - sgn pos * ((0 : ℕ) : ℝ)| ≤ (c.one : ℝ) := by
      rw [hv.one_eq]; push_cast
      rw [mul_zero, sub_zero, abs_mul, abs_of_pos hP]
      exact mul_le_of_le_one_left (le_of_lt hP) (Real.abs_sin_le_one _)
    obtain ⟨h1, h2, h3, h4⟩ := rotate_sound c.P φ k 0 c.one 0 c.one pos hc0 hs0
    rw [← hθ] at h1 h2
    refine ⟨h1, h2, ?_, ?_⟩
    · exact le_trans h3 (by simp)
    · exact le_trans h4 (by simp)
  | true =>
    have hmu : mag * 16 ≤ 13 * 2 ^ c.P :=
      le_trans (Nat.mul_le_mul_right 16 (Nat.le_of_ble_eq_true hbr)) hv.umax_le
    have hT := taylor_fixed c.P K mag c.tau hmu hv.tau_ok
    simp only at hT
    rw [hv.hc_eq, hv.hs_eq, hv.dcos_eq, hv.dsin_eq, hv.one_eq]
    obtain ⟨tC, tS, tCle, tSle⟩ := hT
    rw [← hu] at tC tS
    set C := horner (2 ^ c.P) (Nat.shiftRight (Nat.mul mag mag) c.P)
      ((divList fcos K).map (fun d : ℕ => 2 ^ c.P * d)) (2 ^ c.P)
    set S0 := Nat.shiftRight (Nat.mul mag (horner (2 ^ c.P) (Nat.shiftRight (Nat.mul mag mag) c.P)
      ((divList fsin K).map (fun d : ℕ => 2 ^ c.P * d)) (2 ^ c.P))) c.P
    have hc1 : |Real.cos φ * 2 ^ c.P - C| ≤ ((Nat.add (Nat.add 3 c.tau) rphi : ℕ) : ℝ) := by
      have e : Real.cos φ * 2 ^ c.P - C = (Real.cos φ - Real.cos u) * 2 ^ c.P + (2 ^ c.P * Real.cos u - C) := by ring
      rw [e]
      calc |(Real.cos φ - Real.cos u) * 2 ^ c.P + (2 ^ c.P * Real.cos u - C)|
          ≤ |(Real.cos φ - Real.cos u) * 2 ^ c.P| + |2 ^ c.P * Real.cos u - (C : ℝ)| := abs_add_le _ _
        _ ≤ rphi + (3 + c.tau) := by
          have a1 : |(Real.cos φ - Real.cos u) * 2 ^ c.P| ≤ rphi := by
            rw [abs_mul, abs_of_pos hP]; exact hcosφ
          have a2 : |2 ^ c.P * Real.cos u - (C : ℝ)| ≤ 3 + c.tau := by
            rw [abs_sub_comm]; exact tC
          exact add_le_add a1 a2
        _ = _ := by simp only [p_add]; push_cast; ring
    have hs1 : |Real.sin φ * 2 ^ c.P - sgn pos * S0| ≤ ((Nat.add (Nat.add 4 c.tau) rphi : ℕ) : ℝ) := by
      have e : Real.sin φ * 2 ^ c.P - sgn pos * S0
          = (Real.sin φ - sgn pos * Real.sin u) * 2 ^ c.P + sgn pos * (2 ^ c.P * Real.sin u - S0) := by ring
      rw [e]
      calc |(Real.sin φ - sgn pos * Real.sin u) * 2 ^ c.P + sgn pos * (2 ^ c.P * Real.sin u - S0)|
          ≤ |(Real.sin φ - sgn pos * Real.sin u) * 2 ^ c.P| + |sgn pos * (2 ^ c.P * Real.sin u - (S0 : ℝ))| :=
            abs_add_le _ _
        _ ≤ rphi + (4 + c.tau) := by
          have a1 : |(Real.sin φ - sgn pos * Real.sin u) * 2 ^ c.P| ≤ rphi := by
            rw [abs_mul, abs_of_pos hP]; exact hsinφ
          have a2 : |sgn pos * (2 ^ c.P * Real.sin u - (S0 : ℝ))| ≤ 4 + c.tau := by
            rw [abs_mul, abs_sgn, one_mul, abs_sub_comm]; exact tS
          exact add_le_add a1 a2
        _ = _ := by simp only [p_add]; push_cast; ring
    obtain ⟨h1, h2, h3, h4⟩ := rotate_sound c.P φ k C _ S0 _ pos hc1 hs1
    rw [← hθ] at h1 h2
    refine ⟨h1, h2, le_trans h3 (max_le tCle tSle), le_trans h4 (max_le tCle tSle)⟩
