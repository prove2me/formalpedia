-- Prove2me | solution 1 for ApproxGKR.error_propagation_C_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T07:09:19.447205+00:00
-- url     : https://prove2.me/submissions/78dabf64-6201-4f0b-821e-7f3c8c5be6fe

import Mathlib
import Definitions.Def_ApproxGKR_DagNode

open ApproxGKR in
theorem solution (G : ℕ → DagNode) (n : ℕ) (x xt : ℕ → ℂ) (B eop : ℝ)
    (hwf : ∀ v < n, ∀ o l r, G v = DagNode.op o l r → l < v ∧ r < v)
    (hx : ∀ v < n, ∀ o l r, G v = DagNode.op o l r → x v = o.eval (x l) (x r))
    (hB : 1 ≤ B) (hxB : ∀ v < n, ‖x v‖ ≤ B) (heop : 0 ≤ eop)
    (hin : ∀ v < n, G v = DagNode.input → ‖xt v - x v‖ ≤ eop)
    (hop : ∀ v < n, ∀ o l r, G v = DagNode.op o l r → ‖xt v - o.eval (xt l) (xt r)‖ ≤ eop)
    (hsmall : ∀ v < n, eop * (2 * B + 3) ^ (dagDepth G v) ≤ 1) :
    ∀ v < n, ‖xt v - x v‖ ≤ eop * (2 * B + 3) ^ (dagDepth G v) := by
  have hK : (1 : ℝ) ≤ 2 * B + 3 := by linarith
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hv
    cases hGv : G v with
    | input =>
      have hd : dagDepth G v = 0 := by rw [dagDepth, hGv]
      rw [hd, pow_zero, mul_one]
      exact hin v hv hGv
    | op o l r =>
      obtain ⟨hl, hr⟩ := hwf v hv o l r hGv
      have hln : l < n := by omega
      have hrn : r < n := by omega
      have hd : dagDepth G v = max (dagDepth G l) (dagDepth G r) + 1 := by
        rw [dagDepth, hGv]
        simp [hl, hr]
      have el := ih l hl hln
      have er := ih r hr hrn
      have el1 := el.trans (hsmall l hln)
      set M := max (dagDepth G l) (dagDepth G r)
      have hP : 1 ≤ (2 * B + 3) ^ M := one_le_pow₀ hK
      have elP : ‖xt l - x l‖ ≤ eop * (2 * B + 3) ^ M :=
        el.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hK (le_max_left _ _)) heop)
      have erP : ‖xt r - x r‖ ≤ eop * (2 * B + 3) ^ M :=
        er.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hK (le_max_right _ _)) heop)
      have hxl := hxB l hln
      have hxr := hxB r hrn
      have hE0 : 0 ≤ eop * (2 * B + 3) ^ M := mul_nonneg heop (by linarith)
      have hdiff : ‖o.eval (xt l) (xt r) - o.eval (x l) (x r)‖ ≤
          (2 * B + 1) * (eop * (2 * B + 3) ^ M) := by
        cases o with
        | add =>
          simp only [ArithOp.eval]
          rw [show xt l + xt r - (x l + x r) = (xt l - x l) + (xt r - x r) by ring]
          refine (norm_add_le _ _).trans ?_
          nlinarith
        | sub =>
          simp only [ArithOp.eval]
          rw [show xt l - xt r - (x l - x r) = (xt l - x l) - (xt r - x r) by ring]
          refine (norm_sub_le _ _).trans ?_
          nlinarith
        | mul =>
          simp only [ArithOp.eval]
          rw [show xt l * xt r - x l * x r = xt l * (xt r - x r) + (xt l - x l) * x r by ring]
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
          have hxtl : ‖xt l‖ ≤ B + 1 := by
            have := norm_le_norm_add_norm_sub' (xt l) (x l)
            linarith
          have t1 := mul_le_mul hxtl erP (norm_nonneg _) (by linarith)
          have t2 := mul_le_mul elP hxr (norm_nonneg _) hE0
          nlinarith
      have htri : ‖xt v - x v‖ ≤ ‖xt v - o.eval (xt l) (xt r)‖ +
          ‖o.eval (xt l) (xt r) - o.eval (x l) (x r)‖ := by
        rw [hx v hv o l r hGv]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      have h1 := hop v hv o l r hGv
      rw [hd, pow_succ]
      nlinarith [mul_le_mul_of_nonneg_left hP heop]
