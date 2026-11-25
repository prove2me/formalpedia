-- Prove2me | solution 1 for Arxiv1007_0377.real_branches_formula
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T14:49:45.061524+00:00
-- url     : https://prove2.me/submissions/5cf96f19-f617-4f0f-be7e-2c49b1b12c50

import Mathlib
import Definitions.Def_Arxiv1007_0377_Basic

open Complex Polynomial

namespace Arxiv1007_0377

theorem real_branches_formula (ε μ : ℂ) :
    0 ≤ branchRadicand ε μ ∧
    indexQuartic ε μ =
      (X - C ((nPlus ε μ : ℝ) : ℂ)) * (X - C ((nMinus ε μ : ℝ) : ℂ)) *
        (X - C (((Real.sqrt (‖ε‖ * ‖μ‖ - epsMuRe ε μ) / Real.sqrt 2 : ℝ) : ℂ) * I)) *
        (X + C (((Real.sqrt (‖ε‖ * ‖μ‖ - epsMuRe ε μ) / Real.sqrt 2 : ℝ) : ℂ) * I)) ∧
    (∀ N : ℂ, N ^ 2 = ε * μ → N.re = nPlus ε μ ∨ N.re = nMinus ε μ) ∧
    (∃ N : ℂ, N ^ 2 = ε * μ ∧ N.re = nPlus ε μ) ∧
    (∃ N : ℂ, N ^ 2 = ε * μ ∧ N.re = nMinus ε μ) := by
  set s := ‖ε‖ * ‖μ‖ with hsdef
  set a := epsMuRe ε μ with ha
  set b := epsMuIm ε μ with hb
  have s0 : 0 ≤ s := by positivity
  have hs2 : s ^ 2 = a ^ 2 + b ^ 2 := by
    rw [hsdef, ha, hb, epsMuRe, epsMuIm, mul_pow, Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    ring
  have hsa : |a| ≤ s := by
    apply abs_le_of_sq_le_sq' _ s0 |>.elim (fun h1 h2 => abs_le.mpr ⟨h1, h2⟩)
    nlinarith
  have hA0 : 0 ≤ a + s := by have := neg_abs_le a; linarith
  have hB0 : 0 ≤ s - a := by have := le_abs_self a; linarith
  have hbr : branchRadicand ε μ = a + s := by rw [branchRadicand, ha, epsMuRe]
  set α := nPlus ε μ with hα
  have hαv : α = Real.sqrt (a + s) / Real.sqrt 2 := by rw [hα, nPlus, hbr]
  have hα0 : 0 ≤ α := by rw [hαv]; positivity
  have hα2 : α ^ 2 = (a + s) / 2 := by
    rw [hαv, div_pow, Real.sq_sqrt hA0, Real.sq_sqrt (by norm_num)]
  have hnm : nMinus ε μ = -α := by rw [hα]; rfl
  set β := Real.sqrt (s - a) / Real.sqrt 2 with hβ
  have hβ2 : β ^ 2 = (s - a) / 2 := by
    rw [hβ, div_pow, Real.sq_sqrt hB0, Real.sq_sqrt (by norm_num)]
  -- every square root has real part ±α
  have P3 : ∀ N : ℂ, N ^ 2 = ε * μ → N.re = α ∨ N.re = -α := by
    intro N hN
    have hre := congrArg Complex.re hN
    have him := congrArg Complex.im hN
    simp only [sq, Complex.mul_re, Complex.mul_im] at hre him
    have e1 : N.re * N.re - N.im * N.im = a := by rw [ha, epsMuRe]; linarith
    have e2 : 2 * (N.re * N.im) = b := by rw [hb, epsMuIm]; linarith
    have hx2 : N.re ^ 2 = (a + s) / 2 := by
      have hprod : (2 * N.re ^ 2 - a - s) * (N.re ^ 2 + N.im ^ 2 + s) = 0 := by
        have : (2 * N.re ^ 2 - a) ^ 2 = s ^ 2 := by rw [hs2, ← e2, ← e1]; ring
        linear_combination this - (2 * N.re ^ 2 - a - s) * e1
      rcases mul_eq_zero.mp hprod with h | h
      · linarith
      · have q1 := sq_nonneg N.re
        have q2 := sq_nonneg N.im
        have hx : N.re ^ 2 = 0 := by linarith
        have hy : N.im ^ 2 = 0 := by linarith
        have hs' : s = 0 := by linarith
        have : a = 0 := by
          have : N.re * N.re - N.im * N.im = N.re ^ 2 - N.im ^ 2 := by ring
          linarith
        rw [hx, hs', this]; norm_num
    rw [← hα2] at hx2
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hx2
  obtain ⟨N0, hN0⟩ := IsAlgClosed.exists_pow_nat_eq (ε * μ) (by norm_num : 0 < 2)
  have hN0' : (-N0) ^ 2 = ε * μ := by rw [neg_sq]; exact hN0
  refine ⟨by rw [hbr]; exact hA0, ?_, fun N hN => by rw [hnm]; exact P3 N hN, ?_, ?_⟩
  · rw [hnm]
    have h1 : C ((α : ℝ) : ℂ) ^ 2 = C ((((a + s) / 2 : ℝ)) : ℂ) := by
      rw [← map_pow, ← Complex.ofReal_pow, hα2]
    have h2 : C (((β : ℝ) : ℂ) * I) ^ 2 = -C ((((s - a) / 2 : ℝ)) : ℂ) := by
      rw [← map_pow, mul_pow, ← Complex.ofReal_pow, hβ2, I_sq, ← map_neg]; ring_nf
    have h3 : C ((((a + s) / 2 : ℝ)) : ℂ) - C ((((s - a) / 2 : ℝ)) : ℂ) = C ((a : ℝ) : ℂ) := by
      rw [← map_sub]; congr 1; push_cast; ring
    have h4 : C ((((a + s) / 2 : ℝ)) : ℂ) * C ((((s - a) / 2 : ℝ)) : ℂ) =
        C ((((b / 2) ^ 2 : ℝ)) : ℂ) := by
      rw [← map_mul]; congr 1; rw [← Complex.ofReal_mul]; congr 1; nlinarith
    unfold indexQuartic
    rw [← ha, ← hb, Complex.ofReal_neg, map_neg, sub_neg_eq_add]
    linear_combination (X ^ 2 - C (((β : ℝ) : ℂ) * I) ^ 2) * h1 +
      (X ^ 2 - C ((((a + s) / 2 : ℝ)) : ℂ)) * h2 + X ^ 2 * h3 + h4
  · rcases P3 N0 hN0 with h | h
    · exact ⟨N0, hN0, h⟩
    · exact ⟨-N0, hN0', by rw [Complex.neg_re, h, neg_neg]⟩
  · rcases P3 N0 hN0 with h | h
    · exact ⟨-N0, hN0', by rw [Complex.neg_re, h, hnm]⟩
    · exact ⟨N0, hN0, by rw [h, hnm]⟩

end Arxiv1007_0377
open Arxiv1007_0377 in
theorem solution (ε μ : ℂ) :
    0 ≤ branchRadicand ε μ ∧
    indexQuartic ε μ =
      (X - C ((nPlus ε μ : ℝ) : ℂ)) * (X - C ((nMinus ε μ : ℝ) : ℂ)) *
        (X - C (((Real.sqrt (‖ε‖ * ‖μ‖ - epsMuRe ε μ) / Real.sqrt 2 : ℝ) : ℂ) * I)) *
        (X + C (((Real.sqrt (‖ε‖ * ‖μ‖ - epsMuRe ε μ) / Real.sqrt 2 : ℝ) : ℂ) * I)) ∧
    (∀ N : ℂ, N ^ 2 = ε * μ → N.re = nPlus ε μ ∨ N.re = nMinus ε μ) ∧
    (∃ N : ℂ, N ^ 2 = ε * μ ∧ N.re = nPlus ε μ) ∧
    (∃ N : ℂ, N ^ 2 = ε * μ ∧ N.re = nMinus ε μ) :=
  real_branches_formula ε μ
