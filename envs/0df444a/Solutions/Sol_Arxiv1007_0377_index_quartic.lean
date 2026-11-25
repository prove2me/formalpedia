-- Prove2me | solution 1 for Arxiv1007_0377.index_quartic
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T14:48:19.6728+00:00
-- url     : https://prove2.me/submissions/1d06e3ce-bef0-48b1-a1b5-d5706c4fd04d

import Mathlib
import Definitions.Def_Arxiv1007_0377_Basic

open Complex Polynomial

namespace Arxiv1007_0377

theorem index_quartic (ε μ : ℂ) :
    (∀ n κ : ℝ, ((n : ℂ) + κ * I) ^ 2 = ε * μ →
      (indexQuartic ε μ).eval (n : ℂ) = 0 ∧
      κ ^ 4 + epsMuRe ε μ * κ ^ 2 - (epsMuIm ε μ / 2) ^ 2 = 0) ∧
    ∃ a b : ℝ, indexQuartic ε μ =
      (X - C (a : ℂ)) * (X + C (a : ℂ)) * (X - C ((b : ℂ) * I)) * (X + C ((b : ℂ) * I)) := by
  set p := epsMuRe ε μ with hp
  set c := (epsMuIm ε μ / 2) ^ 2 with hc
  constructor
  · intro n κ h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at hre him
    have hr : n * n - κ * κ = p := by rw [hp, epsMuRe]; linarith
    have hi : 2 * n * κ = epsMuIm ε μ := by rw [epsMuIm]; linarith
    have hc' : c = (n * κ) ^ 2 := by rw [hc, ← hi]; ring
    refine ⟨?_, ?_⟩
    · unfold indexQuartic
      rw [← hp, ← hc]
      simp only [eval_sub, eval_pow, eval_X, eval_C, eval_mul]
      rw [hc', ← hr]
      push_cast
      ring
    · rw [hc', ← hr]; ring
  · have hc0 : 0 ≤ c := sq_nonneg _
    set s := Real.sqrt (p ^ 2 + 4 * c) with hs
    have hs2 : s ^ 2 = p ^ 2 + 4 * c := Real.sq_sqrt (by positivity)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hsp : |p| ≤ s := by
      rw [hs]; exact Real.abs_le_sqrt (by nlinarith)
    have hA0 : 0 ≤ (p + s) / 2 := by have := neg_abs_le p; linarith
    have hB0 : 0 ≤ (s - p) / 2 := by have := le_abs_self p; linarith
    refine ⟨Real.sqrt ((p + s) / 2), Real.sqrt ((s - p) / 2), ?_⟩
    have h1 : C ((Real.sqrt ((p + s) / 2) : ℝ) : ℂ) ^ 2 = C ((((p + s) / 2 : ℝ)) : ℂ) := by
      rw [← map_pow, ← Complex.ofReal_pow, Real.sq_sqrt hA0]
    have h2 : C (((Real.sqrt ((s - p) / 2) : ℝ) : ℂ) * I) ^ 2 = -C ((((s - p) / 2 : ℝ)) : ℂ) := by
      rw [← map_pow, mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt hB0, I_sq, ← map_neg]; ring_nf
    have h3 : C ((((p + s) / 2 : ℝ)) : ℂ) - C ((((s - p) / 2 : ℝ)) : ℂ) = C ((p : ℝ) : ℂ) := by
      rw [← map_sub]; congr 1; push_cast; ring
    have h4 : C ((((p + s) / 2 : ℝ)) : ℂ) * C ((((s - p) / 2 : ℝ)) : ℂ) = C ((c : ℝ) : ℂ) := by
      rw [← map_mul]; congr 1; rw [← Complex.ofReal_mul]; congr 1; nlinarith
    unfold indexQuartic
    rw [← hp, ← hc]
    linear_combination (X ^ 2 - C (((Real.sqrt ((s - p) / 2) : ℝ) : ℂ) * I) ^ 2) * h1 +
      (X ^ 2 - C ((((p + s) / 2 : ℝ)) : ℂ)) * h2 + X ^ 2 * h3 + h4

end Arxiv1007_0377
open Arxiv1007_0377 in
theorem solution (ε μ : ℂ) :
    (∀ n κ : ℝ, ((n : ℂ) + κ * I) ^ 2 = ε * μ →
      (indexQuartic ε μ).eval (n : ℂ) = 0 ∧
      κ ^ 4 + epsMuRe ε μ * κ ^ 2 - (epsMuIm ε μ / 2) ^ 2 = 0) ∧
    ∃ a b : ℝ, indexQuartic ε μ =
      (X - C (a : ℂ)) * (X + C (a : ℂ)) * (X - C ((b : ℂ) * I)) * (X + C ((b : ℂ) * I)) :=
  index_quartic ε μ
