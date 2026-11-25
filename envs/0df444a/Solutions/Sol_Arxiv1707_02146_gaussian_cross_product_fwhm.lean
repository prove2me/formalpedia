-- Prove2me | solution 1 for Arxiv1707_02146.gaussian_cross_product_fwhm
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T19:38:55.447034+00:00
-- url     : https://prove2.me/submissions/f509702d-5ce8-45ef-8bff-e1b79bd2ca8b

import Mathlib
import Definitions.Def_Arxiv1707_02146_Basic

open Matrix ComplexConjugate
open Arxiv1707_02146

theorem solution (f g : ℝ → ℝ) (l0 w : ℝ)
    (hf : IsGaussianFWHM f l0 w) (hg : IsGaussianFWHM g l0 w) :
    IsGaussianFWHM (fun lam => f lam * g lam) l0 (w / Real.sqrt 2) ∧
    (∀ lam : ℝ, f lam * g lam ≤ f l0 * g l0) ∧
    {lam : ℝ | f l0 * g l0 / 2 ≤ f lam * g lam} =
      Set.Icc (l0 - w / Real.sqrt 2 / 2) (l0 + w / Real.sqrt 2 / 2) ∧
    w / Real.sqrt 2 < w := by
  obtain ⟨hw, A, hA, rfl⟩ := hf
  obtain ⟨-, B, hB, rfl⟩ := hg
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have prod : ∀ lam, gaussianProfile A l0 w lam * gaussianProfile B l0 w lam =
      A * B * Real.exp (-(4 * Real.log 2) * (lam - l0) ^ 2 / (w / Real.sqrt 2) ^ 2) := by
    intro lam
    simp only [gaussianProfile]
    rw [show A * Real.exp (-(4 * Real.log 2) * (lam - l0) ^ 2 / w ^ 2) *
        (B * Real.exp (-(4 * Real.log 2) * (lam - l0) ^ 2 / w ^ 2)) =
        A * B * (Real.exp (-(4 * Real.log 2) * (lam - l0) ^ 2 / w ^ 2) *
        Real.exp (-(4 * Real.log 2) * (lam - l0) ^ 2 / w ^ 2)) by ring, ← Real.exp_add]
    congr 2
    rw [div_pow, hsq]; field_simp; ring
  have at0 : gaussianProfile A l0 w l0 * gaussianProfile B l0 w l0 = A * B := by
    simp [gaussianProfile]
  refine ⟨⟨by positivity, A * B, by positivity, ?_⟩, ?_, ?_, ?_⟩
  · funext lam; rw [prod]; simp [gaussianProfile]
  · intro lam
    rw [prod, at0]
    have : Real.exp (-(4 * Real.log 2) * (lam - l0) ^ 2 / (w / Real.sqrt 2) ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      have := sq_nonneg (lam - l0); nlinarith
    have hAB : 0 < A * B := by positivity
    nlinarith
  · ext lam
    simp only [Set.mem_ofPred_eq, Set.mem_Icc]
    rw [at0, prod]
    have hAB : 0 < A * B := by positivity
    have hw2 : (w / Real.sqrt 2) ^ 2 = w ^ 2 / 2 := by rw [div_pow, hsq]
    rw [hw2]
    constructor
    · intro h
      have h' : 1 / 2 ≤ Real.exp (-(4 * Real.log 2) * (lam - l0) ^ 2 / (w ^ 2 / 2)) := by
        by_contra hc; push_neg at hc; nlinarith
      have h'' := Real.log_le_log (by norm_num) h'
      rw [Real.log_exp, one_div, Real.log_inv] at h''
      rw [le_div_iff₀ (by positivity)] at h''
      have hd : (lam - l0) ^ 2 ≤ (w / Real.sqrt 2 / 2) ^ 2 := by
        rw [div_pow, div_pow, hsq]; nlinarith
      have hpos : 0 ≤ w / Real.sqrt 2 / 2 := by positivity
      have := abs_le_of_sq_le_sq' hd hpos
      constructor <;> linarith [this.1, this.2]
    · rintro ⟨h1, h2⟩
      have hd : (lam - l0) ^ 2 ≤ (w / Real.sqrt 2 / 2) ^ 2 := by
        apply sq_le_sq'  <;> linarith
      rw [div_pow, div_pow, hsq] at hd
      have hexp : 1 / 2 ≤ Real.exp (-(4 * Real.log 2) * (lam - l0) ^ 2 / (w ^ 2 / 2)) := by
        rw [show (1 / 2 : ℝ) = Real.exp (-Real.log 2) by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num]
        apply Real.exp_le_exp.mpr
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      nlinarith
  · rw [div_lt_iff₀ hs2]
    have : 1 < Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    nlinarith

