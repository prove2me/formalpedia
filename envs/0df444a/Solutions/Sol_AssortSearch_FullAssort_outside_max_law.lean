-- Prove2me | solution 1 for AssortSearch.FullAssort.outside_max_law
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T21:55:45.449984+00:00
-- url     : https://prove2.me/submissions/f9f50a00-0c66-4e93-a549-0416aa1c17e9

import Mathlib
import Definitions.Def_AssortSearch_FullAssort_Model

open MeasureTheory ProbabilityTheory Set
open AssortSearch.FullAssort

lemma fullAssortML_term (μ : ℝ) (hμ : 0 < μ) (y ai : ℝ) :
    AssortSearch.Cannibal.lam μ y * Real.exp (ai / μ) =
      Real.exp (-((y - ai) / μ + Real.eulerMascheroniConstant)) := by
  unfold AssortSearch.Cannibal.lam
  rw [← Real.exp_add]; congr 1; field_simp; ring

theorem solution {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : AssortSearch.Cannibal.IsZeroMeanGumbel μ G) (a : Fin n → ℝ) (S : Finset (Fin n))
    (hS : S ≠ Finset.univ) :
    (∀ y : ℝ, (Measure.pi (fun _ : Fin n => G) {ζ | ∀ i ∈ Sᶜ, a i + ζ i ≤ y}).toReal =
        outsideCdf μ (fun i => Real.exp (a i / μ)) S y) ∧
      ∀ y : ℝ, HasDerivAt (outsideCdf μ (fun i => Real.exp (a i / μ)) S)
        (w μ (fun i => Real.exp (a i / μ)) S y) y := by
  constructor
  · intro y
    have hset : {ζ : Fin n → ℝ | ∀ i ∈ Sᶜ, a i + ζ i ≤ y} =
        Set.pi univ (fun i => if i ∈ Sᶜ then Iic (y - a i) else univ) := by
      ext ζ
      simp only [mem_ofPred_eq, Set.mem_pi, mem_univ, true_implies]
      constructor
      · intro h i
        split_ifs with hi
        · simp only [mem_Iic]; have := h i hi; linarith
        · trivial
      · intro h i hi
        have := h i
        rw [if_pos hi] at this
        simp only [mem_Iic] at this; linarith
    rw [hset, Measure.pi_pi, ENNReal.toReal_prod]
    have hterm : ∀ i, (G (if i ∈ Sᶜ then Iic (y - a i) else univ)).toReal =
        if i ∈ Sᶜ then Real.exp (-Real.exp (-((y - a i) / μ + Real.eulerMascheroniConstant)))
        else 1 := by
      intro i
      split_ifs with hi
      · have := hG (y - a i)
        rw [cdf_eq_real] at this
        rw [← measureReal_def, this]; rfl
      · simp
    simp_rw [hterm]
    rw [Finset.prod_ite_mem, Finset.univ_inter, ← Real.exp_sum]
    unfold outsideCdf outsidePref
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fullAssortML_term μ hμ]
  · intro y
    set V := outsidePref (fun i => Real.exp (a i / μ)) S
    have hlam : HasDerivAt (fun y => AssortSearch.Cannibal.lam μ y)
        (AssortSearch.Cannibal.lam μ y * (-(1 / μ))) y := by
      unfold AssortSearch.Cannibal.lam
      have h1 : HasDerivAt (fun y : ℝ => -(y / μ + Real.eulerMascheroniConstant)) (-(1 / μ)) y := by
        have h0 : HasDerivAt (fun x : ℝ => x / μ + Real.eulerMascheroniConstant) (1 / μ) y := by
          simpa using ((hasDerivAt_id y).div_const μ).add_const Real.eulerMascheroniConstant
        exact h0.neg
      exact h1.exp
    have h2 := ((hlam.mul_const V).neg).exp
    convert h2 using 1
    · funext x; simp [outsideCdf, V]
    · simp only [w, outsideCdf, V, Pi.neg_apply]
      field_simp
