-- Prove2me | Definitions.Def_SourceProof_4f6673f9096f52fcbaa7b357
-- name    : SourceProof_4f6673f9096f52fcbaa7b357
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:27:13.78319+00:00
-- url     : https://prove2.me/theorems/b911abef-f489-42a2-92e3-da2461bb89c3
-- title:
--   LevyStochCalc source module: SourceProof_4f6673f9096f52fcbaa7b357
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.markStepIntegral_diff_isometry` comes from the `LevyStochCalc.Poisson.CompensatedDensityRefinement` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRefinement_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Doob `L²` bricks and dyadic cross-resolution refinement

Two preparations for the passage to the limit: the submartingale property of `‖M‖` and the
discrete tail maximal inequality for a martingale, and the re-expression of a dyadic step
integrand at level `n` on a finer dyadic level `m ≥ n`. The refinement keeps the integrand
adapted and its compensated integral unchanged, so integrands of different resolutions can be
compared on a common grid.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Doob `L²` machinery (toward the càdlàg conjunct of #6)

Mathlib has only the discrete *tail* maximal inequality (`maximal_ineq`), the
layer-cake formula, and conditional Jensen. The continuous-time Doob `L²` maximal
inequality and the càdlàg regularization are built here from those pieces. -/


theorem _root_.Prove2MeSourceProof.h_4f6673f9096f52fcbaa7b357
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ) {N₀ : ℕ} (p : Fin (N₀ +
      1) → ℝ)
    (hp0 : p 0 = 0) (hpmono : StrictMono p) {T : ℝ} (hpleT : p (Fin.last N₀) ≤ T)
    {Ki1 Ki2 : Fin N₀ → ℕ} (Bi1 : ∀ i, Fin (Ki1 i) → Set E) (Bi2 : ∀ i, Fin (Ki2 i) → Set E)
    (ci1 : ∀ i, Fin (Ki1 i) → Ω → ℝ) (ci2 : ∀ i, Fin (Ki2 i) → Ω → ℝ)
    (hBi1m : ∀ i k, MeasurableSet (Bi1 i k)) (hBi2m : ∀ i k, MeasurableSet (Bi2 i k))
    (hBi1f : ∀ i k, ν (Bi1 i k) ≠ ⊤) (hBi2f : ∀ i k, ν (Bi2 i k) ≠ ⊤)
    (hci1b : ∀ i k, ∃ M, ∀ ω, |ci1 i k ω| ≤ M) (hci2b : ∀ i k, ∃ M, ∀ ω, |ci2 i k ω| ≤ M)
    (hci1m : ∀ i k, Measurable (ci1 i k)) (hci2m : ∀ i k, Measurable (ci2 i k))
    (hci1a : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc)) (ci1 i k))
    (hci2a : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc)) (ci2 i k)) :
    ∫ ω, ((∑ i : Fin N₀, ∑ k₀, ci1 i k₀ ω
          * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ Bi1 i k₀) ω)
        - ∑ i : Fin N₀, ∑ k₀, ci2 i k₀ ω
          * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ Bi2 i k₀) ω) ^ 2 ∂P
      = ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) T,
        ((∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
            * ∑ k₀, ci1 i k₀ ω * (Bi1 i k₀).indicator (fun _ => (1 : ℝ)) e)
          - ∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
            * ∑ k₀, ci2 i k₀ ω * (Bi2 i k₀).indicator (fun _ => (1 : ℝ)) e) ^ 2
        ∂volume ∂ν) ∂P := by
  classical
  set BiC : ∀ i, Fin (Ki1 i + Ki2 i) → Set E := fun i => Fin.append (Bi1 i) (Bi2 i) with hBiC
  set ciC : ∀ i, Fin (Ki1 i + Ki2 i) → Ω → ℝ :=
    fun i => Fin.append (ci1 i) (fun k ω => -(ci2 i k ω)) with hciC
  have hBiCm : ∀ i k, MeasurableSet (BiC i k) := fun i =>
    Fin.addCases (fun k => by simp only [hBiC, Fin.append_left]; exact hBi1m i k)
      (fun k => by simp only [hBiC, Fin.append_right]; exact hBi2m i k)
  have hBiCf : ∀ i k, ν (BiC i k) ≠ ⊤ := fun i =>
    Fin.addCases (fun k => by simp only [hBiC, Fin.append_left]; exact hBi1f i k)
      (fun k => by simp only [hBiC, Fin.append_right]; exact hBi2f i k)
  have hciCb : ∀ i k, ∃ M, ∀ ω, |ciC i k ω| ≤ M := fun i =>
    Fin.addCases (fun k => by
        simp only [hciC, Fin.append_left]; exact hci1b i k)
      (fun k => by
        simp only [hciC, Fin.append_right]
        obtain ⟨M, hM⟩ := hci2b i k; exact ⟨M, fun ω => by rw [abs_neg]; exact hM ω⟩)
  have hciCm : ∀ i k, Measurable (ciC i k) := fun i =>
    Fin.addCases (fun k => by simp only [hciC, Fin.append_left]; exact hci1m i k)
      (fun k => by simp only [hciC, Fin.append_right]; exact (hci2m i k).neg)
  have hciCa : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc)) (ciC i k) := fun i =>
    Fin.addCases (fun k => by simp only [hciC, Fin.append_left]; exact hci1a i k)
      (fun k => by simp only [hciC, Fin.append_right]; exact (hci2a i k).neg)
  have key := LevyStochCalc.Poisson.Compensated.markStepIntegral_isometry N ℱ hℱ p hp0 hpmono hpleT BiC ciC hBiCm hBiCf hciCb hciCm
    hciCa
  have hI : ∀ ω, (∑ i : Fin N₀, ∑ k, ciC i k ω
        * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ BiC i k) ω)
      = (∑ i : Fin N₀, ∑ k₀, ci1 i k₀ ω
          * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ Bi1 i k₀) ω)
        - ∑ i : Fin N₀, ∑ k₀, ci2 i k₀ ω
          * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ Bi2 i k₀) ω := by
    intro ω
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fin.sum_univ_add]
    simp only [hBiC, hciC, Fin.append_left, Fin.append_right, neg_mul, Finset.sum_neg_distrib]
    ring
  have hev : ∀ ω e s, (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator
        (fun _ => (1 : ℝ)) s * ∑ k, ciC i k ω * (BiC i k).indicator (fun _ => (1 : ℝ)) e)
      = (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * ∑ k₀, ci1 i k₀ ω * (Bi1 i k₀).indicator (fun _ => (1 : ℝ)) e)
        - ∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * ∑ k₀, ci2 i k₀ ω * (Bi2 i k₀).indicator (fun _ => (1 : ℝ)) e := by
    intro ω e s
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fin.sum_univ_add]
    simp only [hBiC, hciC, Fin.append_left, Fin.append_right, neg_mul, Finset.sum_neg_distrib]
    ring
  simp only [hI, hev] at key
  exact key
/-! ### Cross-resolution refinement (toward the `L²(P)` Cauchy property)

To compare the step integrals of two density approximants at *different* dyadic
levels, both are re-expressed on the common (finer) dyadic refinement. The basic
brick is additivity of the compensated integral over a split time-interval. -/

end LevyStochCalc.Poisson.Compensated


