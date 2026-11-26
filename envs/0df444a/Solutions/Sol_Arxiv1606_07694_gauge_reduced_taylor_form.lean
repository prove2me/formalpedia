-- Prove2me | solution 1 for Arxiv1606_07694.gauge_reduced_taylor_form
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T03:10:01.225895+00:00
-- url     : https://prove2.me/submissions/a44b8f33-ec37-4fe7-9d48-9394d49eceac

import Mathlib
import Definitions.Def_Arxiv1606_07694_Basic

set_option autoImplicit false

open MeasureTheory Complex Filter Topology Asymptotics

namespace S76GT
open Arxiv1606_07694

lemma split_one {n : ℕ} (f : Fin n → ℂ) (i : Fin n) :
    ∑ j, f j = f i + ∑ j ∈ Finset.Ioi i, f j + ∑ j ∈ Finset.Iio i, f j := by
  have hu : (Finset.univ : Finset (Fin n)) = insert i (Finset.Ioi i ∪ Finset.Iio i) := by
    ext j; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, Finset.mem_Ioi,
      Finset.mem_Iio, true_iff]
    rcases lt_trichotomy j i with h | h | h
    · right; right; exact h
    · left; exact h
    · right; left; exact h
  rw [hu, Finset.sum_insert, Finset.sum_union, add_assoc]
  · rw [Finset.disjoint_left]; intro j h1 h2
    simp only [Finset.mem_Ioi, Finset.mem_Iio] at h1 h2; exact absurd (h1.trans h2) (lt_irrefl _)
  · simp only [Finset.mem_union, Finset.mem_Ioi, Finset.mem_Iio, lt_irrefl, or_self,
      not_false_eq_true]

lemma split {n : ℕ} (x y : Fin n → ℂ) :
    (∑ i, x i) * (∑ j, y j) = ∑ i, x i * y i + ∑ i, ∑ j ∈ Finset.Ioi i, x i * y j +
      ∑ i, ∑ j ∈ Finset.Ioi i, y i * x j := by
  rw [Finset.sum_mul_sum]
  have h : ∀ i, ∑ j, x i * y j = x i * y i + ∑ j ∈ Finset.Ioi i, x i * y j +
      ∑ j ∈ Finset.Iio i, x i * y j := fun i => split_one (fun j => x i * y j) i
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun j => Finset.Ioi j)]
  · apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  · intro a b; simp

noncomputable def T {n : ℕ} (κ : Fin n → Vec2) (μ ν : Fin 2) : ℂ :=
  ∑ i, ∑ j ∈ Finset.Ioi i, (κ i μ : ℂ) * (κ j ν : ℂ)

lemma cross_eq {n : ℕ} (Dm : Matrix (Fin 2) (Fin 2) ℂ) (κ : Fin n → Vec2) :
    crossSum Dm κ = ∑ μ, ∑ ν, Dm μ ν * T κ μ ν := by
  unfold crossSum T
  simp only [Finset.mul_sum, Fin.sum_univ_two]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

end S76GT

open Arxiv1606_07694 S76GT in
theorem solution {n : ℕ} (k k0 : Vec2) (g : (Fin n → Vec2) → ℂ)
    (hg : ∀ (κ : Fin n → Vec2) (σ : Equiv.Perm (Fin n)), g (κ ∘ σ) = g κ)
    (a : ℂ) (b : Fin 2 → ℂ) (C Dm : Matrix (Fin 2) (Fin 2) ℂ)
    (h16 : HasSecondOrderExpansion g a b C Dm) :
    ∃ (Ahat : Fin 2 → ℂ) (Bhat : Matrix (Fin 2) (Fin 2) ℂ),
      (∀ κ : Fin n → Vec2, OnHyperplane k k0 κ → gaugeTerm k k0 Ahat Bhat κ = 0) ∧
      ∃ (a' : ℂ) (Dm' : Matrix (Fin 2) (Fin 2) ℂ),
        HasReducedExpansion (fun κ => g κ + gaugeTerm k k0 Ahat Bhat κ) a' Dm' := by
  set d : Fin 2 → ℂ := fun μ => (((k0 - k) μ : ℝ) : ℂ) with hd
  refine ⟨fun μ => -b μ + ∑ ν, d ν * C ν μ, -C, ?_, a + ∑ μ, d μ * (-b μ + ∑ ν, d ν * C ν μ),
    Dm + C + C.transpose, ?_⟩
  · intro κ hκ
    unfold gaugeTerm
    unfold OnHyperplane at hκ
    simp [hκ]
  · unfold HasReducedExpansion
    refine h16.congr' (Eventually.of_forall fun κ => ?_) (EventuallyEq.refl _ _)
    simp only
    unfold gaugeTerm truncPoly
    rw [cross_eq, cross_eq]
    have hS : ∀ μ, (((∑ i, κ i) μ : ℝ) : ℂ) = ∑ i, ((κ i μ : ℝ) : ℂ) := by
      intro μ; simp [WithLp.ofLp_sum]
    have hS2 : ∀ μ, (((∑ i, κ i + k0 - k) μ : ℝ) : ℂ) = ∑ i, ((κ i μ : ℝ) : ℂ) + d μ := by
      intro μ; simp [hd, WithLp.ofLp_sum]; ring
    simp only [hS, hS2]
    have sp := fun μ ν => split (fun i => ((κ i μ : ℝ) : ℂ)) (fun i => ((κ i ν : ℝ) : ℂ))
    have e00 := sp 0 0
    have e01 := sp 0 1
    have e10 := sp 1 0
    have e11 := sp 1 1
    simp only [Fin.sum_univ_two, Matrix.add_apply, Matrix.transpose_apply, Matrix.neg_apply] at *
    unfold T
    linear_combination (C 0 0) * e00 + C 0 1 * e01 + C 1 0 * e10 + C 1 1 * e11
