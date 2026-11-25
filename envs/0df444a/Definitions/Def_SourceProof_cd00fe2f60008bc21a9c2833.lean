-- Prove2me | Definitions.Def_SourceProof_cd00fe2f60008bc21a9c2833
-- name    : SourceProof_cd00fe2f60008bc21a9c2833
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:36.590805+00:00
-- url     : https://prove2.me/theorems/90ef7f79-4c62-4604-bfc6-6216c722a035
-- title:
--   StochLean source theorem: ProbabilityTheory.tendstoUCP_of_uniform_approximation

import Definitions.Def_SourceProof_8a6833f86adf7b2b1ff4dc1a
import Definitions.Def_SourceProof_c85f5070e7769bac711d7f66

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # UCP limits through uniformly controlled approximations

Sequential control for every choice of a column gives a uniform probability
bound over all columns. This permits a double-limit argument without assuming
uniform rates of convergence for the individual rows. No measurability or
finiteness hypothesis on the measure is needed for these outer-measure bounds.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem _root_.Prove2MeSourceProof.h_cd00fe2f60008bc21a9c2833
    {A : ℕ → ℕ → ℝ≥0 → Ω → ℝ} {B C : ℕ → ℝ≥0 → Ω → ℝ}
    {D : ℝ≥0 → Ω → ℝ}
    (hA : ∀ k, TendstoUCP P (A k) atTop (C k))
    (hC : TendstoUCP P C atTop D)
    (hE : ∀ n : ℕ → ℕ,
      TendstoUCP P (fun k ↦ A k (n k) - B (n k)) atTop 0) :
    TendstoUCP P B atTop D := by
  apply _root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mpr
  intro T ε hε
  apply ENNReal.tendsto_atTop_zero.mpr
  intro η hη
  have hε2 : 0 < ε / 2 := half_pos hε
  have hε4 : 0 < ε / 2 / 2 := half_pos hε2
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  have hη4 : 0 < η / 2 / 2 := ENNReal.half_pos hη2.ne'
  obtain ⟨KE, hKE⟩ := eventually_atTop.mp
    (_root_.Prove2MeSourceProof.h_8a6833f86adf7b2b1ff4dc1a
      (E := fun k n t ω ↦ A k n t ω - B n t ω) hE T hε2 hη2)
  obtain ⟨KC, hKC⟩ := ENNReal.tendsto_atTop_zero.mp
    (_root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mp hC T (ε / 2 / 2) hε4)
    (η / 2 / 2) hη4
  let k := max KE KC
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp
    (_root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mp (hA k) T (ε / 2 / 2) hε4)
    (η / 2 / 2) hη4
  refine ⟨N, fun n hn ↦ ?_⟩
  let E₁ := {ω | ∃ t ≤ T, ε / 2 < ‖A k n t ω - B n t ω‖}
  let E₂ := {ω | ∃ t ≤ T, ε / 2 / 2 < ‖A k n t ω - C k t ω‖}
  let E₃ := {ω | ∃ t ≤ T, ε / 2 / 2 < ‖C k t ω - D t ω‖}
  have hsub : {ω | ∃ t ≤ T, ε < ‖B n t ω - D t ω‖} ⊆ E₁ ∪ (E₂ ∪ E₃) := by
    rintro ω ⟨t, ht, hω⟩
    by_contra h
    have h₁ : ‖A k n t ω - B n t ω‖ ≤ ε / 2 := by
      by_contra h'
      exact h (Or.inl ⟨t, ht, lt_of_not_ge h'⟩)
    have h₂ : ‖A k n t ω - C k t ω‖ ≤ ε / 2 / 2 := by
      by_contra h'
      exact h (Or.inr (Or.inl ⟨t, ht, lt_of_not_ge h'⟩))
    have h₃ : ‖C k t ω - D t ω‖ ≤ ε / 2 / 2 := by
      by_contra h'
      exact h (Or.inr (Or.inr ⟨t, ht, lt_of_not_ge h'⟩))
    have heq : B n t ω - D t ω =
        -(A k n t ω - B n t ω) +
          ((A k n t ω - C k t ω) + (C k t ω - D t ω)) := by ring
    have hb := norm_add_le (-(A k n t ω - B n t ω))
      ((A k n t ω - C k t ω) + (C k t ω - D t ω))
    have hc := norm_add_le (A k n t ω - C k t ω) (C k t ω - D t ω)
    rw [← heq, norm_neg] at hb
    linarith only [hω, h₁, h₂, h₃, hb, hc]
  calc
    P {ω | ∃ t ≤ T, ε < ‖B n t ω - D t ω‖}
        ≤ P E₁ + (P E₂ + P E₃) :=
      (measure_mono hsub).trans ((measure_union_le _ _).trans
        (add_le_add le_rfl (measure_union_le _ _)))
    _ ≤ η / 2 + (η / 2 / 2 + η / 2 / 2) := by
      exact add_le_add (hKE k (le_max_left _ _) n)
        (add_le_add (hN n hn) (hKC k (le_max_right _ _)))
    _ = η := by rw [ENNReal.add_halves, ENNReal.add_halves]
end ProbabilityTheory


