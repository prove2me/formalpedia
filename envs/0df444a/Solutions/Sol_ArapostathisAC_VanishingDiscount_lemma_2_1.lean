-- Prove2me | solution 1 for ArapostathisAC.VanishingDiscount.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T04:22:59.641418+00:00
-- url     : https://prove2.me/submissions/f98e6685-cab8-4bc6-bbfb-010e0cc9a66f

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_DPMaps

set_option autoImplicit false

namespace ArapostathisAC.VanishingDiscount.L21Aux

open ArapostathisAC.VanishingDiscount MeasureTheory ProbabilityTheory

theorem prob_nonneg {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (i : ℕ) (a : A) (j : ℕ) : 0 ≤ prob M i a j := ENNReal.toReal_nonneg

theorem prob_tsum_enn {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (i : ℕ) (a : A) : ∑' j, M.P (i, a) {j} = 1 := by
  have h := Measure.tsum_indicator_apply_singleton (M.P (i, a)) Set.univ MeasurableSet.univ
  simp only [Set.indicator_univ, measure_univ] at h
  exact h

theorem prob_summable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (i : ℕ) (a : A) : Summable (fun j => prob M i a j) := by
  unfold prob
  exact ENNReal.summable_toReal (by rw [prob_tsum_enn]; exact ENNReal.one_ne_top)

theorem prob_tsum {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (i : ℕ) (a : A) : ∑' j, prob M i a j = 1 := by
  unfold prob
  rw [← ENNReal.tsum_toReal_eq (fun j => measure_ne_top _ _), prob_tsum_enn]
  simp

theorem tsum_ge {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (v : ℕ → ℝ) (m : ℝ) (hm : ∀ j, m ≤ v j) (i : ℕ) (a : A)
    (hs : Summable (fun j => prob M i a j * v j)) : m ≤ ∑' j, prob M i a j * v j := by
  have h1 : ∑' j, prob M i a j * m = m := by
    rw [tsum_mul_right, prob_tsum, one_mul]
  rw [← h1]
  exact Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (hm j) (prob_nonneg M i a j))
    ((prob_summable M i a).mul_right m) hs

theorem bdd {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (v : ℕ → ℝ) (hv : BddBelow (Set.range v))
    (hsv : ∀ i, ∀ a ∈ M.U i, Summable (fun j => prob M i a j * v j)) (i : ℕ) :
    BddBelow (Set.range (fun a : M.U i => M.c i a + ∑' j, prob M i a j * v j)) := by
  obtain ⟨m, hm⟩ := hv
  have hm' : ∀ j, m ≤ v j := fun j => hm ⟨j, rfl⟩
  refine ⟨m, ?_⟩
  rintro _ ⟨a, rfl⟩
  have h1 := M.c_nonneg i a a.2
  have h2 := tsum_ge M v m hm' i a (hsv i a a.2)
  linarith

theorem ciInf_add_const' {ι : Sort*} [Nonempty ι] (f : ι → ℝ) (hf : BddBelow (Set.range f))
    (k : ℝ) : ⨅ a, (f a + k) = (⨅ a, f a) + k := by
  have hfk : BddBelow (Set.range (fun a => f a + k)) := by
    obtain ⟨m, hm⟩ := hf
    refine ⟨m + k, ?_⟩
    rintro _ ⟨a, rfl⟩
    have := hm ⟨a, rfl⟩
    simp only at this ⊢
    linarith
  apply le_antisymm
  · have : (⨅ a, (f a + k)) - k ≤ ⨅ a, f a := by
      apply le_ciInf
      intro a
      have := ciInf_le hfk a
      linarith
    linarith
  · apply le_ciInf
    intro a
    have := ciInf_le hf a
    linarith

end ArapostathisAC.VanishingDiscount.L21Aux

open ArapostathisAC.VanishingDiscount in
theorem solution {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (v v' : ℕ → ℝ) (hv : BddBelow (Set.range v)) (hv' : BddBelow (Set.range v'))
    (hsv : ∀ i, ∀ a ∈ M.U i, Summable (fun j => prob M i a j * v j))
    (hsv' : ∀ i, ∀ a ∈ M.U i, Summable (fun j => prob M i a j * v' j)) :
    (∀ k : ℝ, bellmanT M (fun j => v j + k) = fun i => bellmanT M v i + k) ∧
    (v ≤ v' → bellmanT M v ≤ bellmanT M v') := by
  constructor
  · intro k
    funext i
    have : Nonempty (M.U i) := (M.U_nonempty i).to_subtype
    unfold bellmanT
    have hpt : ∀ a : M.U i, M.c i a + ∑' j, prob M i a j * (v j + k)
        = (M.c i a + ∑' j, prob M i a j * v j) + k := by
      intro a
      have hs1 := hsv i a a.2
      have hs2 : Summable (fun j => prob M i a j * k) := (L21Aux.prob_summable M i a).mul_right k
      have : (fun j => prob M i a j * (v j + k))
          = fun j => prob M i a j * v j + prob M i a j * k := by
        funext j; ring
      rw [this, hs1.tsum_add hs2, tsum_mul_right, L21Aux.prob_tsum, one_mul]
      ring
    simp_rw [hpt]
    exact L21Aux.ciInf_add_const' _ (L21Aux.bdd M v hv hsv i) k
  · intro hle i
    have : Nonempty (M.U i) := (M.U_nonempty i).to_subtype
    unfold bellmanT
    apply ciInf_mono (L21Aux.bdd M v hv hsv i)
    intro a
    have := Summable.tsum_le_tsum
      (fun j => mul_le_mul_of_nonneg_left (hle j) (L21Aux.prob_nonneg M i a j))
      (hsv i a a.2) (hsv' i a a.2)
    linarith
