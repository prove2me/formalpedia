-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.poisson_subgraph_intensity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:52:12.461202+00:00
-- url     : https://prove2.me/submissions/b996064f-731a-4857-8d53-1e4ebfde0cac

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false
theorem solution
    (T M : ℝ) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (φ : ℝ -> ℝ) (hφ : Continuous φ)
    (hφ0 : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ φ t)
    (hφM : ∀ t ∈ Set.Icc (0 : ℝ) T, φ t ≤ M) :
    let A : Set (ℝ × ℝ) :=
      {z | z.1 ∈ Set.Icc (0 : ℝ) T ∧ z.2 ∈ Set.Icc 0 (φ z.1)}
    ((volume : Measure (ℝ × ℝ)).restrict
      (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) M)) A =
      ENNReal.ofReal (∫ t in (0 : ℝ)..T, φ t) := by
  let A : Set (ℝ × ℝ) :=
    {z | z.1 ∈ Set.Icc (0 : ℝ) T ∧ z.2 ∈ Set.Icc 0 (φ z.1)}
  have hA : MeasurableSet A := by
    dsimp only [A]
    exact (measurableSet_Icc.preimage measurable_fst).inter
      ((measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd
          (hφ.measurable.comp measurable_fst)))
  have hsub : A ⊆ Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) M := by
    rintro ⟨t, u⟩ ⟨ht, hu⟩
    exact ⟨ht, ⟨hu.1, le_trans hu.2 (hφM t ht)⟩⟩
  have heval (t : ℝ) :
      (volume : Measure ℝ) ((Prod.mk t) ⁻¹' A) =
      (Set.Icc (0 : ℝ) T).indicator
        (fun v => ENNReal.ofReal (φ v)) t := by
    by_cases ht : t ∈ Set.Icc (0 : ℝ) T
    · have hs : (Prod.mk t) ⁻¹' A = Set.Icc 0 (φ t) := by
        ext u
        change (t ∈ Set.Icc (0 : ℝ) T ∧ u ∈ Set.Icc 0 (φ t)) ↔
          u ∈ Set.Icc 0 (φ t)
        simp only [ht, true_and]
      rw [hs, Real.volume_Icc]
      simp [Set.indicator_of_mem ht]
    · have hs : (Prod.mk t) ⁻¹' A = (∅ : Set ℝ) := by
        ext u
        change (t ∈ Set.Icc (0 : ℝ) T ∧ u ∈ Set.Icc 0 (φ t)) ↔ False
        simp only [ht, false_and, iff_self]
      rw [hs, measure_empty]
      simp [Set.indicator_of_notMem ht]
  have hmass : (volume : Measure (ℝ × ℝ)) A =
      ∫⁻ t in Set.Icc (0 : ℝ) T,
        ENNReal.ofReal (φ t) ∂ (volume : Measure ℝ) := by
    rw [Measure.volume_eq_prod ℝ ℝ]
    rw [Measure.prod_apply hA]
    simp_rw [heval]
    rw [lintegral_indicator measurableSet_Icc]
  have hint : IntegrableOn φ (Set.Icc (0 : ℝ) T) :=
    hφ.integrableOn_Icc
  have hae : ∀ᵐ t ∂
      (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) T),
      0 ≤ φ t :=
    (ae_restrict_iff' measurableSet_Icc).mpr
      (Filter.Eventually.of_forall hφ0)
  have hreal :
      ENNReal.ofReal (∫ t in Set.Icc (0 : ℝ) T,
        φ t ∂ (volume : Measure ℝ)) =
      ∫⁻ t in Set.Icc (0 : ℝ) T,
        ENNReal.ofReal (φ t) ∂ (volume : Measure ℝ) :=
    ofReal_integral_eq_lintegral_ofReal hint hae
  have hinterval :
      (∫ t in (0 : ℝ)..T, φ t) =
      (∫ t in Set.Icc (0 : ℝ) T, φ t) := by
    rw [intervalIntegral.integral_of_le hT]
    exact (integral_Icc_eq_integral_Ioc).symm
  change ((volume : Measure (ℝ × ℝ)).restrict
    (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) M)) A =
    ENNReal.ofReal (∫ t in (0 : ℝ)..T, φ t)
  rw [Measure.restrict_apply hA, Set.inter_eq_left.mpr hsub, hmass]
  rw [← hreal, hinterval]
