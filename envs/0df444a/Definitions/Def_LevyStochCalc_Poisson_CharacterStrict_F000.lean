-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CharacterStrict_F000
-- name    : LevyStochCalc_Poisson_CharacterStrict_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:51:03.478987+00:00
-- url     : https://prove2.me/theorems/62af93bb-138b-4be1-a84a-7b21961bfc73
-- title:
--   Source declarations: LevyStochCalc.Poisson.CharacterStrict
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CharacterStrict. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterCompensator_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The character at a time and the character strictly before it agree almost surely

A Poisson random measure has no point on a fixed time slice, so the counts up to `s` and strictly
before `s` agree almost surely; hence the character at `s` equals the character of the strict
past, which is what the chain rule's predictable integrand exponentiates.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section Slice

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- A fixed time slice carries no reference intensity. -/
theorem referenceIntensity_inter_singleton {B : Set (ℝ × E)} (hB : MeasurableSet B) (s : ℝ) :
    referenceIntensity ν (B ∩ {s} ×ˢ Set.univ) = 0 := by
  rw [_root_.Prove2MeSourceProof.h_b53022bf4ec47748c83ffa9f hB (measurableSet_singleton s)]
  exact setLIntegral_measure_zero _ _ Real.volume_singleton
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- A Poisson random measure has no point on a fixed time slice. -/
theorem ae_count_time_singleton_eq_zero (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (s : ℝ) : ∀ᵐ ω ∂P, N.N ω (B ∩ {s} ×ˢ Set.univ) = 0 :=
  ae_count_eq_zero_of_intensity_eq_zero N
    (hB.inter ((measurableSet_singleton s).prod MeasurableSet.univ))
    (referenceIntensity_inter_singleton hB s)
omit [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem inter_Ioc_prod_eq_union {B : Set (ℝ × E)} {s : ℝ} (hs : 0 < s) :
    B ∩ Set.Ioc (0 : ℝ) s ×ˢ Set.univ
      = B ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ ∪ B ∩ {s} ×ˢ Set.univ := by
  ext p
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_prod, Set.mem_Ioc, Set.mem_Ioo,
    Set.mem_singleton_iff, Set.mem_univ, and_true]
  constructor
  · rintro ⟨hB, h0, hle⟩
    rcases hle.lt_or_eq with h | h
    · exact Or.inl ⟨hB, h0, h⟩
    · exact Or.inr ⟨hB, h⟩
  · rintro (⟨hB, h0, h⟩ | ⟨hB, h⟩)
    · exact ⟨hB, h0, h.le⟩
    · exact ⟨hB, h ▸ hs, h.le⟩
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The counts up to `s` and strictly before `s` agree almost surely. -/
theorem ae_count_Ioc_eq_count_Ioo (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ ω ∂P, N.N ω (B ∩ Set.Ioc (0 : ℝ) s ×ˢ Set.univ)
      = N.N ω (B ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ) := by
  filter_upwards [ae_count_time_singleton_eq_zero N hB s] with ω hω
  have hdisj : Disjoint (B ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ) (B ∩ {s} ×ˢ Set.univ) := by
    refine Set.disjoint_left.mpr fun p hp hq => ?_
    exact absurd (Set.mem_singleton_iff.mp hq.2.1) hp.2.1.2.ne
  rw [inter_Ioc_prod_eq_union hs,
    measure_union hdisj (hB.inter ((measurableSet_singleton s).prod MeasurableSet.univ)), hω,
    add_zero]
end Slice

section Strict

/-- The character of the counts strictly before `s`. -/
noncomputable def charStrict (N : PoissonRandomMeasure P ν) (w : ι → ℝ) (Bfam : ι → Set (ℝ × E))
    (s : ℝ) (ω : Ω) : ℂ :=
  Complex.exp (Complex.I *
    ((∑ j, w j * (N.N ω (Bfam j ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ)).toReal : ℝ) : ℂ))
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The character at `s` is almost surely the character of the strict past. -/
theorem ae_charAt_eq_charStrict (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ ω ∂P, charAt N w Bfam s ω = charStrict N w Bfam s ω := by
  have h : ∀ᵐ ω ∂P, ∀ j, N.N ω (Bfam j ∩ Set.Ioc (0 : ℝ) s ×ˢ Set.univ)
      = N.N ω (Bfam j ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ) :=
    ae_all_iff.mpr fun j => ae_count_Ioc_eq_count_Ioo N (hBm j) hs
  filter_upwards [h] with ω hω
  simp only [charAt, charStrict, hω]
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The chain rule's predictable exponential is the strict-past character. -/
theorem exp_predStrict_truncFam (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    (Bfam : ι → Set (ℝ × E)) {A : Set E} {T s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (htT : t ≤ T)
    {e : E} (he : e ∈ A) (ω : Ω) :
    Complex.exp (Complex.I * (predStrict N w (truncFam Bfam t) A T ω s e : ℂ))
      = charStrict N w Bfam s ω := by
  rw [predStrict_truncFam N w Bfam hs hst htT he ω]
  rfl
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- Pairing the weight with the predictable exponential at `(s, e)` is pairing it with the
character at `s`. -/
theorem integral_mul_exp_predStrict (N : PoissonRandomMeasure P ν) {r : Ω → ℝ} (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} {T s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) (htT : t ≤ T) {e : E} (he : e ∈ A) :
    ∫ ω, (r ω : ℂ) * Complex.exp (Complex.I * (predStrict N w (truncFam Bfam t) A T ω s e : ℂ)) ∂P
      = ∫ ω, (r ω : ℂ) * charAt N w Bfam s ω ∂P := by
  simp_rw [exp_predStrict_truncFam N w Bfam hs hst htT he]
  refine integral_congr_ae ?_
  filter_upwards [ae_charAt_eq_charStrict N w hBm hs] with ω hω
  rw [hω]
end Strict

end LevyStochCalc.Poisson


