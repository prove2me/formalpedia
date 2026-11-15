-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.poisson_void_probability_subgraph
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:06:56.847285+00:00
-- url     : https://prove2.me/submissions/7aee66ae-850d-4646-8bf3-e443f689d203

import Mathlib
import Theorems.Thm_ProbabilityTheory_map_poissonRandomMeasure_apply
import Theorems.Thm_AppliedSDE_SarkkaSolin_poisson_subgraph_intensity
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → (ℝ × ℝ)}
    (T M : ℝ) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (φ : ℝ → ℝ) (hφ : Continuous φ)
    (hφ0 : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ φ t)
    (hφM : ∀ t ∈ Set.Icc (0 : ℝ) T, φ t ≤ M)
    (hPPP : IsPoissonPointFamily K X
      ((volume : Measure (ℝ × ℝ)).restrict
        (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) M)) P) :
    let A : Set (ℝ × ℝ) :=
      {z | z.1 ∈ Set.Icc (0 : ℝ) T ∧ z.2 ∈ Set.Icc (0 : ℝ) (φ z.1)}
    P.real {ω | ProbabilityTheory.poissonRandomMeasure K X ω A = 0} =
      Real.exp (-(∫ t in (0 : ℝ)..T, φ t)) := by
  let m : Measure (ℝ × ℝ) :=
    (volume : Measure (ℝ × ℝ)).restrict
      (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) M)
  let A : Set (ℝ × ℝ) :=
    {z | z.1 ∈ Set.Icc (0 : ℝ) T ∧ z.2 ∈ Set.Icc (0 : ℝ) (φ z.1)}
  have hA : MeasurableSet A := by
    dsimp only [A]
    exact (measurableSet_Icc.preimage measurable_fst).inter
      ((measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd
          (hφ.measurable.comp measurable_fst)))
  have hmass : m A =
      ENNReal.ofReal (∫ t in (0 : ℝ)..T, φ t) := by
    simpa only [m, A] using
      (AppliedSDE.SarkkaSolin.poisson_subgraph_intensity
        T M hT hM φ hφ hφ0 hφM)
  have hfinite : m A < ⊤ := by
    rw [hmass]
    exact ENNReal.ofReal_lt_top
  have hmap :
      P.map (fun omega => poissonRandomMeasure K X omega A) =
        (poissonMeasure (m A).toNNReal).map
          (Nat.cast : ℕ -> ℝ≥0∞) := by
    exact ProbabilityTheory.map_poissonRandomMeasure_apply
      (m := m) hPPP hA hfinite
  have hmea :
      Measurable (fun omega => poissonRandomMeasure K X omega A) :=
    ProbabilityTheory.measurable_poissonRandomMeasure_apply
      hPPP.measurable_count hPPP.measurable_point hA
  have hzero :
      P {omega | poissonRandomMeasure K X omega A = 0} =
        poissonMeasure (m A).toNNReal ({0} : Set ℕ) := by
    have heq : (fun n : ℕ => (n : ℝ≥0∞)) ⁻¹' ({0} : Set ℝ≥0∞) =
          ({0} : Set ℕ) := by
      ext n
      simp
    calc
      P {omega | poissonRandomMeasure K X omega A = 0} =
          (P.map (fun omega => poissonRandomMeasure K X omega A))
            ({0} : Set ℝ≥0∞) := by
        simpa only [Set.preimage, Set.mem_singleton_iff]
          using (Measure.map_apply hmea (measurableSet_singleton (0 : ENNReal))).symm
      _ = ((poissonMeasure (m A).toNNReal).map
            (Nat.cast : ℕ -> ℝ≥0∞)) ({0} : Set ℝ≥0∞) := by rw [hmap]
      _ = poissonMeasure (m A).toNNReal ({0} : Set ℕ) := by
        rw [Measure.map_apply measurable_from_top (measurableSet_singleton (0 : ENNReal)), heq]
  have hnonneg : 0 ≤ (∫ t in (0 : ℝ)..T, φ t) := by
    apply intervalIntegral.integral_nonneg hT
    intro t ht
    exact hφ0 t ht
  change P.real {omega | poissonRandomMeasure K X omega A = 0} =
    Real.exp (-(∫ t in (0 : ℝ)..T, φ t))
  rw [Measure.real_def, hzero, ← Measure.real_def,
    poissonMeasure_real_singleton]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
  rw [hmass]
  simp [ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_ofReal hnonneg]
