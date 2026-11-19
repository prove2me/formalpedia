-- Prove2me | Definitions.Def_BrownianMotion_Auxiliary_MeasureTheory_F001
-- name    : BrownianMotion_Auxiliary_MeasureTheory_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:12:03.66365+00:00
-- url     : https://prove2.me/theorems/e5b3dcb9-9276-4b8e-a162-6e6c15e5cb11
-- title:
--   Source declarations: BrownianMotion.Auxiliary.MeasureTheory
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.Auxiliary.MeasureTheory. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_Algebra_F000
import Definitions.Def_BrownianMotion_Auxiliary_Metric_F000
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.ZeroOne


/-!
# Measure theory lemmas to be upstreamed to Mathlib
-/

@[expose] public section

open MeasureTheory WithLp

open scoped ENNReal NNReal ProbabilityTheory

attribute [fun_prop] aemeasurable_id'

namespace ProbabilityTheory

section iIndepFun

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)}

variable [∀ i, IsProbabilityMeasure (μ i)]

end iIndepFun

section covariance

end covariance

end ProbabilityTheory

--generalizing `MeasureTheory.Measure.addHaar_ball_center`

open Metric

section covariance

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X Y Z : Ω → ℝ} (c : ℝ)

lemma covariance_fun_add_left [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[fun ω ↦ X ω + Y ω, Z; μ] = cov[fun ω ↦ X ω, Z; μ] + cov[fun ω ↦ Y ω, Z; μ] :=
  covariance_add_left hX hY hZ
lemma covariance_fun_add_right [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[X, fun ω ↦ Y ω + Z ω; μ] = cov[X, fun ω ↦ Y ω; μ] + cov[X, fun ω ↦ Z ω; μ] :=
  covariance_add_right hX hY hZ
lemma variance_fun_div (hX : AEMeasurable X μ) :
    Var[fun ω ↦ X ω / c; μ] = Var[X; μ] / c ^ 2 := by
  rw [← covariance_self (by fun_prop), covariance_fun_div_left, covariance_fun_div_right,
    covariance_self hX]
  field_simp
end ProbabilityTheory

open ProbabilityTheory MeasurableSpace

lemma MeasurableSpace.comap_process {Ω T : Type*} {𝓧 : T → Type*} [∀ t, MeasurableSpace (𝓧 t)]
    (X : (t : T) → Ω → 𝓧 t) :
    MeasurableSpace.comap (fun ω t ↦ X t ω) MeasurableSpace.pi =
      ⨆ t, MeasurableSpace.comap (X t) inferInstance := by
  simp_rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rfl
lemma MeasurableSpace.comap_le_comap
    {Ω 𝓧 𝓨 : Type*} [m𝓧 : MeasurableSpace 𝓧] [m𝓨 : MeasurableSpace 𝓨]
    {X : Ω → 𝓧} {Y : Ω → 𝓨} (f : 𝓧 → 𝓨) (hf : Measurable f) (h : Y = f ∘ X) :
    m𝓨.comap Y ≤ m𝓧.comap X := by
  rw [h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hf.comap_le
lemma MeasurableSpace.generateFrom_singleton_eq_comap_indicator_one {Ω : Type*} {A : Set Ω} :
    MeasurableSpace.generateFrom {A} =
      MeasurableSpace.comap (A.indicator (1 : Ω → ℝ)) inferInstance := by
  refine le_antisymm (MeasurableSpace.generateFrom_le fun s hs ↦ ?_)
    (Measurable.comap_le ?_)
  · simp only [Set.mem_singleton_iff] at hs
    rw [hs, ← measurable_indicator_const_iff (1 : ℝ)]
    exact comap_measurable _
  · apply (measurable_indicator_const_iff 1).2 ?_
    exact MeasurableSpace.measurableSet_generateFrom (by simp)
lemma ProbabilityTheory.singleton_indepSets_comap_iff {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsZeroOrProbabilityMeasure P] {𝓧 : Type*}
    {m𝓧 : MeasurableSpace 𝓧} {A : Set Ω} {X : Ω → 𝓧} (hX : Measurable X) (hA : MeasurableSet A) :
    IndepSets {A} {s | MeasurableSet[m𝓧.comap X] s} P ↔
      (A.indicator (1 : Ω → ℝ)) ⟂ᵢ[P] X := by
  rw [IndepFun_iff_Indep, ← generateFrom_singleton_eq_comap_indicator_one]
  constructor
  · exact IndepSets.indep (generateFrom_le (by simpa)) hX.comap_le (by simp [IsPiSystem])
      (@MeasurableSpace.isPiSystem_measurableSet _ (m𝓧.comap X)) rfl (by simp)
  · refine fun h ↦ Indep.indepSets ?_
    convert h
    simp
end covariance


