-- Prove2me | Definitions.Def_Malliavin_PredictableKernel
-- name    : Malliavin_PredictableKernel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:13:41.261275+00:00
-- url     : https://prove2.me/theorems/04de028f-d336-44de-8557-3f9a7e5dca1f
-- title:
--   Predictable Kernel
-- statement:
--   Definitions and structural lemmas for Predictable Kernel, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableKernel.lean

import Definitions.Def_Malliavin_ClarkOcone
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Composition.MapComap
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
namespace Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
noncomputable def finiteHorizonTimeMeasure (T : ℝ≥0) : Measure ℝ≥0 :=
  nonnegativeLebesgueMeasure.restrict (Set.Iic T)
instance (T : ℝ≥0) : IsFiniteMeasure (finiteHorizonTimeMeasure T) :=
  isFiniteMeasure_restrict.mpr (nonnegativeLebesgueMeasure_Iic_ne_top T)
noncomputable def finiteHorizonProductMeasure (P : Measure W) (T : ℝ≥0) :
    Measure (ℝ≥0 × W) :=
  (finiteHorizonTimeMeasure T).prod P
instance (P : Measure W) [IsFiniteMeasure P] (T : ℝ≥0) :
    IsFiniteMeasure (finiteHorizonProductMeasure P T) := by
  unfold finiteHorizonProductMeasure
  infer_instance
section SameTime
variable {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]
noncomputable def predictableSectionKernel
    (μ : Measure (ℝ≥0 × S)) [IsFiniteMeasure μ]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace S›) :
    @Kernel (ℝ≥0 × S) S 𝓕.predictable inferInstance :=
  (condExpKernel μ 𝓕.predictable).map Prod.snd
instance instIsMarkovKernelPredictableSectionKernel
    (μ : Measure (ℝ≥0 × S)) [IsFiniteMeasure μ]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace S›) :
    IsMarkovKernel (predictableSectionKernel μ 𝓕) := by
  unfold predictableSectionKernel
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _ measurable_snd
end SameTime
end Malliavin


