-- Prove2me | Definitions.Def_LeanPool_ChannelCapacity_Discharged
-- name    : LeanPool_ChannelCapacity_Discharged
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:41:06.539718+00:00
-- url     : https://prove2.me/theorems/21812960-9b1a-47c8-9fa9-c7e475a8bb72
-- title:
--   Discharged
-- statement:
--   Definitions and structural lemmas for Discharged, from Adam Benenson and LeanPool contributors's pinned Uniqueness of capacity-achieving priors development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Discharged.lean

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal
namespace ChannelCapacity
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [TopologicalSpace α] [TopologicalSpace β]
namespace Kernel
structure ContinuousPositiveDensity
    (k : Kernel α β) (ν : Measure β) [IsMarkovKernel k] [OpensMeasurableSpace α] where
  /-- The common density of every row of `k` with respect to `ν`. -/
  density : α → β → NNReal
  continuous_density : Continuous (Function.uncurry density)
  eq_withDensity : ∀ a, k a = ν.withDensity (fun b => (density a b : ℝ≥0∞))
  density_pos : ∀ a b, 0 < density a b
  mutualInformation_usc :
    UpperSemicontinuous fun p : ProbabilityMeasure α => mutualInformation p k
namespace ContinuousPositiveDensity
variable {k : Kernel α β} [IsMarkovKernel k] [OpensMeasurableSpace α] {ν : Measure β}
section UniformBounds
variable [CompactSpace α] [CompactSpace β] [Nonempty α] [Nonempty β]
end UniformBounds
section OutputPrior
variable [CompactSpace α] [CompactSpace β] [PolishSpace α] [PolishSpace β]
variable [BorelSpace α] [BorelSpace β]
variable [OpensMeasurableSpace β] [IsFiniteMeasure ν]
noncomputable def outputDensity (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) :
    β → ENNReal :=
  fun b => ∫⁻ a, (h.density a b : ENNReal) ∂p.toMeasure
end OutputPrior
section Compactness
variable [CompactSpace α] [PolishSpace α] [BorelSpace α] [Nonempty α]
end Compactness
end ContinuousPositiveDensity
end Kernel
section Capacity
variable [CompactSpace α] [CompactSpace β] [PolishSpace α] [PolishSpace β]
variable [BorelSpace α] [BorelSpace β]
variable [OpensMeasurableSpace α] [OpensMeasurableSpace β]
variable [MeasurableSpace.CountableOrCountablyGenerated α β]
variable [Nonempty α]
end Capacity
end ChannelCapacity


