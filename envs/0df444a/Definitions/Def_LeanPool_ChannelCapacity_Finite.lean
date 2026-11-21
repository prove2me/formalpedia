-- Prove2me | Definitions.Def_LeanPool_ChannelCapacity_Finite
-- name    : LeanPool_ChannelCapacity_Finite
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:41:03.312207+00:00
-- url     : https://prove2.me/theorems/6c9c77a6-14db-4183-b986-7879afc6c0c8
-- title:
--   Finite
-- statement:
--   Definitions and structural lemmas for Finite, from Adam Benenson and LeanPool contributors's pinned Uniqueness of capacity-achieving priors development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Finite.lean

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
namespace ChannelCapacity
variable {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
namespace ProbabilityMeasure
noncomputable def entropy (μ : ProbabilityMeasure α) : ℝ :=
  ∑ a, Real.negMulLog ((μ.toMeasure {a}).toReal)
end ProbabilityMeasure
namespace Kernel
def RowMatrixFullRank (k : Kernel α β) : Prop :=
  Function.Injective fun w : α → ℝ =>
    fun b => ∑ a, w a * (k a {b}).toReal
end Kernel
section DiscreteKL
end DiscreteKL
section EntropyFormula
noncomputable def Kernel.rowProbabilityMeasure (k : Kernel α β) [IsMarkovKernel k] (a : α) :
    ProbabilityMeasure β :=
  ⟨k a, ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure (κ := k) a⟩
noncomputable def Kernel.rowEntropy (k : Kernel α β) [IsMarkovKernel k] (a : α) : ℝ :=
  ProbabilityMeasure.entropy (Kernel.rowProbabilityMeasure k a)
noncomputable def conditionalEntropy (p : ProbabilityMeasure α) (k : Kernel α β)
    [IsMarkovKernel k] : ℝ :=
  ∑ a, (p.toMeasure {a}).toReal * Kernel.rowEntropy k a
section FiniteWeakTopology
variable [TopologicalSpace α] [TopologicalSpace β]
  [DiscreteTopology α] [DiscreteTopology β]
  [BorelSpace α] [BorelSpace β]
  [CompactSpace α] [CompactSpace β]
noncomputable def singletonIndicatorContinuousMap (a : α) : C(α, ℝ) :=
  ⟨({a} : Set α).indicator (fun _ => (1 : ℝ)), continuous_of_discreteTopology⟩
end FiniteWeakTopology
section
end
end EntropyFormula
end ChannelCapacity


