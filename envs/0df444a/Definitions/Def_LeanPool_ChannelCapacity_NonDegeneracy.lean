-- Prove2me | Definitions.Def_LeanPool_ChannelCapacity_NonDegeneracy
-- name    : LeanPool_ChannelCapacity_NonDegeneracy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:39:35.598762+00:00
-- url     : https://prove2.me/theorems/59bc672d-0346-46bb-ad6a-2a8f17f463c1
-- title:
--   Non Degeneracy
-- statement:
--   Definitions and structural lemmas for Non Degeneracy, from Adam Benenson and LeanPool contributors's pinned Uniqueness of capacity-achieving priors development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/NonDegeneracy.lean

module
public import Definitions.Def_LeanPool_ChannelCapacity_Basic
public import Mathlib.MeasureTheory.Measure.DiracProba
public import Mathlib.Probability.Kernel.Composition.MeasureComp
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal
namespace ChannelCapacity
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
namespace Kernel
noncomputable def priorPushforward (k : Kernel α β) [IsMarkovKernel k]
    (p : ProbabilityMeasure α) : ProbabilityMeasure β :=
  outputPrior k p
def RowSeparating (k : Kernel α β) : Prop :=
  ∀ ⦃a a' : α⦄, a ≠ a' → k a ≠ k a'
def InjectivePriorPushforward (k : Kernel α β) [IsMarkovKernel k] : Prop :=
  Function.Injective (priorPushforward k)
def OutputMarginalReference (k : Kernel α β) [IsMarkovKernel k]
    (p : ProbabilityMeasure α) (ν : Measure β) : Prop :=
  ∃ q : ProbabilityMeasure α, p.toMeasure ≪ q.toMeasure ∧ ν = (outputPrior k q).toMeasure
structure WellConditionedForCapacity (k : Kernel α β) [IsMarkovKernel k] : Prop where
  hRowAC : ∀ p : ProbabilityMeasure α,
    ∀ᵐ x ∂p.toMeasure, k x ≪ (outputPrior k p).toMeasure
  hFiniteRefKL : ∀ (p : ProbabilityMeasure α) (ν : Measure β),
    OutputMarginalReference k p ν →
      InformationTheory.klDiv (p.toMeasure ⊗ₘ k) (p.toMeasure ⊗ₘ Kernel.const _ ν) ≠ ∞
  hChainRule : ∀ (p : ProbabilityMeasure α) (ν : Measure β),
    OutputMarginalReference k p ν →
      InformationTheory.klDiv (jointLaw k p).toMeasure (p.toMeasure ⊗ₘ Kernel.const _ ν) =
        InformationTheory.klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure +
          InformationTheory.klDiv (outputPrior k p).toMeasure ν
end Kernel
end ChannelCapacity


