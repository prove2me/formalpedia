-- Prove2me | Definitions.Def_LeanPool_ChannelCapacity_Basic
-- name    : LeanPool_ChannelCapacity_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:39:16.398726+00:00
-- url     : https://prove2.me/theorems/9fbbda60-cf7c-40f1-bc4b-03c4660272cd
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Adam Benenson and LeanPool contributors's pinned Uniqueness of capacity-achieving priors development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/Basic.lean

module
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Kernel.Composition.CompNotation
public import Mathlib.Probability.Kernel.Composition.MeasureComp
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal
namespace ProbabilityMeasure
variable {Ω : Type*} [MeasurableSpace Ω]
noncomputable def convexCombination (μ ν : ProbabilityMeasure Ω) (t : NNReal)
    (ht : t ≤ (1 : NNReal)) :
    ProbabilityMeasure Ω :=
  ⟨t • μ.toMeasure + ((1 : NNReal) - t) • ν.toMeasure, by
    refine ⟨?_⟩
    calc
      (t • μ.toMeasure + ((1 : NNReal) - t) • ν.toMeasure) Set.univ =
          (t • μ.toMeasure) Set.univ + (((1 : NNReal) - t) • ν.toMeasure) Set.univ := by
            rw [Measure.add_apply]
      _ = t • (μ.toMeasure Set.univ) + ((1 : NNReal) - t) • (ν.toMeasure Set.univ) := by
            simp [Measure.smul_apply]
      _ = t • (1 : ENNReal) + ((1 : NNReal) - t) • (1 : ENNReal) := by simp
      _ = 1 := by
            change (t : ENNReal) * 1 + (((1 : NNReal) - t : NNReal) : ENNReal) * 1 = 1
            rw [mul_one, mul_one]
            have h : t + (1 - t) = (1 : NNReal) := add_tsub_cancel_of_le ht
            exact_mod_cast h⟩
end ProbabilityMeasure
namespace ChannelCapacity
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
noncomputable def outputPrior (k : Kernel α β) [IsMarkovKernel k] (p : ProbabilityMeasure α) :
    ProbabilityMeasure β :=
  ⟨k ∘ₘ p.toMeasure, by infer_instance⟩
noncomputable def jointLaw (k : Kernel α β) [IsMarkovKernel k] (p : ProbabilityMeasure α) :
    ProbabilityMeasure (α × β) :=
  ⟨p.toMeasure ⊗ₘ k, by infer_instance⟩
noncomputable def independentJointLaw (k : Kernel α β) [IsMarkovKernel k]
    (p : ProbabilityMeasure α) : ProbabilityMeasure (α × β) :=
  let q := outputPrior k p
  ⟨p.toMeasure ⊗ₘ Kernel.const α q.toMeasure, by infer_instance⟩
noncomputable def mutualInformation (p : ProbabilityMeasure α) (k : Kernel α β)
    [IsMarkovKernel k] : ℝ :=
  (InformationTheory.klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure).toReal
end ChannelCapacity


