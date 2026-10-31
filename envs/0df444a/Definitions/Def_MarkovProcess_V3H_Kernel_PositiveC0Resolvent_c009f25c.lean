-- Prove2me | Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0Resolvent_c009f25c
-- name    : MarkovProcess_V3H_Kernel_PositiveC0Resolvent_c009f25c
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:40:23.534373+00:00
-- url     : https://prove2.me/theorems/12036ac2-0f63-4afd-83eb-2deb5b80c5ee
-- title:
--   MarkovProcess: MarkovProcess_V3H_Kernel_PositiveC0Resolvent_c009f25c
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Feller_Semigroup_2cfe612a
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorKernel_13678038
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0SemigroupFeller_3612e71e
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0SemigroupKernel_c6b9bee0
import Definitions.Def_MarkovProcess_V3H_Semigroup_Basic_fec91841
import Definitions.Def_MarkovProcess_V3H_Semigroup_ContractiveResolvent_4e63c9ca
import Definitions.Def_MarkovProcess_V3H_Semigroup_Generation_6c19e644
import Definitions.Def_MarkovProcess_V3H_Semigroup_InvariantSet_e2a740e2
import Definitions.Def_MarkovProcess_V3H_Semigroup_PoissonInvariant_3353c646
import Definitions.Def_MarkovProcess_V3H_Semigroup_PositiveShift_fb2cca50
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Metrizable.Urysohn

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Positive `C₀` resolvents and their Feller kernels

A positive contractive resolvent on `C₀` canonically generates a strongly continuous semigroup
of positive contractions.  The existing pointwise Riesz construction then represents that
semigroup by a sub-Markov kernel semigroup and identifies its `C₀` operators exactly.

The package in this file starts from the resolvent identity, the Hille--Yosida bound, dense range,
and positivity of the actual shifted resolvents.  It assumes neither a semigroup nor a kernel.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ZeroAtInfty

noncomputable section

namespace MarkovProcess

open MarkovProcess.Semigroup

variable (X : Type*) [TopologicalSpace X]

/-- A contractive resolvent on `C₀(X, ℝ)` whose shifted operators preserve nonnegative
functions. -/
structure PositiveC0ContractiveResolvent extends ContractiveResolvent C₀(X, ℝ) where
  /-- Every shifted resolvent is positivity preserving. -/
  isPositive : ∀ alpha,
    PositiveC0OperatorMeasure.IsPositive (toContractiveResolvent.operator alpha)

namespace PositiveC0ContractiveResolvent

variable {X : Type*} [TopologicalSpace X]

/-- The closed cone of pointwise nonnegative functions in `C₀(X, ℝ)`. -/
def nonnegativeSet : Set C₀(X, ℝ) :=
  {f | ∀ x, 0 ≤ f x}

theorem isClosed_nonnegativeSet : IsClosed (nonnegativeSet (X := X)) := by
  unfold nonnegativeSet
  rw [show {f : C₀(X, ℝ) | ∀ x, 0 ≤ f x} =
      ⋂ x : X, {f : C₀(X, ℝ) | f x ∈ Set.Ici 0} by
    ext f
    simp only [mem_ofPred_eq, mem_iInter, mem_Ici]]
  apply isClosed_iInter
  intro x
  exact isClosed_Ici.preimage
    (((ZeroAtInftyContinuousMap.isometry_toBCF (α := X) (β := ℝ)).continuous).eval
      continuous_const)

theorem convex_nonnegativeSet : Convex ℝ (nonnegativeSet (X := X)) := by
  intro f hf g hg a b ha hb _hab x
  change 0 ≤ a * f x + b * g x
  exact add_nonneg (mul_nonneg ha (hf x)) (mul_nonneg hb (hg x))

theorem zero_mem_nonnegativeSet :
    (0 : C₀(X, ℝ)) ∈ nonnegativeSet (X := X) := by
  intro x
  exact le_rfl

variable (R : PositiveC0ContractiveResolvent X)

/-- Every normalized shifted resolvent preserves the pointwise nonnegative cone. -/
theorem preservesSet_scaledOperator_nonnegative (alpha : PositiveShift) :
    PreservesSet (R.toContractiveResolvent.scaledOperator alpha)
      (nonnegativeSet (X := X)) (nonnegativeSet (X := X)) := by
  intro f hf x
  change 0 ≤ (alpha : ℝ) * R.toContractiveResolvent.operator alpha f x
  exact mul_nonneg alpha.property.le (R.isPositive alpha f hf x)

/-- The canonical semigroup generated by a positive `C₀` contractive resolvent is positivity
preserving at every time. -/
theorem isPositive_generatedSemigroup :
    ∀ t, PositiveC0OperatorMeasure.IsPositive
      (R.toContractiveResolvent.generatedSemigroup t) := by
  intro t f hf
  exact R.toContractiveResolvent.preservesSet_generatedSemigroup_of_scaledOperator
    (nonnegativeSet (X := X)) isClosed_nonnegativeSet convex_nonnegativeSet
    zero_mem_nonnegativeSet R.preservesSet_scaledOperator_nonnegative t hf

section Kernel

variable [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-- The sub-Markov kernel semigroup represented by the canonical positive `C₀` semigroup. -/
noncomputable def kernelSemigroup : SubMarkovKernelSemigroup X :=
  PositiveC0SemigroupKernel.kernelSemigroup
    R.toContractiveResolvent.generatedSemigroup R.isPositive_generatedSemigroup

/-- The represented kernels act on `C₀` exactly by the generated semigroup operators. -/
theorem integral_kernelSemigroup (t : NNReal) (f : C₀(X, ℝ)) (x : X) :
    ∫ y, f y ∂R.kernelSemigroup t x =
      R.toContractiveResolvent.generatedSemigroup t f x := by
  rw [kernelSemigroup, PositiveC0SemigroupKernel.kernelSemigroup_apply]
  exact _root_.MarkovProcess.PositiveC0OperatorKernel.p2m_embedded_4181f4d5139144bc
    (R.toContractiveResolvent.generatedSemigroup t)
    (R.isPositive_generatedSemigroup t)
    (R.toContractiveResolvent.generatedSemigroup.norm_operator_le_one t) x f

/-- The represented kernel semigroup satisfies the Feller interface. -/
theorem isFellerKernelSemigroup_kernelSemigroup : R.kernelSemigroup.IsFellerKernelSemigroup :=
  PositiveC0SemigroupFeller.isFellerKernelSemigroup_kernelSemigroup
    R.toContractiveResolvent.generatedSemigroup R.isPositive_generatedSemigroup



end Kernel

end PositiveC0ContractiveResolvent

end MarkovProcess


