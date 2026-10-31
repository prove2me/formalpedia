-- Prove2me | Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0SemigroupFeller_3612e71e
-- name    : MarkovProcess_V3H_Kernel_PositiveC0SemigroupFeller_3612e71e
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:36:16.99409+00:00
-- url     : https://prove2.me/theorems/8c606354-da90-44ba-95f8-58a7a405f562
-- title:
--   MarkovProcess: MarkovProcess_V3H_Kernel_PositiveC0SemigroupFeller_3612e71e
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Feller_Semigroup_2cfe612a
import Definitions.Def_MarkovProcess_V3H_Kernel_C0_dfad2e28
import Definitions.Def_MarkovProcess_V3H_Kernel_Integral_2b459584
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorKernel_13678038
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0SemigroupKernel_c6b9bee0
import Definitions.Def_MarkovProcess_V3H_Semigroup_Basic_fec91841
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
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
# Feller property of kernels represented by positive `C₀` semigroups

The kernel semigroup represented by a strongly continuous semigroup of positive contractions
recovers the original operators on `C₀` and therefore satisfies the existing Feller interface.
This file makes no conservativity, stochastic-process, or Hunt-process claim.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ZeroAtInfty

namespace MarkovProcess.PositiveC0SemigroupFeller

open MarkovProcess.Semigroup

variable {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
  [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]

variable (S : StronglyContinuousContractionSemigroup C₀(α, ℝ))
  (hS : ∀ t, PositiveC0OperatorMeasure.IsPositive (S t))

/-- The represented kernel semigroup maps `C₀(α, ℝ)` into itself. -/
theorem mapsC0_kernelSemigroup :
    (PositiveC0SemigroupKernel.kernelSemigroup S hS).MapsC0 := by
  intro t f
  have heq : kernelIntegral (PositiveC0SemigroupKernel.kernelSemigroup S hS t) f = S t f := by
    funext x
    change ∫ y, f y ∂PositiveC0SemigroupKernel.kernelSemigroup S hS t x = S t f x
    rw [PositiveC0SemigroupKernel.kernelSemigroup_apply]
    exact _root_.MarkovProcess.PositiveC0OperatorKernel.p2m_embedded_4181f4d5139144bc
      (S t) (hS t) (S.norm_operator_le_one t) x f
  rw [heq]
  exact ⟨(S t f).continuous, zero_at_infty (S t f)⟩

/-- The represented `C₀`-valued kernel integral is exactly the original semigroup action. -/
@[simp]
theorem kernelSemigroup_c0KernelIntegral
    (hC0 : (PositiveC0SemigroupKernel.kernelSemigroup S hS).MapsC0)
    (t : NNReal) (f : C₀(α, ℝ)) :
    (PositiveC0SemigroupKernel.kernelSemigroup S hS).c0KernelIntegral hC0 t f = S t f := by
  apply ZeroAtInftyContinuousMap.ext
  intro x
  change ∫ y, f y ∂PositiveC0SemigroupKernel.kernelSemigroup S hS t x = S t f x
  rw [PositiveC0SemigroupKernel.kernelSemigroup_apply]
  exact _root_.MarkovProcess.PositiveC0OperatorKernel.p2m_embedded_4181f4d5139144bc
    (S t) (hS t) (S.norm_operator_le_one t) x f

/-- The represented continuous linear `C₀` operator is the original semigroup operator. -/
@[simp]
theorem kernelSemigroup_c0Operator
    (hC0 : (PositiveC0SemigroupKernel.kernelSemigroup S hS).MapsC0)
    (t : NNReal) :
    (PositiveC0SemigroupKernel.kernelSemigroup S hS).c0Operator hC0 t = S t := by
  apply ContinuousLinearMap.ext
  intro f
  exact kernelSemigroup_c0KernelIntegral S hS hC0 t f

/-- The represented `C₀` kernel operators have continuous time orbits. -/
theorem hasContinuousC0Orbits_kernelSemigroup :
    (PositiveC0SemigroupKernel.kernelSemigroup S hS).HasContinuousC0Orbits
      (mapsC0_kernelSemigroup S hS) := by
  intro f
  have heq : (fun t : NNReal ↦
      (PositiveC0SemigroupKernel.kernelSemigroup S hS).c0Operator
        (mapsC0_kernelSemigroup S hS) t f) = fun t ↦ S t f := by
    funext t
    rw [kernelSemigroup_c0Operator]
  rw [heq]
  exact S.continuous f

/-- The represented sub-Markov kernel semigroup satisfies the Feller interface. -/
theorem isFellerKernelSemigroup_kernelSemigroup :
    (PositiveC0SemigroupKernel.kernelSemigroup S hS).IsFellerKernelSemigroup :=
  ⟨mapsC0_kernelSemigroup S hS, hasContinuousC0Orbits_kernelSemigroup S hS⟩



end MarkovProcess.PositiveC0SemigroupFeller


