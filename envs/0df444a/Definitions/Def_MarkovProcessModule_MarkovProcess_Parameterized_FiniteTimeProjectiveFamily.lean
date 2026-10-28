-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Parameterized_FiniteTimeProjectiveFamily
-- name    : MarkovProcessModule_MarkovProcess_Parameterized_FiniteTimeProjectiveFamily
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T20:06:17.158831+00:00
-- url     : https://prove2.me/theorems/e26ac95c-e85e-4608-8308-c7c7a684712d
-- title:
--   MarkovProcess.Parameterized.FiniteTimeProjectiveFamily
-- statement:
--   # Parameterized finite-set finite-time kernels
--
--   This file reindexes parameterized finite-time kernels by finite sets of times. It proves exact
--   agreement with the ordinary finite-set kernel at every fixed parameter and starting state, and
--   derives projectivity under fiberwise conservativity. It does not construct a projective-limit
--   measure or a stochastic process.
--
--   Complete pinned Lean module MarkovProcess.Parameterized.FiniteTimeProjectiveFamily by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Parameterized/FiniteTimeProjectiveFamily.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_FiniteTime_ProjectiveFamily
import Definitions.Def_MarkovProcessModule_MarkovProcess_Parameterized_FiniteTimeKernel

/-!
# Parameterized finite-set finite-time kernels

This file reindexes parameterized finite-time kernels by finite sets of times. It proves exact
agreement with the ordinary finite-set kernel at every fixed parameter and starting state, and
derives projectivity under fiberwise conservativity. It does not construct a projective-limit
measure or a stochastic process.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]

/-- The jointly measurable finite-time kernel indexed by a finite set of times. -/
noncomputable def parameterizedFiniteSetKernel
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (I : Finset NNReal) :
    Kernel (Theta × alpha) (I → alpha) :=
  Kernel.mapOfMeasurable
    (P.parameterizedFiniteTimeKernel (SubMarkovKernelSemigroup.finiteSetTimes I))
    (SubMarkovKernelSemigroup.orderedPathToFiniteSet I)
    (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I)

/-- The parameterized finite-set kernel agrees with the ordinary kernel map. -/
theorem parameterizedFiniteSetKernel_eq_map
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (I : Finset NNReal) :
    P.parameterizedFiniteSetKernel I =
      (P.parameterizedFiniteTimeKernel
        (SubMarkovKernelSemigroup.finiteSetTimes I)).map
          (SubMarkovKernelSemigroup.orderedPathToFiniteSet I) :=
  Kernel.mapOfMeasurable_eq_map _
    (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I)

/-- At a fixed parameter and start, the parameterized finite-set kernel is the ordinary one. -/
theorem parameterizedFiniteSetKernel_apply
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (I : Finset NNReal)
    (theta : Theta) (x : alpha) :
    P.parameterizedFiniteSetKernel I (theta, x) =
      (P.toSubMarkovKernelSemigroup theta).finiteSetKernel I x := by
  rw [parameterizedFiniteSetKernel_eq_map,
    Kernel.map_apply _ (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I),
    parameterizedFiniteTimeKernel_apply,
    SubMarkovKernelSemigroup.finiteSetKernel_eq_map,
    Kernel.map_apply _ (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I)]

/-- Fiberwise conservativity makes every parameterized finite-set kernel Markov. -/
theorem isMarkovKernel_parameterizedFiniteSetKernel
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (I : Finset NNReal) : IsMarkovKernel (P.parameterizedFiniteSetKernel I) := by
  rw [parameterizedFiniteSetKernel_eq_map]
  let : IsMarkovKernel
      (P.parameterizedFiniteTimeKernel (SubMarkovKernelSemigroup.finiteSetTimes I)) :=
    P.isMarkovKernel_parameterizedFiniteTimeKernel hP
      (SubMarkovKernelSemigroup.finiteSetTimes I)
  exact Kernel.IsMarkovKernel.map _
    (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I)

/-- Restriction along an inclusion gives the kernel on the smaller finite time set. -/
theorem parameterizedFiniteSetKernel_map_restrict₂
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    {I J : Finset NNReal} (hJI : J ⊆ I) :
    P.parameterizedFiniteSetKernel J =
      (P.parameterizedFiniteSetKernel I).map
        (Finset.restrict₂ (π := fun _ ↦ alpha) hJI) := by
  apply Kernel.ext
  intro q
  obtain ⟨theta, x⟩ := q
  rw [Kernel.map_apply _ (Finset.measurable_restrict₂ (X := fun _ ↦ alpha) hJI),
    parameterizedFiniteSetKernel_apply, parameterizedFiniteSetKernel_apply]
  have h := congrArg (fun K : Kernel alpha (J → alpha) ↦ K x)
    ((hP theta).finiteSetKernel_map_restrict₂
      (P.toSubMarkovKernelSemigroup theta) hJI)
  change (P.toSubMarkovKernelSemigroup theta).finiteSetKernel J x =
    ((P.toSubMarkovKernelSemigroup theta).finiteSetKernel I).map
      (Finset.restrict₂ (π := fun _ ↦ alpha) hJI) x at h
  rw [Kernel.map_apply _ (Finset.measurable_restrict₂ (X := fun _ ↦ alpha) hJI)] at h
  exact h

/-- At every parameter and start, the finite-set laws form a projective measure family. -/
theorem isProjectiveMeasureFamily_parameterizedFiniteSetKernel_apply
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (theta : Theta) (x : alpha) :
    IsProjectiveMeasureFamily (α := fun _ : NNReal ↦ alpha)
      (fun I : Finset NNReal ↦ P.parameterizedFiniteSetKernel I (theta, x)) := by
  intro I J hJI
  change P.parameterizedFiniteSetKernel J (theta, x) =
    Measure.map (Finset.restrict₂ (π := fun _ ↦ alpha) hJI)
      (P.parameterizedFiniteSetKernel I (theta, x))
  rw [← Kernel.map_apply _ (Finset.measurable_restrict₂ (X := fun _ ↦ alpha) hJI)]
  exact congrArg (fun K : Kernel (Theta × alpha) (J → alpha) ↦ K (theta, x))
    (P.parameterizedFiniteSetKernel_map_restrict₂ hP hJI)

end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess


