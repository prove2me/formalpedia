-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Lifetime_Law
-- name    : MarkovProcessModule_MarkovProcess_Lifetime_Law
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:46:57.244867+00:00
-- url     : https://prove2.me/theorems/c1887fd7-334e-4d93-86a7-3e43b7f82493
-- title:
--   MarkovProcess.Lifetime.Law
-- statement:
--   # Continuous laws as nonexplosive lifetime-path laws
--
--   This file transports kernels on ordinary continuous paths through the infinite-lifetime
--   embedding. It records the resulting nonexplosion and coordinate identities without asserting
--   that any particular dense-time or PDE law has continuous paths.
--
--   Complete pinned Lean module MarkovProcess.Lifetime.Law by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Lifetime/Law.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Lifetime_Basic
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Continuous laws as nonexplosive lifetime-path laws

This file transports kernels on ordinary continuous paths through the infinite-lifetime
embedding. It records the resulting nonexplosion and coordinate identities without asserting
that any particular dense-time or PDE law has continuous paths.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess

noncomputable section

namespace Kernel

variable {beta alpha : Type*} [MeasurableSpace beta] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

/-- A kernel on lifetime paths is nonexplosive when its lifetime is almost surely infinite
from every starting point. -/
def IsNonexplosive (kappa : Kernel beta (LifetimePath alpha)) : Prop :=
  ∀ x, ∀ᵐ omega ∂kappa x, omega.lifetime = ∞

/-- Regard a kernel on ordinary continuous paths as a kernel on infinite-lifetime paths. -/
def toLifetimePathKernel (kappa : Kernel beta (ContinuousPath alpha)) :
    Kernel beta (LifetimePath alpha) :=
  Kernel.mapOfMeasurable kappa LifetimePath.ofContinuousPath
    LifetimePath.measurable_ofContinuousPath

/-- The lifetime-path transport agrees with ordinary kernel mapping. -/
theorem toLifetimePathKernel_eq_map (kappa : Kernel beta (ContinuousPath alpha)) :
    toLifetimePathKernel kappa = kappa.map LifetimePath.ofContinuousPath :=
  Kernel.mapOfMeasurable_eq_map _ LifetimePath.measurable_ofContinuousPath

/-- A Markov continuous-path kernel remains Markov after the infinite-lifetime embedding. -/
theorem isMarkovKernel_toLifetimePathKernel
    (kappa : Kernel beta (ContinuousPath alpha)) [IsMarkovKernel kappa] :
    IsMarkovKernel (toLifetimePathKernel kappa) := by
  rw [toLifetimePathKernel_eq_map]
  exact Kernel.IsMarkovKernel.map _ LifetimePath.measurable_ofContinuousPath

/-- Transporting an ordinary continuous-path law through the infinite-lifetime embedding is
nonexplosive. -/
theorem isNonexplosive_toLifetimePathKernel
    (kappa : Kernel beta (ContinuousPath alpha)) :
    IsNonexplosive (toLifetimePathKernel kappa) := by
  intro x
  rw [toLifetimePathKernel_eq_map,
    Kernel.map_apply _ LifetimePath.measurable_ofContinuousPath]
  refine (ae_map_iff (μ := kappa x)
    LifetimePath.measurable_ofContinuousPath.aemeasurable ?_).2 ?_
  · exact measurableSet_eq_fun LifetimePath.measurable_lifetime measurable_const
  · exact Filter.Eventually.of_forall LifetimePath.lifetime_ofContinuousPath

/-- At every time, the coordinate law of the lifetime-path transport is the original
continuous-path coordinate law, embedded as a live cemetery state. -/
theorem toLifetimePathKernel_map_coordinate
    (kappa : Kernel beta (ContinuousPath alpha)) (t : NNReal) :
    (toLifetimePathKernel kappa).map (LifetimePath.coordinate t) =
      kappa.map (fun omega => Cemetery.alive (omega t)) := by
  rw [toLifetimePathKernel_eq_map, ← Kernel.map_comp_right]
  · apply congrArg (Kernel.map kappa)
    funext omega
    exact LifetimePath.coordinate_ofContinuousPath omega t
  · exact LifetimePath.measurable_ofContinuousPath
  · exact LifetimePath.measurable_coordinate t

end Kernel
end
end MarkovProcess


