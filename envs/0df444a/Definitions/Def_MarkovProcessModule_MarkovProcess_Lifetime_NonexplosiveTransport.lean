-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Lifetime_NonexplosiveTransport
-- name    : MarkovProcessModule_MarkovProcess_Lifetime_NonexplosiveTransport
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:53:06.531612+00:00
-- url     : https://prove2.me/theorems/9be0e51b-a8b8-4f3e-8e52-ea397aacf35d
-- title:
--   MarkovProcess.Lifetime.NonexplosiveTransport
-- statement:
--   # Transporting nonexplosive lifetime laws to continuous paths
--
--   This file constructs the measurable inverse of the infinite-lifetime embedding.  A kernel on
--   lifetime paths whose lifetime is almost surely infinite therefore gives a canonical kernel on
--   ordinary continuous paths, independent of the off-support default.
--
--   Complete pinned Lean module MarkovProcess.Lifetime.NonexplosiveTransport by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Lifetime/NonexplosiveTransport.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Lifetime_Law

/-!
# Transporting nonexplosive lifetime laws to continuous paths

This file constructs the measurable inverse of the infinite-lifetime embedding.  A kernel on
lifetime paths whose lifetime is almost surely infinite therefore gives a canonical kernel on
ordinary continuous paths, independent of the off-support default.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace MarkovProcess

noncomputable section

namespace LifetimePath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- Infinite-lifetime paths are exactly the paths coming from ordinary continuous paths. -/
theorem mem_range_ofContinuousPath_iff (omega : LifetimePath alpha) :
    omega ∈ Set.range (ofContinuousPath (α := alpha)) ↔ omega.lifetime = ∞ := by
  constructor
  · rintro ⟨eta, rfl⟩
    exact lifetime_ofContinuousPath eta
  · intro homega
    exact ⟨toContinuousPath omega homega,
      ofContinuousPath_toContinuousPath omega homega⟩

/-- A total inverse to `ofContinuousPath`, with a fixed value away from infinite-lifetime paths. -/
def continuousPathExtension (default : ContinuousPath alpha) :
    LifetimePath alpha → ContinuousPath alpha :=
  Function.extend ofContinuousPath id (fun _ ↦ default)

@[simp]
theorem continuousPathExtension_ofContinuousPath (default eta : ContinuousPath alpha) :
    continuousPathExtension default (ofContinuousPath eta) = eta := by
  exact Function.Injective.extend_apply ofContinuousPath_injective _ _ _

theorem continuousPathExtension_of_lifetime_eq_top (default : ContinuousPath alpha)
    (omega : LifetimePath alpha) (homega : omega.lifetime = ∞) :
    continuousPathExtension default omega = toContinuousPath omega homega := by
  calc
    continuousPathExtension default omega =
        continuousPathExtension default
          (ofContinuousPath (toContinuousPath omega homega)) :=
      congrArg (continuousPathExtension default)
        (ofContinuousPath_toContinuousPath omega homega).symm
    _ = toContinuousPath omega homega :=
      continuousPathExtension_ofContinuousPath default _

section Measurable

variable [MeasurableSpace alpha] [BorelSpace alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (LifetimePath alpha)]

/-- The total inverse is measurable for the coordinate-generated lifetime-path structure. -/
theorem measurable_continuousPathExtension (default : ContinuousPath alpha) :
    Measurable (continuousPathExtension default) :=
  measurableEmbedding_ofContinuousPath.measurable_extend measurable_id measurable_const

end Measurable
end LifetimePath

namespace Kernel

variable {beta alpha : Type*} [MeasurableSpace beta] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (LifetimePath alpha)]

/-- Transport a lifetime-path kernel to ordinary continuous paths.  Under nonexplosion, the
result is independent of `default`. -/
def fromLifetimePathKernel (kappa : Kernel beta (LifetimePath alpha))
    (default : ContinuousPath alpha) : Kernel beta (ContinuousPath alpha) :=
  Kernel.mapOfMeasurable kappa (LifetimePath.continuousPathExtension default)
    (LifetimePath.measurable_continuousPathExtension default)

/-- The lifetime-path transport agrees with ordinary kernel mapping. -/
theorem fromLifetimePathKernel_eq_map (kappa : Kernel beta (LifetimePath alpha))
    (default : ContinuousPath alpha) :
    fromLifetimePathKernel kappa default =
      kappa.map (LifetimePath.continuousPathExtension default) :=
  Kernel.mapOfMeasurable_eq_map _
    (LifetimePath.measurable_continuousPathExtension default)

/-- A Markov lifetime-path kernel remains Markov after transport to continuous paths. -/
theorem isMarkovKernel_fromLifetimePathKernel
    (kappa : Kernel beta (LifetimePath alpha)) [IsMarkovKernel kappa]
    (default : ContinuousPath alpha) :
    IsMarkovKernel (fromLifetimePathKernel kappa default) := by
  rw [fromLifetimePathKernel_eq_map]
  exact Kernel.IsMarkovKernel.map _
    (LifetimePath.measurable_continuousPathExtension default)

/-- Under nonexplosion, the transported continuous-path kernel does not depend on the default. -/
theorem IsNonexplosive.fromLifetimePathKernel_eq
    (kappa : Kernel beta (LifetimePath alpha)) (hkappa : IsNonexplosive kappa)
    (default₁ default₂ : ContinuousPath alpha) :
    fromLifetimePathKernel kappa default₁ = fromLifetimePathKernel kappa default₂ := by
  rw [fromLifetimePathKernel_eq_map, fromLifetimePathKernel_eq_map]
  ext x s hs
  rw [Kernel.map_apply' _ (LifetimePath.measurable_continuousPathExtension default₁) x hs,
    Kernel.map_apply' _ (LifetimePath.measurable_continuousPathExtension default₂) x hs]
  have hfun : LifetimePath.continuousPathExtension default₁ =ᵐ[kappa x]
      LifetimePath.continuousPathExtension default₂ :=
    (hkappa x).mono fun omega homega ↦ by
      rw [LifetimePath.continuousPathExtension_of_lifetime_eq_top default₁ omega homega,
        LifetimePath.continuousPathExtension_of_lifetime_eq_top default₂ omega homega]
  exact measure_congr (hfun.preimage s)

/-- Under nonexplosion, transport to continuous paths and back recovers the lifetime-path law. -/
theorem IsNonexplosive.toLifetimePathKernel_fromLifetimePathKernel
    (kappa : Kernel beta (LifetimePath alpha)) (hkappa : IsNonexplosive kappa)
    (default : ContinuousPath alpha) :
    toLifetimePathKernel (fromLifetimePathKernel kappa default) = kappa := by
  rw [toLifetimePathKernel_eq_map, fromLifetimePathKernel_eq_map, ← Kernel.map_comp_right]
  · ext x s hs
    rw [Kernel.map_apply' _
      (LifetimePath.measurable_ofContinuousPath.comp
        (LifetimePath.measurable_continuousPathExtension default)) x hs]
    have hfun : LifetimePath.ofContinuousPath ∘
        LifetimePath.continuousPathExtension default =ᵐ[kappa x] id :=
      (hkappa x).mono fun omega homega ↦ by
        change LifetimePath.ofContinuousPath
          (LifetimePath.continuousPathExtension default omega) = omega
        rw [LifetimePath.continuousPathExtension_of_lifetime_eq_top default omega homega,
          LifetimePath.ofContinuousPath_toContinuousPath omega homega]
    simpa only [Set.preimage_id] using measure_congr (hfun.preimage s)
  · exact LifetimePath.measurable_continuousPathExtension default
  · exact LifetimePath.measurable_ofContinuousPath

/-- Transporting an ordinary continuous-path kernel to lifetime paths and back recovers it. -/
@[simp]
theorem fromLifetimePathKernel_toLifetimePathKernel
    (kappa : Kernel beta (ContinuousPath alpha)) (default : ContinuousPath alpha) :
    fromLifetimePathKernel (toLifetimePathKernel kappa) default = kappa := by
  rw [fromLifetimePathKernel_eq_map, toLifetimePathKernel_eq_map, ← Kernel.map_comp_right]
  · have hcomp : LifetimePath.continuousPathExtension default ∘
        LifetimePath.ofContinuousPath = id := by
      funext eta
      exact LifetimePath.continuousPathExtension_ofContinuousPath default eta
    rw [hcomp, Kernel.map_id]
  · exact LifetimePath.measurable_ofContinuousPath
  · exact LifetimePath.measurable_continuousPathExtension default

end Kernel
end
end MarkovProcess


