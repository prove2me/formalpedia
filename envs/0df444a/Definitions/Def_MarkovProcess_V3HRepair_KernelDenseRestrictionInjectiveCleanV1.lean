-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_KernelDenseRestrictionInjectiveCleanV1
-- name    : MarkovProcess_V3HRepair_KernelDenseRestrictionInjectiveCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T09:44:49.717233+00:00
-- url     : https://prove2.me/theorems/06d20526-bcc2-4969-9c5e-118575454ab2
-- title:
--   Verified MarkovProcess source repair: KernelDenseRestrictionInjectiveCleanV1
-- statement:
--   Restriction of a continuous-path kernel to dense times admits reconstruction through continuous extension, so dense-time restrictions determine the original kernel.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream commit 1f8060caa137731fa08029592019eeaf9d997fe5; source-faithful adapted axiom-clean proof module V3HRepaired.KernelDenseRestrictionInjectiveCleanV1, archived SHA-256 933be72d542eb56ddd44d798bf6450e2e90975d3c7bedcd62a32fd7698754e89.

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Identifying continuous-path kernels from dense-time restrictions

Restriction to the fixed dense time carrier is injective on kernels whose target is continuous-path
space.  A measurable left inverse is obtained from the total continuous-extension map.  This is a
deterministic property of continuous paths; it makes no stochastic-process, Markov, or regularity
claim.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace Kernel

noncomputable section

variable {alpha beta : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [MeasurableSpace beta]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]

/-- Pushing a continuous-path kernel to dense-time paths and then applying the measurable total
continuous extension recovers the original kernel. -/
@[simp]
theorem map_denseRestriction_map_continuousExtension
    (kappa : Kernel beta (ContinuousPath alpha)) (default : ContinuousPath alpha) :
    (kappa.map ContinuousPath.denseRestriction).map
        (ContinuousPath.continuousExtension default) = kappa := by
  rw [← Kernel.map_comp_right]
  · have hcomp : ContinuousPath.continuousExtension default ∘
        ContinuousPath.denseRestriction = id := by
      funext omega
      exact ContinuousPath.continuousExtension_denseRestriction default omega
    rw [hcomp, Kernel.map_id]
  · exact ContinuousPath.measurable_denseRestriction
  · exact ContinuousPath.measurable_continuousExtension default

/-- A kernel on continuous-path space is determined by its pushforward to the fixed dense time
carrier. -/
theorem map_denseRestriction_injective :
    Function.Injective
      (fun kappa : Kernel beta (ContinuousPath alpha) ↦
        kappa.map ContinuousPath.denseRestriction) := by
  intro kappa eta h
  ext x s hs
  have himage : MeasurableSet (ContinuousPath.denseRestriction '' s) :=
    ContinuousPath.measurableEmbedding_denseRestriction.measurableSet_image' hs
  have hx := congrArg
    (fun z : Kernel beta (DenseTime → alpha) ↦
      z x (ContinuousPath.denseRestriction '' s)) h
  dsimp only at hx
  rw [Kernel.map_apply' _ ContinuousPath.measurable_denseRestriction x himage,
    Kernel.map_apply' _ ContinuousPath.measurable_denseRestriction x himage] at hx
  simpa only [ContinuousPath.denseRestriction_injective.preimage_image] using hx

end
end Kernel
end MarkovProcess

#print axioms MarkovProcess.Kernel.map_denseRestriction_injective


