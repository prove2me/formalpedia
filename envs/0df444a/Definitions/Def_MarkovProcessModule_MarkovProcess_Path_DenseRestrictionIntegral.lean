-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Path_DenseRestrictionIntegral
-- name    : MarkovProcessModule_MarkovProcess_Path_DenseRestrictionIntegral
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:40:58.756063+00:00
-- url     : https://prove2.me/theorems/d7a1a90d-e648-4328-b2b5-28e02b36c416
-- title:
--   MarkovProcess.Path.DenseRestrictionIntegral
-- statement:
--   # Integrals of finite dense-time marginals of a path measure
--
--   Integrating a compactly supported test against the finite dense-time marginal of a measure on
--   continuous-path space is integrating the composed test against the measure itself.  This is a
--   change-of-variables identity with no probabilistic content.
--
--   Complete pinned Lean module MarkovProcess.Path.DenseRestrictionIntegral by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Path/DenseRestrictionIntegral.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Continuity_DenseTimeContinuousExtension
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Integrals of finite dense-time marginals of a path measure

Integrating a compactly supported test against the finite dense-time marginal of a measure on
continuous-path space is integrating the composed test against the measure itself.  This is a
change-of-variables identity with no probabilistic content.
-/

open MeasureTheory
open scoped CompactlySupported

namespace MarkovProcess
namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha] [SecondCountableTopology alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

/-- A compactly supported test integrated against a finite dense-time marginal of a path measure
is the composed test integrated against the path measure. -/
theorem integral_map_denseRestriction_map_restrict
    (nu : Measure (ContinuousPath alpha)) (J : Finset DenseTime) (f : C_c(J → alpha, ℝ)) :
    ∫ z, f z ∂((nu.map denseRestriction).map J.restrict) =
      ∫ omega, f (J.restrict (denseRestriction omega)) ∂nu := by
  have hdense := measurable_denseRestriction (alpha := alpha)
  have hrestrict := Finset.measurable_restrict (X := fun _ ↦ alpha) J
  rw [Measure.map_map hrestrict hdense]
  exact integral_map (hrestrict.comp hdense).aemeasurable
    f.continuous.stronglyMeasurable.aestronglyMeasurable

end ContinuousPath
end MarkovProcess


