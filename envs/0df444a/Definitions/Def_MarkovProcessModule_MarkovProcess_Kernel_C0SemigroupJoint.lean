-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Kernel_C0SemigroupJoint
-- name    : MarkovProcessModule_MarkovProcess_Kernel_C0SemigroupJoint
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:40:48.896709+00:00
-- url     : https://prove2.me/theorems/98615727-e4a0-48ba-a2f2-85f1bfd24e1d
-- title:
--   MarkovProcess.Kernel.C0SemigroupJoint
-- statement:
--   # Joint regularity of strongly continuous semigroups on `C₀`
--
--   Strong continuity of a semigroup orbit in the `C₀` norm and continuity of
--   evaluation give continuity, jointly in time and state, of the evaluated orbit.
--   The corresponding Borel measurability statement follows without any additional
--   regularity premise on the semigroup.
--
--   This is a generic functional-analytic API. It makes no representation claim
--   about the semigroup.
--
--   Complete pinned Lean module MarkovProcess.Kernel.C0SemigroupJoint by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/C0SemigroupJoint.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Semigroup_Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Joint regularity of strongly continuous semigroups on `C₀`

Strong continuity of a semigroup orbit in the `C₀` norm and continuity of
evaluation give continuity, jointly in time and state, of the evaluated orbit.
The corresponding Borel measurability statement follows without any additional
regularity premise on the semigroup.

This is a generic functional-analytic API. It makes no representation claim
about the semigroup.
-/

open scoped ZeroAtInfty

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

variable {α : Type*} [TopologicalSpace α]

/-- A strongly continuous `C₀`-semigroup orbit is jointly continuous in time
and state after evaluation. -/
theorem continuous_apply_apply
    (S : StronglyContinuousContractionSemigroup C₀(α, ℝ)) (f : C₀(α, ℝ)) :
    Continuous fun tx : NNReal × α ↦ S tx.1 f tx.2 :=
  ((ZeroAtInftyContinuousMap.isometry_toBCF (α := α) (β := ℝ)).continuous.comp
    ((S.continuous f).comp continuous_fst)).eval continuous_snd

/-- Joint evaluation of a strongly continuous `C₀`-semigroup orbit is Borel
measurable for the product measurable space. -/
theorem measurable_apply_apply
    [MeasurableSpace α] [BorelSpace α]
    (S : StronglyContinuousContractionSemigroup C₀(α, ℝ)) (f : C₀(α, ℝ)) :
    Measurable fun tx : NNReal × α ↦ S tx.1 f tx.2 :=
  (S.continuous_apply_apply f).measurable

end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup


