-- Prove2me | Definitions.Def_MarkovProcess_V3H_Kernel_C0SemigroupJoint_9aea0383
-- name    : MarkovProcess_V3H_Kernel_C0SemigroupJoint_9aea0383
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:27:48.719906+00:00
-- url     : https://prove2.me/theorems/a094cc72-7eb7-4baf-9ca9-89739f87512e
-- title:
--   MarkovProcess: MarkovProcess_V3H_Kernel_C0SemigroupJoint_9aea0383
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Semigroup_Basic_fec91841
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

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


