-- Prove2me | Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousLaw
-- name    : MarkovProcess_Continuity_DenseTimeContinuousLaw
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T12:46:43.587759+00:00
-- url     : https://prove2.me/theorems/5b9f7777-a1d0-4675-95f8-52cf8203896e
-- title:
--   MarkovProcess definitions: Continuity.DenseTimeContinuousLaw
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.Continuity.DenseTimeContinuousLaw`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DenseTimeContinuousLaw.lean#L1-L95

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousExtension
import Definitions.Def_MarkovProcess_Path_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_CountableDenseTime
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-!
# Transporting dense-time laws to continuous paths

This file transports a kernel on dense-time trajectories to ordinary continuous paths under an
explicit support-on-the-continuous-range hypothesis. It does not prove that support hypothesis.
-/

open MeasureTheory ProbabilityTheory Set

namespace MarkovProcess

noncomputable section

namespace Kernel

variable {β alpha : Type*} [MeasurableSpace β] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [T2Space alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]

/-- A dense-time kernel is almost surely supported on restrictions of continuous paths. -/
def IsSupportedOnContinuousPaths (κ : Kernel β (DenseTime → alpha)) : Prop :=
  ∀ x, ∀ᵐ path ∂κ x, path ∈ Set.range (ContinuousPath.denseRestriction (alpha := alpha))

/-- Transport a dense-time kernel to continuous paths by the measurable extension map. -/
def toContinuousPathKernel (κ : Kernel β (DenseTime → alpha))
    (default : ContinuousPath alpha) : Kernel β (ContinuousPath alpha) :=
  Kernel.mapOfMeasurable κ (ContinuousPath.continuousExtension default)
    (ContinuousPath.measurable_continuousExtension default)

/-- The continuous-path transport agrees with the ordinary kernel map. -/
theorem toContinuousPathKernel_eq_map (κ : Kernel β (DenseTime → alpha))
    (default : ContinuousPath alpha) :
    toContinuousPathKernel κ default =
      κ.map (ContinuousPath.continuousExtension default) :=
  Kernel.mapOfMeasurable_eq_map _
    (ContinuousPath.measurable_continuousExtension default)

/-- A Markov dense-time kernel transports to a Markov continuous-path kernel. -/
theorem isMarkovKernel_toContinuousPathKernel (κ : Kernel β (DenseTime → alpha))
    [IsMarkovKernel κ] (default : ContinuousPath alpha) :
    IsMarkovKernel (toContinuousPathKernel κ default) := by
  rw [toContinuousPathKernel_eq_map]
  exact Kernel.IsMarkovKernel.map _
    (ContinuousPath.measurable_continuousExtension default)





end Kernel
end
end MarkovProcess


