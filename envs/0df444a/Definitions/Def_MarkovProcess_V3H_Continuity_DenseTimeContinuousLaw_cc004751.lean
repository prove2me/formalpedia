-- Prove2me | Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousLaw_cc004751
-- name    : MarkovProcess_V3H_Continuity_DenseTimeContinuousLaw_cc004751
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:32:09.656596+00:00
-- url     : https://prove2.me/theorems/04bf4edd-1ac3-4edd-9f17-a1e2fcf6fd98
-- title:
--   MarkovProcess: MarkovProcess_V3H_Continuity_DenseTimeContinuousLaw_cc004751
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
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

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

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



/-- On the continuous restriction range, extension followed by restriction is the identity. -/
theorem IsSupportedOnContinuousPaths.p2m_embedded_0eb019a7602852c8
    (κ : Kernel β (DenseTime → alpha)) (hκ : IsSupportedOnContinuousPaths κ)
    (default : ContinuousPath alpha) :
    (toContinuousPathKernel κ default).map ContinuousPath.denseRestriction = κ := by
  rw [toContinuousPathKernel_eq_map, ← Kernel.map_comp_right]
  · ext x s hs
    rw [Kernel.map_apply' _
      ((ContinuousPath.measurable_denseRestriction).comp
        (ContinuousPath.measurable_continuousExtension default)) x hs]
    have hfun :
        ContinuousPath.denseRestriction ∘ ContinuousPath.continuousExtension default
          =ᵐ[κ x] id :=
      (hκ x).mono fun path hpath ↦
        ContinuousPath.denseRestriction_continuousExtension_of_mem_range default hpath
    simpa only [Set.preimage_id] using measure_congr (hfun.preimage s)
  · exact ContinuousPath.measurable_continuousExtension default
  · exact ContinuousPath.measurable_denseRestriction

end Kernel
end
end MarkovProcess


