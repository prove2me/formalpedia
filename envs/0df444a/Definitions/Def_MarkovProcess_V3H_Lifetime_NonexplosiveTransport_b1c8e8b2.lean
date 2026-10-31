-- Prove2me | Definitions.Def_MarkovProcess_V3H_Lifetime_NonexplosiveTransport_b1c8e8b2
-- name    : MarkovProcess_V3H_Lifetime_NonexplosiveTransport_b1c8e8b2
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:36:01.009113+00:00
-- url     : https://prove2.me/theorems/4dd5c54e-d661-4c71-96f3-ecf6deb3fbf3
-- title:
--   MarkovProcess: MarkovProcess_V3H_Lifetime_NonexplosiveTransport_b1c8e8b2
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Lifetime_Basic_6f1c513f
import Definitions.Def_MarkovProcess_V3H_Lifetime_Law_b2011c24
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

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



/-- A total inverse to `ofContinuousPath`, with a fixed value away from infinite-lifetime paths. -/
def continuousPathExtension (default : ContinuousPath alpha) :
    LifetimePath alpha → ContinuousPath alpha :=
  Function.extend ofContinuousPath id (fun _ ↦ default)

@[simp]
theorem continuousPathExtension_ofContinuousPath (default eta : ContinuousPath alpha) :
    continuousPathExtension default (ofContinuousPath eta) = eta := by
  exact Function.Injective.extend_apply ofContinuousPath_injective _ _ _



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







/-- Transporting an ordinary continuous-path kernel to lifetime paths and back recovers it. -/
@[simp]
theorem p2m_embedded_2dcc412841fa7100
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


