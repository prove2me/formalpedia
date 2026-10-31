-- Prove2me | Definitions.Def_MarkovProcess_V3H_DenseTime_Shift_b3e2f7d9
-- name    : MarkovProcess_V3H_DenseTime_Shift_b3e2f7d9
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:32:21.303322+00:00
-- url     : https://prove2.me/theorems/a63541d1-d47a-412b-b9da-1e9744e96ef4
-- title:
--   MarkovProcess: MarkovProcess_V3H_DenseTime_Shift_b3e2f7d9
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Shifts of dense-time paths

This file defines addition by a nonnegative rational time on the fixed dense carrier and the
induced shift of dense-time paths.  Restriction of a continuous path commutes with this shift.
No probability law or Markov property is asserted.
-/

namespace MarkovProcess

noncomputable section

namespace DenseTime

/-- Addition by a fixed dense time as an order embedding of the dense time carrier. -/
def addOrderEmbedding (s : DenseTime) : DenseTime ↪o DenseTime :=
  OrderEmbedding.ofStrictMono (fun t ↦ s + t) fun _ _ h ↦ by
    simpa only [add_comm] using add_lt_add_left h s

@[simp]
theorem p2m_embedded_c719b818823db419 (s t : DenseTime) : addOrderEmbedding s t = s + t := rfl

/-- Embedding a rational-time sum into physical time gives the sum of the embedded times. -/
@[simp]
theorem castOrderEmbedding_add (s t : DenseTime) :
    castOrderEmbedding (s + t) = castOrderEmbedding s + castOrderEmbedding t := by
  change ((s + t : DenseTime) : NNReal) = (s : NNReal) + (t : NNReal)
  norm_cast

end DenseTime

namespace DenseTimePath

variable {alpha : Type*}

/-- Shift a dense-time path by a fixed nonnegative rational time. -/
def shift (s : DenseTime) (path : DenseTime → alpha) : DenseTime → alpha :=
  path ∘ DenseTime.addOrderEmbedding s

@[simp]
theorem p2m_embedded_91abc2ea1e78e481 (s t : DenseTime) (path : DenseTime → alpha) :
    shift s path t = path (s + t) := rfl

@[simp]
theorem p2m_embedded_ef56d2d502cd8d81 (path : DenseTime → alpha) : shift 0 path = path := by
  funext t
  simp only [_root_.MarkovProcess.DenseTimePath.p2m_embedded_91abc2ea1e78e481, zero_add]



variable [MeasurableSpace alpha]



end DenseTimePath

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]



end ContinuousPath
end
end MarkovProcess


