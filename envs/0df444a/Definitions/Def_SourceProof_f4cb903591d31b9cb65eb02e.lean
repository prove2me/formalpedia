-- Prove2me | Definitions.Def_SourceProof_f4cb903591d31b9cb65eb02e
-- name    : SourceProof_f4cb903591d31b9cb65eb02e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:52:32.255463+00:00
-- url     : https://prove2.me/theorems/afd3032e-b14b-48b4-a3cb-13cd0ccacbc0
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.jumpProcess_elementaryIntegralProcess

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_67aa45a3af307cb4d46b1678
import Definitions.Def_SourceProof_693094da5a8c94cbc1a6a90b
import Mathlib.Topology.Order.DenselyOrdered

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Jumps of the source elementary integral process

Actual left limits of the finite stopped summands give the formula at every time.
The coefficient on `(T_i,T_(i+1)]` is used at its right endpoint, with the separate
initial coefficient at zero. Repeated endpoints and unbounded coefficients are allowed.
-/

@[expose] public section

open MeasureTheory Filter Set Finset
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

namespace IsSimplePredictable
theorem _root_.Prove2MeSourceProof.h_f4cb903591d31b9cb65eb02e
    {H : ℝ≥0 → Ω → ℝ} (hH : IsSimplePredictable H F) (hX : IsCadlagPath (X · ω)) (t : ℝ≥0) :
    jumpProcess (hH.elementaryIntegralProcess X) t ω = H t ω * jumpProcess X t ω := by
  rw [(_root_.Prove2MeSourceProof.h_67aa45a3af307cb4d46b1678 hH) hH.choose hH.choose_spec X]
  simpa only [hH.choose_spec] using (_root_.Prove2MeSourceProof.h_693094da5a8c94cbc1a6a90b hH.choose) hX t
end IsSimplePredictable

end ProbabilityTheory


