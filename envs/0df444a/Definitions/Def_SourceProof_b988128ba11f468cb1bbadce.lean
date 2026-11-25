-- Prove2me | Definitions.Def_SourceProof_b988128ba11f468cb1bbadce
-- name    : SourceProof_b988128ba11f468cb1bbadce
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:12:40.873802+00:00
-- url     : https://prove2.me/theorems/495b05ec-f136-41ef-b516-ac4ddd624343
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.integral_integralProcess

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Associativity_F000
import Definitions.Def_SourceProof_92f98353d1ecfc763009098e
import Definitions.Def_SourceProof_b1eb338f14932f1513d6a139
import Definitions.Def_SourceProof_e0009b000942fd3d989e2e5e
import Definitions.Def_SourceProof_f1dc368dba361aa17c9bfbeb
import Definitions.Def_SourceProof_f2413a3b51825efc6a057b76

open private integral_integralProcess_of_partition_eq from Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Associativity_F000
/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Associativity of source elementary integration

Actual common stopping partitions reduce the proof to the integral increment
on one cell. Both the initial coefficient product and every repeated endpoint
are retained. The integrator is arbitrary; no semimartingale premise is used.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep

theorem _root_.Prove2MeSourceProof.h_b988128ba11f468cb1bbadce (G H : SimplePredictableRep F) (X : ℝ≥0 → Ω → ℝ) :
    G.integral (H.integralProcess X) =
      ((_root_.Prove2MeSourceProof.h_f2413a3b51825efc6a057b76 (show IsSimplePredictable G.toProcess F from ⟨G, rfl⟩))
        (show IsSimplePredictable H.toProcess F from ⟨H, rfl⟩)).elementaryIntegral X := by
  obtain ⟨G', H', hp, hG, hH⟩ := (_root_.Prove2MeSourceProof.h_e0009b000942fd3d989e2e5e G) H
  have h := integral_integralProcess_of_partition_eq G' H' hp X
  rw [(_root_.Prove2MeSourceProof.h_f1dc368dba361aa17c9bfbeb G') G hG (H'.integralProcess X), (_root_.Prove2MeSourceProof.h_b1eb338f14932f1513d6a139 H') H hH X] at h
  refine h.trans (_root_.Prove2MeSourceProof.h_92f98353d1ecfc763009098e _ _ ?_ X)
  rw [hG, hH]
end SimplePredictableRep

namespace IsSimplePredictable

variable {G H : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable

end ProbabilityTheory


