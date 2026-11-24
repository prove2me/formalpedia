-- Prove2me | Definitions.Def_SourceProof_2de3ac64de8bd31f1d59bd9f
-- name    : SourceProof_2de3ac64de8bd31f1d59bd9f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:28.165546+00:00
-- url     : https://prove2.me/theorems/f05187a2-52cd-4281-a73c-170ccfffd4cd
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.measurable_initial

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F003
import Definitions.Def_SourceProof_a9c44e06617a4753cffd0417

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Protter simple predictable processes and their elementary integral

The coefficients are finite real random variables, measurable at the left
stopping endpoint. They need not be bounded. A representation is witness data;
the public process is a raw function. Representation independence is proved
before the public integral selector is introduced.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal BigOperators

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace SimplePredictableRep

variable {F : Filtration ℝ≥0 mΩ}

end SimplePredictableRep

namespace IsSimplePredictable

variable {F : Filtration ℝ≥0 mΩ} {H : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_2de3ac64de8bd31f1d59bd9f (hH : IsSimplePredictable H F) : Measurable[F 0] (H 0) := by
  have heq : H 0 = hH.choose.initial := by
    funext ω
    simpa only [_root_.Prove2MeSourceProof.h_a9c44e06617a4753cffd0417] using
      (congrFun (congrFun hH.choose_spec 0) ω).symm
  rw [heq]
  exact hH.choose.measurable_initial
end IsSimplePredictable
end ProbabilityTheory


