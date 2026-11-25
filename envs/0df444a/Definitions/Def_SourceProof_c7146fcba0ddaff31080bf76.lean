-- Prove2me | Definitions.Def_SourceProof_c7146fcba0ddaff31080bf76
-- name    : SourceProof_c7146fcba0ddaff31080bf76
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:58:41.505393+00:00
-- url     : https://prove2.me/theorems/8dab12f3-3e9b-430a-a8cc-0280d1a79646
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.elementaryIntegral_const_initial

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


theorem _root_.Prove2MeSourceProof.h_c7146fcba0ddaff31080bf76 (hH : IsSimplePredictable H F) (Z : Ω → ℝ) :
    hH.elementaryIntegral (fun _ : ℝ≥0 ↦ Z) = fun ω ↦ H 0 ω * Z ω := by
  funext ω
  have heq : hH.choose.initial ω = H 0 ω := by
    simpa only [_root_.Prove2MeSourceProof.h_a9c44e06617a4753cffd0417] using
      congrFun (congrFun hH.choose_spec 0) ω
  simp [ProbabilityTheory.IsSimplePredictable.elementaryIntegral, SimplePredictableRep.integral, heq]
end IsSimplePredictable
end ProbabilityTheory


