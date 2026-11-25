-- Prove2me | Definitions.Def_SourceProof_92ecc823f6e85260a04d51c7
-- name    : SourceProof_92ecc823f6e85260a04d51c7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:57:05.656915+00:00
-- url     : https://prove2.me/theorems/f327de71-6a73-5a82-9c98-1042ebc7b15c
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.eLpNorm_elementaryIntegral_min_const_le

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Sampling_F000
import Definitions.Def_SourceProof_bc13bcc2e8c79f08b8230861
import Definitions.Def_SourceProof_cfea7ef7947d7407a37a3e21
import Definitions.Def_SourceProof_da50a9b4aa24d95cd193edfb

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The source elementary-integral L2 estimate

For a martingale stopped at a finite deterministic horizon `T`, a uniform process bound `C`
on a simple predictable integrand gives `E[(H · X^T)^2] ≤ C^2 E[X_T^2]`. The source initial
term is retained, random endpoints are not bounded deterministically, and coefficients on
empty intervals are normalized before applying the discrete martingale estimate.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]
  {X : ℝ≥0 → Ω → ℝ}

namespace SimplePredictableRep

end SimplePredictableRep

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_92ecc823f6e85260a04d51c7 (hH : IsSimplePredictable H F)
    (hX : Martingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (T : ℝ≥0) (hXT : MemLp (X T) 2 P) (C : ℝ≥0) (hb : ∀ t ω, ‖H t ω‖ ≤ C) :
    eLpNorm (hH.elementaryIntegral (fun t ↦ X (min t T))) 2 P ≤ C * eLpNorm (X T) 2 P :=
  _root_.Prove2MeSourceProof.h_cfea7ef7947d7407a37a3e21
    ((_root_.Prove2MeSourceProof.h_da50a9b4aa24d95cd193edfb hH) hX hF hr T hXT C hb) hXT C
    ((_root_.Prove2MeSourceProof.h_bc13bcc2e8c79f08b8230861 hH) hX hF hr T hXT C hb)
end IsSimplePredictable
end ProbabilityTheory


