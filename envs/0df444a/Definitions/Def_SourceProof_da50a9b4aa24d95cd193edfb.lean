-- Prove2me | Definitions.Def_SourceProof_da50a9b4aa24d95cd193edfb
-- name    : SourceProof_da50a9b4aa24d95cd193edfb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:38:54.555829+00:00
-- url     : https://prove2.me/theorems/6f48a1a9-e690-4680-9380-696711c4f3a5
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.memLp_elementaryIntegral_min_const

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Sampling_F000
import Definitions.Def_SourceProof_49660bd0ff7ae0f5dd4892ed
import Mathlib.MeasureTheory.Integral.Bochner.Basic

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

theorem _root_.Prove2MeSourceProof.h_da50a9b4aa24d95cd193edfb (hH : IsSimplePredictable H F)
    (hX : Martingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (T : ℝ≥0) (hXT : MemLp (X T) 2 P) (C : ℝ≥0) (hb : ∀ t ω, ‖H t ω‖ ≤ C) :
    MemLp (hH.elementaryIntegral (fun t ↦ X (min t T))) 2 P :=
  (_root_.Prove2MeSourceProof.h_49660bd0ff7ae0f5dd4892ed hH.choose) hX hF hr T hXT C (by simpa only [hH.choose_spec] using hb)
end IsSimplePredictable
end ProbabilityTheory


