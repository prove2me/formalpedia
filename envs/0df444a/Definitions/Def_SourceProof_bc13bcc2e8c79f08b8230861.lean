-- Prove2me | Definitions.Def_SourceProof_bc13bcc2e8c79f08b8230861
-- name    : SourceProof_bc13bcc2e8c79f08b8230861
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:52:18.278097+00:00
-- url     : https://prove2.me/theorems/b998ad72-4998-54c2-908d-a27f7396c312
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSimplePredictable.integral_sq_elementaryIntegral_min_const_le

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Sampling_F000
import Definitions.Def_SourceProof_e01319e635365a8c8bc9744b
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

theorem _root_.Prove2MeSourceProof.h_bc13bcc2e8c79f08b8230861 (hH : IsSimplePredictable H F)
    (hX : Martingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (T : ℝ≥0) (hXT : MemLp (X T) 2 P) (C : ℝ≥0) (hb : ∀ t ω, ‖H t ω‖ ≤ C) :
    ∫ ω, (hH.elementaryIntegral (fun t ↦ X (min t T)) ω) ^ 2 ∂P ≤
      (C : ℝ) ^ 2 * ∫ ω, (X T ω) ^ 2 ∂P :=
  (_root_.Prove2MeSourceProof.h_e01319e635365a8c8bc9744b hH.choose) hX hF hr T hXT C
    (by simpa only [hH.choose_spec] using hb)
end IsSimplePredictable
end ProbabilityTheory


