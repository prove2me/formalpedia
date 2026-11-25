-- Prove2me | Definitions.Def_SourceProof_e01319e635365a8c8bc9744b
-- name    : SourceProof_e01319e635365a8c8bc9744b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:49:42.447559+00:00
-- url     : https://prove2.me/theorems/368254ff-b3d0-4026-b449-d3a386b59a30
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.integral_sq_integral_min_const_le

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Sampling_F000
import Definitions.Def_SourceProof_7d58eb4e8ca0b9afe6bb32b4
import Definitions.Def_SourceProof_a9c44e06617a4753cffd0417
import Definitions.Def_SourceProof_aa05bbbbd7a39bd6fd18d38a
import Definitions.Def_SourceProof_ac7ce9a51c9b630bf39062ad
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

theorem _root_.Prove2MeSourceProof.h_e01319e635365a8c8bc9744b (H : SimplePredictableRep F)
    (hX : Martingale X F P) (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (T : ℝ≥0) (hXT : MemLp (X T) 2 P) (C : ℝ≥0)
    (hb : ∀ t ω, ‖H.toProcess t ω‖ ≤ C) :
    ∫ ω, (H.integral (fun t ↦ X (min t T)) ω) ^ 2 ∂P ≤
      (C : ℝ) ^ 2 * ∫ ω, (X T ω) ^ 2 ∂P := by
  rw [← (_root_.Prove2MeSourceProof.h_ac7ce9a51c9b630bf39062ad H)]
  exact (_root_.Prove2MeSourceProof.h_aa05bbbbd7a39bd6fd18d38a H.removeEmptyIntervals) hX hF hr T hXT C
    (fun ω ↦ by
      change ‖H.initial ω‖ ≤ (C : ℝ)
      simpa only [_root_.Prove2MeSourceProof.h_a9c44e06617a4753cffd0417] using hb 0 ω)
    ((_root_.Prove2MeSourceProof.h_7d58eb4e8ca0b9afe6bb32b4 H) C.coe_nonneg hb)
end SimplePredictableRep

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


