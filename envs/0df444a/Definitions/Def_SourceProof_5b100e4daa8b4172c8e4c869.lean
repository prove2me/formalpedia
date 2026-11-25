-- Prove2me | Definitions.Def_SourceProof_5b100e4daa8b4172c8e4c869
-- name    : SourceProof_5b100e4daa8b4172c8e4c869
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:34:56.606883+00:00
-- url     : https://prove2.me/theorems/5079288b-9b3d-53d0-b271-d3dff1572065
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.integralProcess_stoppedProcess

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Stopping_F000
import Definitions.Def_SourceProof_5caa95db89fdd596c2cde105

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stopping the source elementary integral process

The integrator-stopping identity is pathwise even for an arbitrary raw random time,
possibly infinite. The integrand-cutoff identity additionally needs a stopping time
to keep the cutoff in the source simple predictable class. Cutoff is not frozen stopping.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep
theorem _root_.Prove2MeSourceProof.h_5b100e4daa8b4172c8e4c869 (H : SimplePredictableRep F)
    (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) :
    H.integralProcess (stoppedProcess X τ) = stoppedProcess (H.integralProcess X) τ := by
  funext t ω
  cases hτ : τ ω with
  | top =>
    have hs (Y : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) : stoppedProcess Y τ s ω = Y s ω :=
      stoppedProcess_eq_of_le (by rw [hτ]; exact le_top)
    rw [hs]
    simp only [_root_.Prove2MeSourceProof.h_5caa95db89fdd596c2cde105, hs]
  | coe T =>
    have hs (Y : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) :
        stoppedProcess Y τ s ω = Y (min s T) ω := by
      change Y (min (s : WithTop ℝ≥0) (τ ω)).untopA ω = _
      rw [hτ, ← WithTop.coe_min]
      rfl
    rw [hs]
    simp only [_root_.Prove2MeSourceProof.h_5caa95db89fdd596c2cde105, hs, min_assoc]
    simp
end SimplePredictableRep

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


