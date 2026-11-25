-- Prove2me | Definitions.Def_SourceProof_f6f1afca5016f9c6b2d52e3e
-- name    : SourceProof_f6f1afca5016f9c6b2d52e3e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:57:18.51075+00:00
-- url     : https://prove2.me/theorems/3bea79d0-7967-40ae-a86e-8e4ab7a6036b
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.le_truncateSequence_terminal

import Definitions.Def_SourceProof_51b42fe979614c7284e94b09

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite capped partitions of an increasing stopping sequence

All `n` cells, including the first one, are retained. Stopping times may be infinite;
the finite cap gives everywhere-finite endpoints and repeated capped endpoints are legal.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

variable (τ : ℕ → Ω → WithTop ℝ≥0) (hτ : ∀ n, IsStoppingTime F (τ n))
  (hm : ∀ ω, Monotone (τ · ω)) (h0 : ∀ ω, τ 0 ω = 0) (n : ℕ) (T : ℝ≥0)

theorem _root_.Prove2MeSourceProof.h_f6f1afca5016f9c6b2d52e3e {t : ℝ≥0} {ω : Ω}
    (ht : t ≤ T) (hτt : (t : WithTop ℝ≥0) ≤ τ n ω) :
    t ≤ (truncateSequence τ hτ hm h0 n T).terminal ω := by
  apply WithTop.coe_le_coe.mp
  rw [_root_.Prove2MeSourceProof.h_51b42fe979614c7284e94b09]
  exact le_min (WithTop.coe_le_coe.mpr ht) hτt
end ProbabilityTheory.StoppingTimePartition


