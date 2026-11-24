-- Prove2me | Definitions.Def_SourceProof_bdb573aab3428152bd91f0a3
-- name    : SourceProof_bdb573aab3428152bd91f0a3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:14:34.361417+00:00
-- url     : https://prove2.me/theorems/fb4e8ad4-35ad-4274-b9e6-cf0acaaac905
-- title:
--   StochLean source theorem: ProbabilityTheory.IsUIMartingale.congr

import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_SourceProof_4a9b239e53ad8f8a45b491f1
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Indistinguishable versions of the existing local-martingale predicates

The actual fundamental sequence is retained, including its initial masks.
Adaptedness of the target is explicit; no measurability of arbitrary versions
is silently assumed.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsUIMartingale
theorem _root_.Prove2MeSourceProof.h_bdb573aab3428152bd91f0a3 (hX : IsUIMartingale X F P)
    (ha : Adapted F Y) (he : Indistinguishable X Y P) : IsUIMartingale Y F P :=
  ⟨hX.1.congr ha.stronglyAdapted (_root_.Prove2MeSourceProof.h_4a9b239e53ad8f8a45b491f1 he), hX.2.ae_eq (_root_.Prove2MeSourceProof.h_4a9b239e53ad8f8a45b491f1 he)⟩
end IsUIMartingale

end ProbabilityTheory


