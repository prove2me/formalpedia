-- Prove2me | Definitions.Def_SourceProof_f40b7170db65e65ad7d3fbe4
-- name    : SourceProof_f40b7170db65e65ad7d3fbe4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:35:26.654689+00:00
-- url     : https://prove2.me/theorems/7765e45b-5a97-44e4-adc4-5f2ecd7b225d
-- title:
--   StochLean source theorem: ProbabilityTheory.IsContinuousLocalMartingale.congr

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_SourceProof_a02883e32df61ba595b3947d
import Definitions.Def_SourceProof_a2f6eccafa4fd5a29354c02c
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
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

namespace IsContinuousLocalMartingale
theorem _root_.Prove2MeSourceProof.h_f40b7170db65e65ad7d3fbe4 (hX : IsContinuousLocalMartingale X F P)
    (hF : F.IsUsual P) (ha : Adapted F Y) (he : Indistinguishable X Y P) :
    IsContinuousLocalMartingale Y F P :=
  ⟨(_root_.Prove2MeSourceProof.h_a02883e32df61ba595b3947d hX.1) hF ha he, (fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_a2f6eccafa4fd5a29354c02c p2mMethodArg0 hX.2) he⟩
end IsContinuousLocalMartingale

end ProbabilityTheory


