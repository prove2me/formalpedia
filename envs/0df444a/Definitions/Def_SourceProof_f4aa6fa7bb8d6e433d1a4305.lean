-- Prove2me | Definitions.Def_SourceProof_f4aa6fa7bb8d6e433d1a4305
-- name    : SourceProof_f4aa6fa7bb8d6e433d1a4305
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:32:40.016474+00:00
-- url     : https://prove2.me/theorems/ede42cf8-165d-5dc5-8869-b757497fdacb
-- title:
--   StochLean source theorem: ProbabilityTheory.IsContinuousLocalMartingale.sub_initial

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_InitialValue_F000
import Definitions.Def_SourceProof_5c813e4c8eaef1522b4ff90a
import Definitions.Def_SourceProof_6c194a6862825607b665066e
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Bounded localization of continuous local martingales

Klenke 21.67 is used with its necessary initial-value guard. Closed-level hitting times of an
everywhere-continuous indistinguishable version give actual monotone localizers. The original
process is bounded after stopping on one common full-measure event, not just at fixed times.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

namespace IsContinuousLocalMartingale

theorem _root_.Prove2MeSourceProof.h_f4aa6fa7bb8d6e433d1a4305 (hX : IsContinuousLocalMartingale X F P)
    (hF : F.IsUsual P) :
    IsContinuousLocalMartingale (fun t ω ↦ X t ω - X 0 ω) F P := by
  refine ⟨(_root_.Prove2MeSourceProof.h_5c813e4c8eaef1522b4ff90a hX.1) (_root_.Prove2MeSourceProof.h_6c194a6862825607b665066e (hX.1.1 0)).1 hF, ?_⟩
  filter_upwards [hX.2] with ω hω
  exact hω.sub continuous_const
end IsContinuousLocalMartingale

end ProbabilityTheory


