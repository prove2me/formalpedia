-- Prove2me | Definitions.Def_SourceProof_f84942774fa9217e287c6136
-- name    : SourceProof_f84942774fa9217e287c6136
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:36:47.002616+00:00
-- url     : https://prove2.me/theorems/e5fc6dd0-adaa-5729-8a2e-3f37fd900104
-- title:
--   StochLean source theorem: ProbabilityTheory.IsContinuousLocalMartingale.exists_bounded_centered_localizingSequence

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_InitialValue_F000
import Definitions.Def_SourceProof_2c97b0da88fd3eb21715f5f0
import Definitions.Def_SourceProof_e79cc5d7fc8aa48d10e205ad
import Definitions.Def_SourceProof_f4aa6fa7bb8d6e433d1a4305
import Definitions.Def_SourceProof_fd09713ebd8a3264a1935dfd
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

theorem _root_.Prove2MeSourceProof.h_f84942774fa9217e287c6136
    (hX : IsContinuousLocalMartingale X F P) (hF : F.IsUsual P) :
    ∃ τ : ℕ → Ω → WithTop ℝ≥0,
      IsKlenkeLocalizingSequence (fun t ω ↦ X t ω - X 0 ω) F P τ ∧
      ∀ n, (∀ᵐ ω ∂P, ∀ t,
        ‖MeasureTheory.stoppedProcess (fun s ω ↦ X s ω - X 0 ω) (τ n) t ω‖ ≤ (n : ℝ)) ∧
        IsSquareIntegrableMartingale
          (MeasureTheory.stoppedProcess (fun s ω ↦ X s ω - X 0 ω) (τ n)) F P := by
  simpa only [NNReal.coe_zero, zero_add] using
    (_root_.Prove2MeSourceProof.h_fd09713ebd8a3264a1935dfd ((_root_.Prove2MeSourceProof.h_f4aa6fa7bb8d6e433d1a4305 hX) hF)) hF 0
      (ae_of_all _ fun _ ↦ by simp)
end IsContinuousLocalMartingale

end ProbabilityTheory


