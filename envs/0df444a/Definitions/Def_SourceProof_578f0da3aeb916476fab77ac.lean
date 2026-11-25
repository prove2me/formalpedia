-- Prove2me | Definitions.Def_SourceProof_578f0da3aeb916476fab77ac
-- name    : SourceProof_578f0da3aeb916476fab77ac
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T22:04:19.330986+00:00
-- url     : https://prove2.me/theorems/18186e13-bb70-5977-b598-1ad3e649a0c5
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.summable_abs_contDiff_second_order_jump_remainders

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_ContinuousPart_F000
import Definitions.Def_SourceProof_472bb0fb2e5ea3f0d733b6e5
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_8715d5ca16e616ee0eee368f
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual absolute jump-remainder series for C2 semimartingale calculus

The conclusion holds on a common event for all finite horizons. It uses
the square-summable jumps of the original raw bracket, not FV paths of X.
-/

@[expose] public section

open MeasureTheory Set StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {f : ℝ → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_578f0da3aeb916476fab77ac
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hf : ContDiff ℝ 2 f) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Summable (fun s : Ioc 0 t ↦
      |f (X s ω) - f (leftLimitProcess X s ω) -
        deriv f (leftLimitProcess X s ω) * jumpProcess X s ω -
        deriv (deriv f) (leftLimitProcess X s ω) / 2 * (jumpProcess X s ω) ^ 2|) := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX), (_root_.Prove2MeSourceProof.h_472bb0fb2e5ea3f0d733b6e5 hX) hF] with ω hx hs t
  have he (s : Ioc 0 t) : ProbabilityTheory.leftLimitProcess X s ω = Function.leftLim (X · ω) s := by
    simp only [ProbabilityTheory.leftLimitProcess, if_neg (ne_of_gt s.2.1)]
  have hsq : Summable (fun s : Ioc 0 t ↦ (X s ω - Function.leftLim (X · ω) s) ^ 2) := by
    simpa only [ProbabilityTheory.jumpProcess, Pi.sub_apply, he] using hs t
  simpa only [ProbabilityTheory.jumpProcess, Pi.sub_apply, he] using
    _root_.Prove2MeSourceProof.h_8715d5ca16e616ee0eee368f hx hsq hf
end IsSemimartingale

end ProbabilityTheory


