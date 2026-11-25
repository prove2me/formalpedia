-- Prove2me | Definitions.Def_SourceProof_83e0b6f196e4f43fa027ce93
-- name    : SourceProof_83e0b6f196e4f43fa027ce93
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:49:55.279506+00:00
-- url     : https://prove2.me/theorems/14bd5d95-e93a-5144-8a88-3c5a8516d182
-- title:
--   StochLean source theorem: ProbabilityTheory.summable_abs_frechet_semimartingale_jump_remainders

import Definitions.Def_StochLean_Analysis_PathVariation_VectorEnergy_F000
import Definitions.Def_StochLean_ForMathlib_Analysis_FrechetTaylorCoefficient_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_ContinuousPart_F000
import Definitions.Def_SourceProof_30d0c59bde2d1c0616100b0f
import Definitions.Def_SourceProof_3b9e1eacb18faa84cc0222f4
import Definitions.Def_SourceProof_4d7fc7190a3d02a61bd44d4d
import Definitions.Def_SourceProof_56c71dd2079e6b44a7dc4950
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_889cc5878c88eebb9dbc02bf
import Mathlib.Topology.Compactness.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual vector Taylor jump series for coordinate semimartingales

Every assertion is on one common event for all finite horizons. The only
stochastic brackets used are the existing real coordinate quadratic variations.
-/

@[expose] public section

open MeasureTheory Set StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
  {X : ι → ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_83e0b6f196e4f43fa027ce93
    (hX : ∀ i, IsSemimartingale (X i) F P) (hF : F.IsUsual P)
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Summable (fun s : Ioc 0 t ↦
        |f (fun i ↦ X i s ω) - f (fun i ↦ leftLimitProcess (X i) s ω) -
          fderiv ℝ f (fun i ↦ leftLimitProcess (X i) s ω)
            (fun i ↦ jumpProcess (X i) s ω)|) ∧
      Summable (fun s : Ioc 0 t ↦
        |frechetSecondOrderRemainder f (fun i ↦ leftLimitProcess (X i) s ω)
          (fun i ↦ X i s ω)|) := by
  have hc := _root_.Prove2MeSourceProof.h_889cc5878c88eebb9dbc02bf (fun i ↦ (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 (hX i)))
  filter_upwards [hc, _root_.Prove2MeSourceProof.h_30d0c59bde2d1c0616100b0f hX hF]
    with ω hx hs t
  have hl (s : Ioc 0 t) : Function.leftLim (fun u i ↦ X i u ω) s =
      fun i ↦ ProbabilityTheory.leftLimitProcess (X i) s ω := by
    rw [(_root_.Prove2MeSourceProof.h_3b9e1eacb18faa84cc0222f4 hx)]
    funext i
    simp only [ProbabilityTheory.leftLimitProcess, if_neg (ne_of_gt s.2.1)]
  have hj (s : Ioc 0 t) : (fun i ↦ X i s ω) - Function.leftLim (fun u i ↦ X i u ω) s =
      fun i ↦ ProbabilityTheory.jumpProcess (X i) s ω := by
    rw [hl]
    rfl
  have hs' : Summable (fun s : Ioc 0 t ↦
      ‖(fun i ↦ X i s ω) - Function.leftLim (fun u i ↦ X i u ω) s‖ ^ 2) := by
    simpa only [hj] using hs t
  have hj' (s : Ioc 0 t) : (fun i ↦ X i s ω) - (fun i ↦ ProbabilityTheory.leftLimitProcess (X i) s ω) =
      fun i ↦ ProbabilityTheory.jumpProcess (X i) s ω := rfl
  constructor
  · simpa only [hl, hj'] using _root_.Prove2MeSourceProof.h_56c71dd2079e6b44a7dc4950 hx hs' hf
  · simpa only [hl] using _root_.Prove2MeSourceProof.h_4d7fc7190a3d02a61bd44d4d hx hs' hf
end ProbabilityTheory


