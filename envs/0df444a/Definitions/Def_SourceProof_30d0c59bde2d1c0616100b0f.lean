-- Prove2me | Definitions.Def_SourceProof_30d0c59bde2d1c0616100b0f
-- name    : SourceProof_30d0c59bde2d1c0616100b0f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:42:34.493863+00:00
-- url     : https://prove2.me/theorems/f418424e-194b-48af-b1b6-70ebf64970b7
-- title:
--   StochLean source theorem: ProbabilityTheory.summable_norm_sq_semimartingale_coordinate_jumps

import Definitions.Def_StochLean_Analysis_PathVariation_VectorEnergy_F000
import Definitions.Def_SourceProof_22dfd694bd9e533ba03d52f6
import Definitions.Def_SourceProof_472bb0fb2e5ea3f0d733b6e5
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Basic

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

theorem _root_.Prove2MeSourceProof.h_30d0c59bde2d1c0616100b0f
    (hX : ∀ i, IsSemimartingale (X i) F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Summable (fun s : Ioc 0 t ↦ ‖fun i ↦ jumpProcess (X i) s ω‖ ^ 2) := by
  have h : ∀ᵐ ω ∂P, ∀ i, ∀ t : ℝ≥0,
      Summable (fun s : Ioc 0 t ↦ (ProbabilityTheory.jumpProcess (X i) s ω) ^ 2) :=
    ae_all_iff.mpr (fun i ↦ (_root_.Prove2MeSourceProof.h_472bb0fb2e5ea3f0d733b6e5 (hX i)) hF)
  filter_upwards [h] with ω hω t
  exact _root_.Prove2MeSourceProof.h_22dfd694bd9e533ba03d52f6
    (fun (s : Ioc 0 t) i ↦ ProbabilityTheory.jumpProcess (X i) s ω) (fun i ↦ hω i t)
end ProbabilityTheory


