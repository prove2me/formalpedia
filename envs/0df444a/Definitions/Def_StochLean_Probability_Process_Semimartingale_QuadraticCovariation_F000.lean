-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticCovariation_F000
-- name    : StochLean_Probability_Process_Semimartingale_QuadraticCovariation_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:06:20.366952+00:00
-- url     : https://prove2.me/theorems/99549880-c57d-453b-a096-71e3adc1b8a8
-- title:
--   StochLean: Probability.Process.Semimartingale.QuadraticCovariation F000

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_F000
import Definitions.Def_SourceProof_31d0de13ef1656df97c05a7d
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Data.Finset.Sort
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.UniformSpace.UniformApproximation

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Raw quadratic covariation by polarization of the canonical square bracket

This is the design's sole mixed bracket owner. It retains `X₀ Y₀`, is adapted
and cadlag, and has locally finite-variation paths. It is not asserted to be
increasing and is not a predictable compensator bracket.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

noncomputable def IsSemimartingale.quadraticCovariation
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    ℝ≥0 → Ω → ℝ := fun t ω ↦ (1 / 2 : ℝ) *
      (((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hX) hY).quadraticVariation hF t ω - hX.quadraticVariation hF t ω -
        hY.quadraticVariation hF t ω)
end ProbabilityTheory


