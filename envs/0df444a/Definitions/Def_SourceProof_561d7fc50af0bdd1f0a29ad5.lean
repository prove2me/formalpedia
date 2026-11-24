-- Prove2me | Definitions.Def_SourceProof_561d7fc50af0bdd1f0a29ad5
-- name    : SourceProof_561d7fc50af0bdd1f0a29ad5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:14.897672+00:00
-- url     : https://prove2.me/theorems/f7a182d1-9ad8-4061-bc94-1a6fe5ee6afc
-- title:
--   StochLean source theorem: StochLean.stieltjesMeasure_Iic_nnreal

import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F002
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.GiryMonad

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurable families of locally finite Stieltjes measures on nonnegative time

Unlike the probability-CDF result on the real line, this result imposes no
normalization or finite total mass. Finite initial-interval restrictions suffice.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_561d7fc50af0bdd1f0a29ad5 (f : StieltjesFunction ℝ≥0) (t : ℝ≥0) :
    f.measure (Iic t) = ENNReal.ofReal (f t - f 0) := by
  rw [← Icc_bot, StieltjesFunction.measure_Icc]
  change ENNReal.ofReal (f t - Function.leftLim f 0) = _
  rw [leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from fun _ ↦ bot_le)]
end StochLean


