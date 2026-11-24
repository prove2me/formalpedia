-- Prove2me | Definitions.Def_SourceProof_54540bbaa62044e454e749e1
-- name    : SourceProof_54540bbaa62044e454e749e1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:27:20.851273+00:00
-- url     : https://prove2.me/theorems/ae397817-68b7-4521-8a0e-4970fc3cecb4
-- title:
--   StochLean source theorem: StochLean.measurable_stieltjesMeasure_restrict_Iic

import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F002
import Definitions.Def_SourceProof_cea06ce35b1a746f3e8af6f7
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

theorem _root_.Prove2MeSourceProof.h_54540bbaa62044e454e749e1 {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → StieltjesFunction ℝ≥0} (hf : ∀ t, Measurable fun ω ↦ f ω t) (T : ℝ≥0) :
    Measurable fun ω ↦ (f ω).measure.restrict (Iic T) :=
  _root_.Prove2MeSourceProof.h_cea06ce35b1a746f3e8af6f7 T (fun t _ ↦ hf t)
end StochLean


