-- Prove2me | Definitions.Def_SourceProof_0e9a3c1ecba0183e8cff41a4
-- name    : SourceProof_0e9a3c1ecba0183e8cff41a4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T07:59:03.751047+00:00
-- url     : https://prove2.me/theorems/df7b60a1-c3f7-495c-9cc4-607dbad3a158
-- title:
--   StochLean source theorem: StochLean.integrableOn_negativeVariationStieltjes

import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F002
import Definitions.Def_SourceProof_1ef5b6976ba2a56deb7b7a9a
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite-horizon integration against a locally BV path

The increment integral on `(s,t]` is the difference of integrals against the
canonical positive and negative Stieltjes components. Integrability is measured
against their sum, the total-variation measure. The source integral from time
zero additionally contains `f 0 * x 0`; this is not a measure atom.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace StochLean

variable (x : ℝ≥0 → ℝ) (hx : LocallyBoundedVariationOn x univ)
  (hr : ∀ t, ContinuousWithinAt x (Ici t) t)

variable {x hx hr} {f g : ℝ≥0 → ℝ} {s t : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_0e9a3c1ecba0183e8cff41a4
    (hf : IntegrableOn f (Ioc s t) (totalVariationStieltjes x hx hr).measure) :
    IntegrableOn f (Ioc s t) (negativeVariationStieltjes x hx hr).measure :=
  hf.mono_measure (_root_.Prove2MeSourceProof.h_1ef5b6976ba2a56deb7b7a9a x hx hr)
end StochLean


