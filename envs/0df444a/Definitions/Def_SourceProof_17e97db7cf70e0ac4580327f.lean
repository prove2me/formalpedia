-- Prove2me | Definitions.Def_SourceProof_17e97db7cf70e0ac4580327f
-- name    : SourceProof_17e97db7cf70e0ac4580327f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T07:59:10.556407+00:00
-- url     : https://prove2.me/theorems/27e5572b-0748-46df-b4b6-1ee921fb9f88
-- title:
--   StochLean source theorem: StochLean.integrableOn_positiveVariationStieltjes

import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F002
import Definitions.Def_SourceProof_4c96a642af2c2b9a1811dd30
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

theorem _root_.Prove2MeSourceProof.h_17e97db7cf70e0ac4580327f
    (hf : IntegrableOn f (Ioc s t) (totalVariationStieltjes x hx hr).measure) :
    IntegrableOn f (Ioc s t) (positiveVariationStieltjes x hx hr).measure :=
  hf.mono_measure (_root_.Prove2MeSourceProof.h_4c96a642af2c2b9a1811dd30 x hx hr)
end StochLean


