-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegral_F000
-- name    : StochLean_Analysis_PathVariation_StieltjesIntegral_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:14:36.191651+00:00
-- url     : https://prove2.me/theorems/7b10b445-210f-4af0-b187-d2d6eea43006
-- title:
--   StochLean: Analysis.PathVariation.StieltjesIntegral F000

import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F002
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

noncomputable def pathStieltjesIncrementIntegral (f : ℝ≥0 → ℝ) (s t : ℝ≥0) : ℝ :=
  (∫ u in Ioc s t, f u ∂(positiveVariationStieltjes x hx hr).measure) -
    ∫ u in Ioc s t, f u ∂(negativeVariationStieltjes x hx hr).measure
noncomputable def pathStieltjesIntegral (f : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  f 0 * x 0 + pathStieltjesIncrementIntegral x hx hr f 0 t
variable {x hx hr} {f g : ℝ≥0 → ℝ} {s t : ℝ≥0}

end StochLean


