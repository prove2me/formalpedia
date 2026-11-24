-- Prove2me | Definitions.Def_StochLean_ForMathlib_Analysis_FrechetTaylorCoefficient_F000
-- name    : StochLean_ForMathlib_Analysis_FrechetTaylorCoefficient_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T15:01:57.856945+00:00
-- url     : https://prove2.me/theorems/235511c5-b412-4444-89fb-0c45e50722e3
-- title:
--   StochLean: ForMathlib.Analysis.FrechetTaylorCoefficient F000

import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Topology.Order.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # A continuous diagonal-zero coefficient for the Frechet Taylor error

Dividing the actual second-order error by the squared increment norm gives
a coefficient continuous even on the diagonal. This makes the jump-separation
argument applicable to vector paths without a discontinuous directional choice.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace StochLean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}

noncomputable def frechetSecondOrderRemainder (f : E → ℝ) (a b : E) : ℝ :=
  f b - f a - fderiv ℝ f a (b - a) -
    (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) a (b - a) (b - a)
noncomputable def frechetTaylorErrorCoefficient (f : E → ℝ) (a b : E) : ℝ :=
  frechetSecondOrderRemainder f a b / ‖b - a‖ ^ 2
end StochLean


