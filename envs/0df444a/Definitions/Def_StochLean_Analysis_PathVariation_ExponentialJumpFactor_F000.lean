-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_ExponentialJumpFactor_F000
-- name    : StochLean_Analysis_PathVariation_ExponentialJumpFactor_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T13:11:15.913489+00:00
-- url     : https://prove2.me/theorems/da920aa1-d6c0-4597-af74-5b29cd5cd724
-- title:
--   StochLean: Analysis.PathVariation.ExponentialJumpFactor F000

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Order.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The jump factor of the Doleans--Dade exponential

Square summability implies absolute summability of the deviations from one.
This proves convergence of the actual product, including zero and negative
factors; logarithms are not taken across those exceptional factors.
-/

@[expose] public section

namespace StochLean

noncomputable def exponentialJumpFactor (u : ℝ) : ℝ := (1 + u) * Real.exp (-u)
end StochLean


