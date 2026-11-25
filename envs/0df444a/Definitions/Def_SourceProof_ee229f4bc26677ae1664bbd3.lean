-- Prove2me | Definitions.Def_SourceProof_ee229f4bc26677ae1664bbd3
-- name    : SourceProof_ee229f4bc26677ae1664bbd3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:46:10.278225+00:00
-- url     : https://prove2.me/theorems/ea7d2ed8-ec17-5ac4-a15d-2b1032c90c0a
-- title:
--   StochLean source theorem: StochLean.abs_jump_le_tsum_abs_jumps

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegralJump_F000
import Definitions.Def_SourceProof_7628ddd4203b7ca1650800e5
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Countable support and absolute summability of FV jumps

The actual positive and negative Stieltjes measures control the jumps. No
enumeration of jumps or summability assumption is supplied by the caller.
-/

@[expose] public section

open MeasureTheory Set Function
open scoped NNReal

namespace StochLean

variable {x : ℝ≥0 → ℝ} (hv : LocallyBoundedVariationOn x univ)
  (hr : ∀ t, ContinuousWithinAt x (Ici t) t)

include hv hr

theorem _root_.Prove2MeSourceProof.h_ee229f4bc26677ae1664bbd3 (T : ℝ≥0) (t : Ioc 0 T) :
    |x t - leftLim x t| ≤ ∑' s : Ioc 0 T, |x s - leftLim x s| := by
  have h := (_root_.Prove2MeSourceProof.h_7628ddd4203b7ca1650800e5 hv hr T).sum_le_tsum
    {t} (fun _ _ ↦ abs_nonneg _)
  simpa only [Finset.sum_singleton] using h
end StochLean


