-- Prove2me | Definitions.Def_SourceProof_7628ddd4203b7ca1650800e5
-- name    : SourceProof_7628ddd4203b7ca1650800e5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:37:33.569961+00:00
-- url     : https://prove2.me/theorems/1d45d34d-0e8b-4d34-b2cc-d61975415939
-- title:
--   StochLean source theorem: StochLean.summable_abs_jumps_of_locallyBoundedVariation

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegralJump_F000
import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F002
import Definitions.Def_SourceProof_26cd731c94161b868cf2046b
import Definitions.Def_SourceProof_c3d82db2ca7eee09ee06d809
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

theorem _root_.Prove2MeSourceProof.h_7628ddd4203b7ca1650800e5 (T : ℝ≥0) :
    Summable (fun t : Ioc 0 T ↦ |x t - leftLim x t|) := by
  let p := StochLean.positiveVariationStieltjes x hv hr
  let n := StochLean.negativeVariationStieltjes x hv hr
  apply ((_root_.Prove2MeSourceProof.h_c3d82db2ca7eee09ee06d809 p T).add (_root_.Prove2MeSourceProof.h_c3d82db2ca7eee09ee06d809 n T)).of_norm_bounded
  intro t
  rw [Real.norm_eq_abs, abs_abs, ← _root_.Prove2MeSourceProof.h_26cd731c94161b868cf2046b hv hr t.2.1]
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (p.mono.leftLim_le le_rfl)),
    abs_of_nonneg (sub_nonneg.mpr (n.mono.leftLim_le le_rfl))] using
      norm_sub_le (p t - leftLim p t) (n t - leftLim n t)
end StochLean


