-- Prove2me | Definitions.Def_SourceProof_26cd731c94161b868cf2046b
-- name    : SourceProof_26cd731c94161b868cf2046b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:21:22.068818+00:00
-- url     : https://prove2.me/theorems/4e613fc3-d28d-409c-80d5-4003ea148146
-- title:
--   StochLean source theorem: StochLean.variationStieltjes_jump_sub

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegralJump_F000
import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F002
import Definitions.Def_SourceProof_cdf76879721d1dc6620e7985
import Definitions.Def_SourceProof_fb1f33a9464fc2436dc87cdd
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

theorem _root_.Prove2MeSourceProof.h_26cd731c94161b868cf2046b {t : ℝ≥0} (ht : 0 < t) :
    (positiveVariationStieltjes x hv hr t - leftLim (positiveVariationStieltjes x hv hr) t) -
      (negativeVariationStieltjes x hv hr t - leftLim (negativeVariationStieltjes x hv hr) t) =
      x t - leftLim x t := by
  simpa only [_root_.Prove2MeSourceProof.h_cdf76879721d1dc6620e7985] using
    (_root_.Prove2MeSourceProof.h_fb1f33a9464fc2436dc87cdd (hx := hv) (hr := hr) ht)
end StochLean


