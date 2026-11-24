-- Prove2me | Definitions.Def_SourceProof_82c6d1dbda060237d4fd2c23
-- name    : SourceProof_82c6d1dbda060237d4fd2c23
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:13:35.904258+00:00
-- url     : https://prove2.me/theorems/12313c3c-dd4f-4157-a7be-2250340060e1
-- title:
--   StochLean source theorem: StochLean.countable_support_jump_of_locallyBoundedVariation

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegralJump_F000
import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F002
import Definitions.Def_SourceProof_fb1f33a9464fc2436dc87cdd
import Definitions.Def_SourceProof_fc5f89aed67e82971b1326cd
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Real

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

theorem _root_.Prove2MeSourceProof.h_82c6d1dbda060237d4fd2c23 :
    (support (fun t ↦ x t - leftLim x t)).Countable := by
  let p := StochLean.positiveVariationStieltjes x hv hr
  let n := StochLean.negativeVariationStieltjes x hv hr
  apply ((_root_.Prove2MeSourceProof.h_fc5f89aed67e82971b1326cd p.measure).union (_root_.Prove2MeSourceProof.h_fc5f89aed67e82971b1326cd n.measure)).mono
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    exact False.elim (ht (by
      change x 0 - leftLim x 0 = 0
      rw [leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from fun _ ↦ bot_le), sub_self]))
  · by_contra h
    have hz : p.measure {t} = 0 ∧ n.measure {t} = 0 := by
      simpa only [mem_union, StochLean.pointAtomSet, mem_ofPred_eq, not_or, not_not] using h
    have he := _root_.Prove2MeSourceProof.h_fb1f33a9464fc2436dc87cdd (hx := hv) (hr := hr)
      (pos_iff_ne_zero.mpr ht0)
    change (p.measure {t}).toReal - (n.measure {t}).toReal = x t - leftLim x t at he
    rw [hz.1, hz.2, ENNReal.toReal_zero, sub_self] at he
    exact ht he.symm
end StochLean


