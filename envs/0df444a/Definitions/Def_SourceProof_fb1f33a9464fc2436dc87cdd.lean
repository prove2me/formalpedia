-- Prove2me | Definitions.Def_SourceProof_fb1f33a9464fc2436dc87cdd
-- name    : SourceProof_fb1f33a9464fc2436dc87cdd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:41.140848+00:00
-- url     : https://prove2.me/theorems/0e12d9c2-0985-47bf-9081-273442c9efc5
-- title:
--   StochLean source theorem: StochLean.variationStieltjes_measure_singleton_sub

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegralJump_F000
import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F002
import Definitions.Def_SourceProof_cdf76879721d1dc6620e7985
import Definitions.Def_SourceProof_dd764e40682425f1343ef671

open private leftLim_const_add_sub from Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegralJump_F000
/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Jumps of pathwise Stieltjes integrals at positive times

The source time-zero convention is dealt with separately at the process layer.
Positive-time jumps are obtained from actual atoms of the two component measures.
-/

@[expose] public section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

variable {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t} {f : ℝ≥0 → ℝ}

theorem _root_.Prove2MeSourceProof.h_fb1f33a9464fc2436dc87cdd {t : ℝ≥0} (ht : 0 < t) :
    ((positiveVariationStieltjes x hx hr).measure {t}).toReal -
      ((negativeVariationStieltjes x hx hr).measure {t}).toReal = x t - Function.leftLim x t := by
  let p := StochLean.positiveVariationStieltjes x hx hr
  let n := StochLean.negativeVariationStieltjes x hx hr
  have heq : x = fun u ↦ x 0 + p u - n u := by
    funext u
    have h := _root_.Prove2MeSourceProof.h_dd764e40682425f1343ef671 x u
    change p u - n u = x u - x 0 at h
    linarith
  have hl : Function.leftLim x t = x 0 + Function.leftLim p t - Function.leftLim n t := by
    calc
      _ = Function.leftLim (fun u ↦ x 0 + p u - n u) t :=
        congrArg (fun z ↦ Function.leftLim z t) heq
      _ = _ := leftLim_const_add_sub ht (x 0) (p.mono.tendsto_leftLim t) (n.mono.tendsto_leftLim t)
  rw [_root_.Prove2MeSourceProof.h_cdf76879721d1dc6620e7985, _root_.Prove2MeSourceProof.h_cdf76879721d1dc6620e7985, hl]
  have h := _root_.Prove2MeSourceProof.h_dd764e40682425f1343ef671 x t
  change p t - n t = x t - x 0 at h
  change (p t - Function.leftLim p t) - (n t - Function.leftLim n t) = _
  linarith
end StochLean


