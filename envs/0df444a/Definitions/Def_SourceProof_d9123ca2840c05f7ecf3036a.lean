-- Prove2me | Definitions.Def_SourceProof_d9123ca2840c05f7ecf3036a
-- name    : SourceProof_d9123ca2840c05f7ecf3036a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:51:30.080904+00:00
-- url     : https://prove2.me/theorems/6db6ad40-089b-5aa7-a13a-5b0529382b41
-- title:
--   StochLean source theorem: StochLean.integrableOn_variationStieltjes_jump

import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F002
import Definitions.Def_SourceProof_422cc6ea2faae9b6d41ad8b0
import Definitions.Def_SourceProof_e21230af6e77c0b6dfe0e73f
import Definitions.Def_SourceProof_ee229f4bc26677ae1664bbd3

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

theorem _root_.Prove2MeSourceProof.h_d9123ca2840c05f7ecf3036a (T : ℝ≥0) :
    IntegrableOn (fun t ↦ x t - leftLim x t) (Ioc 0 T)
      (totalVariationStieltjes x hv hr).measure := by
  apply _root_.Prove2MeSourceProof.h_e21230af6e77c0b6dfe0e73f
    (_root_.Prove2MeSourceProof.h_422cc6ea2faae9b6d41ad8b0 hv hr)
    (C := ∑' s : Ioc 0 T, |x s - leftLim x s|)
  intro t ht
  exact _root_.Prove2MeSourceProof.h_ee229f4bc26677ae1664bbd3 hv hr T ⟨t, ht⟩
end StochLean


