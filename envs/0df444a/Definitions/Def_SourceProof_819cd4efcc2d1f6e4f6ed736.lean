-- Prove2me | Definitions.Def_SourceProof_819cd4efcc2d1f6e4f6ed736
-- name    : SourceProof_819cd4efcc2d1f6e4f6ed736
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:18.146259+00:00
-- url     : https://prove2.me/theorems/c88735cb-5eda-4f6d-8977-98076999ea7d
-- title:
--   StochLean source theorem: StochLean.norm_pathStieltjesIncrementIntegral_le

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegral_F000
import Definitions.Def_SourceProof_22908da40768e213d2860fb4
import Definitions.Def_SourceProof_3234cdb3b753271f289ac706

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

theorem _root_.Prove2MeSourceProof.h_819cd4efcc2d1f6e4f6ed736 {C : ℝ}
    (hC : ∀ u ∈ Ioc s t, ‖f u‖ ≤ C) (hst : s ≤ t) :
    ‖pathStieltjesIncrementIntegral x hx hr f s t‖ ≤ C * (eVariationOn x (Icc s t)).toReal := by
  have hp := norm_setIntegral_le_of_norm_le_const
    (μ := (StochLean.positiveVariationStieltjes x hx hr).measure) measure_Ioc_lt_top hC
  have hn := norm_setIntegral_le_of_norm_le_const
    (μ := (StochLean.negativeVariationStieltjes x hx hr).measure) measure_Ioc_lt_top hC
  have hm : ((StochLean.positiveVariationStieltjes x hx hr).measure (Ioc s t)).toReal +
      ((StochLean.negativeVariationStieltjes x hx hr).measure (Ioc s t)).toReal =
        (eVariationOn x (Icc s t)).toReal := by
    rw [← ENNReal.toReal_add measure_Ioc_lt_top.ne measure_Ioc_lt_top.ne,
      ← Measure.add_apply, ← _root_.Prove2MeSourceProof.h_22908da40768e213d2860fb4,
      _root_.Prove2MeSourceProof.h_3234cdb3b753271f289ac706 x hx hr hst]
  calc
    ‖StochLean.pathStieltjesIncrementIntegral x hx hr f s t‖ ≤
        ‖∫ u in Ioc s t, f u ∂(StochLean.positiveVariationStieltjes x hx hr).measure‖ +
          ‖∫ u in Ioc s t, f u ∂(StochLean.negativeVariationStieltjes x hx hr).measure‖ := norm_sub_le _ _
    _ ≤ C * ((StochLean.positiveVariationStieltjes x hx hr).measure (Ioc s t)).toReal +
        C * ((StochLean.negativeVariationStieltjes x hx hr).measure (Ioc s t)).toReal := add_le_add hp hn
    _ = C * (eVariationOn x (Icc s t)).toReal := by rw [← mul_add, hm]
end StochLean


