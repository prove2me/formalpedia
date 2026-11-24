-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F002
-- name    : StochLean_Analysis_PathVariation_Stieltjes_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:00.629199+00:00
-- url     : https://prove2.me/theorems/9aebffff-191c-4771-b136-dfdec181ab04
-- title:
--   StochLean: Analysis.PathVariation.Stieltjes F002

import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F001
import Definitions.Def_SourceProof_1b364b3ac1881eb32ea6aaf9
import Definitions.Def_SourceProof_3c6a77962047238919981f55
import Definitions.Def_SourceProof_7d2787f4ad27ed704ba3ff83
import Definitions.Def_SourceProof_b929c4bb83943309aff34d46

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stieltjes components of a right-continuous locally BV path

Only Mathlib variation and Stieltjes measures are used. The components start at
zero and represent increments after time zero. The initial value is retained
separately in the reconstruction identity; it is not inserted into an unsigned
measure when it may be negative. Local BV is not mistaken for global finite mass.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace StochLean

noncomputable def totalVariationStieltjes (x : ℝ≥0 → ℝ)
    (hx : LocallyBoundedVariationOn x univ) (hr : ∀ t, ContinuousWithinAt x (Ici t) t) :
    StieltjesFunction ℝ≥0 where
  toFun := pathTotalVariation x
  mono' := _root_.Prove2MeSourceProof.h_7d2787f4ad27ed704ba3ff83 hx
  right_continuous' := _root_.Prove2MeSourceProof.h_b929c4bb83943309aff34d46 hx hr
noncomputable def positiveVariationStieltjes (x : ℝ≥0 → ℝ)
    (hx : LocallyBoundedVariationOn x univ) (hr : ∀ t, ContinuousWithinAt x (Ici t) t) :
    StieltjesFunction ℝ≥0 where
  toFun := pathPositiveVariation x
  mono' := _root_.Prove2MeSourceProof.h_3c6a77962047238919981f55 hx
  right_continuous' := fun t ↦ by
    have hv := _root_.Prove2MeSourceProof.h_b929c4bb83943309aff34d46 hx hr t
    exact ((hv.add (hr t)).sub_const (x 0)).div_const 2
noncomputable def negativeVariationStieltjes (x : ℝ≥0 → ℝ)
    (hx : LocallyBoundedVariationOn x univ) (hr : ∀ t, ContinuousWithinAt x (Ici t) t) :
    StieltjesFunction ℝ≥0 where
  toFun := pathNegativeVariation x
  mono' := _root_.Prove2MeSourceProof.h_1b364b3ac1881eb32ea6aaf9 hx
  right_continuous' := fun t ↦ by
    have hv := _root_.Prove2MeSourceProof.h_b929c4bb83943309aff34d46 hx hr t
    exact ((hv.sub (hr t)).add_const (x 0)).div_const 2
end StochLean


