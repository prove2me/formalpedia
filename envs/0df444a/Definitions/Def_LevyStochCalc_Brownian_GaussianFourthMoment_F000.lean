-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_GaussianFourthMoment_F000
-- name    : LevyStochCalc_Brownian_GaussianFourthMoment_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:51:56.365487+00:00
-- url     : https://prove2.me/theorems/fc8f87a8-8909-4d9f-bd21-a7be2a11cc52
-- title:
--   Source declarations: LevyStochCalc.Brownian.GaussianFourthMoment
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.GaussianFourthMoment. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentIncrements_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentIncrements_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentIncrements_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The value of the standard Gaussian fourth moment

The fourth moment of a centred real Gaussian of variance `v` is `3 v²`
(`LevyStochCalc.Brownian.Continuity.gaussianReal_fourth_moment`), so at `v = 1` the constant
`gaussianFourthMoment` of `LevyStochCalc.Brownian.ItoFourthMomentIncrements` is `3`.

## Main statements

* `gaussianFourthMoment_eq_three` — `∫ x, x ^ 4 ∂(gaussianReal 0 1) = 3`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Ito

/-- The fourth moment of the standard real Gaussian distribution is `3`. -/
theorem gaussianFourthMoment_eq_three : gaussianFourthMoment = 3 := by
  have h := _root_.Prove2MeSourceProof.h_30c2a27da1025349f8d2b70b 1
  rw [gaussianFourthMoment, h]
  norm_num
end LevyStochCalc.Brownian.Ito


