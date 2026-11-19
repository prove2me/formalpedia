-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_TaylorTwoVector_F000
-- name    : LevyStochCalc_Brownian_TaylorTwoVector_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:43:27.776228+00:00
-- url     : https://prove2.me/theorems/e8a91908-17a1-4c10-9ff5-3ec6ac138c9a
-- title:
--   Source declarations: LevyStochCalc.Brownian.TaylorTwoVector
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.TaylorTwoVector. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_TaylorTwo_F000
import Definitions.Def_LevyStochCalc_Brownian_TaylorTwo_F001
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The second-order Taylor bound on a normed space

For a real function on a normed space whose second derivative is Lipschitz, the second-order
Taylor remainder at a point is cubic in the increment. The bound follows from the scalar case
along the segment joining the two points.

## Main statements

* `LevyStochCalc.abs_sub_taylor_two_le_normed` — the pointwise cubic bound.
* `LevyStochCalc.taylorRemainderNormed` — the remainder along a sequence.
-/

namespace LevyStochCalc

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The second-order Taylor remainder of `f` along the first `m` steps of the sequence `x` in a
normed space. -/
noncomputable def taylorRemainderNormed (f : E → ℝ) (f' : E → E →L[ℝ] ℝ)
    (f'' : E → E →L[ℝ] E →L[ℝ] ℝ) (x : ℕ → E) (m : ℕ) : ℝ :=
  f (x m) - f (x 0)
    - ((∑ i ∈ Finset.range m, f' (x i) (x (i + 1) - x i))
      + ∑ i ∈ Finset.range m, f'' (x i) (x (i + 1) - x i) (x (i + 1) - x i) / 2)
end LevyStochCalc


