-- Prove2me | Definitions.Def_SourceProof_9fcb638ec84cd76ccac67258
-- name    : SourceProof_9fcb638ec84cd76ccac67258
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:23:37.893206+00:00
-- url     : https://prove2.me/theorems/50cba593-5b3d-40a2-9928-aebe5d953098
-- title:
--   LevyStochCalc source proof: LevyStochCalc.abs_sub_taylor_two_le_normed
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

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


theorem _root_.Prove2MeSourceProof.h_9fcb638ec84cd76ccac67258 {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hf'' : ∀ z w, ‖f'' z - f'' w‖ ≤ K * ‖z - w‖) (x y : E) :
    |f y - f x - f' x (y - x) - f'' x (y - x) (y - x) / 2| ≤ K * ‖y - x‖ ^ 3 := by
  set v : E := y - x with hv
  have hseg : ∀ t : ℝ, HasDerivAt (fun r : ℝ => x + r • v) v t := fun t => by
    have h := ((hasDerivAt_id t).smul_const v).const_add x
    simpa using h
  have hg : ∀ t : ℝ, HasDerivAt (fun r : ℝ => f (x + r • v)) (f' (x + t • v) v) t := fun t =>
    (hf (x + t • v)).comp_hasDerivAt t (hseg t)
  have hg' : ∀ t : ℝ,
      HasDerivAt (fun r : ℝ => f' (x + r • v) v) (f'' (x + t • v) v v) t := fun t => by
    have hap : HasFDerivAt (fun z : E => f' z v)
        ((ContinuousLinearMap.apply ℝ ℝ v).comp (f'' (x + t • v))) (x + t • v) :=
      (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp _ (hf' (x + t • v))
    exact hap.comp_hasDerivAt t (hseg t)
  have hlip : ∀ u w : ℝ, |f'' (x + u • v) v v - f'' (x + w • v) v v|
      ≤ (K * ‖v‖ ^ 3) * |u - w| := by
    intro u w
    have hsub : f'' (x + u • v) v v - f'' (x + w • v) v v = (f'' (x + u • v) - f'' (x + w • v)) v v
      := by simp
    have hbd : ‖(f'' (x + u • v) - f'' (x + w • v)) v v‖
        ≤ ‖f'' (x + u • v) - f'' (x + w • v)‖ * ‖v‖ * ‖v‖ :=
      ContinuousLinearMap.le_opNorm₂ _ v v
    have hd : ‖(x + u • v) - (x + w • v)‖ = |u - w| * ‖v‖ := by
      have : (x + u • v) - (x + w • v) = (u - w) • v := by module
      rw [this, norm_smul, Real.norm_eq_abs]
    have hK := hf'' (x + u • v) (x + w • v)
    rw [hd] at hK
    calc |f'' (x + u • v) v v - f'' (x + w • v) v v|
        = ‖(f'' (x + u • v) - f'' (x + w • v)) v v‖ := by rw [hsub]; exact (Real.norm_eq_abs _).symm
      _ ≤ ‖f'' (x + u • v) - f'' (x + w • v)‖ * ‖v‖ * ‖v‖ := hbd
      _ ≤ (K * (|u - w| * ‖v‖)) * ‖v‖ * ‖v‖ := by
          gcongr
      _ = (K * ‖v‖ ^ 3) * |u - w| := by ring
  have hmain := _root_.Prove2MeSourceProof.h_5da8457f4c66732a5c2f52e6 (f := fun r : ℝ => f (x + r • v))
    (f' := fun r : ℝ => f' (x + r • v) v) (f'' := fun r : ℝ => f'' (x + r • v) v v)
    (K := K * ‖v‖ ^ 3) (by positivity) hg hg' hlip 0 1
  simpa [hv] using hmain
end LevyStochCalc


