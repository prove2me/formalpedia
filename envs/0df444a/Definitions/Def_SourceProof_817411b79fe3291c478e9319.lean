-- Prove2me | Definitions.Def_SourceProof_817411b79fe3291c478e9319
-- name    : SourceProof_817411b79fe3291c478e9319
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:27:09.93688+00:00
-- url     : https://prove2.me/theorems/d5868694-e40a-4539-a3b1-cf3d9611007c
-- title:
--   StochLean source theorem: StochLean.tprod_exponentialJumpFactor_eq_re_cexp_tsum_log_of_ne_zero

import Definitions.Def_SourceProof_61bad4bf4babd22e06805bca
import Definitions.Def_SourceProof_8324dac51fdbfa267964d2a0
import Definitions.Def_SourceProof_e53a0a54f0755719030aa5d3

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # A zero-guarded complex-log representation of the real jump product

The principal complex logarithm retains the sign of negative factors.
Its convergent exponential represents the real product only when every
factor is nonzero. A separately summable count of jumps of size -1 supplies
the zero guard. This representation is intended for measurability proofs,
not as a replacement for the canonical real product definition.
-/

@[expose] public section

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_817411b79fe3291c478e9319
    {ι : Type*} {u : ι → ℝ} (hu : Summable (fun i ↦ u i ^ 2))
    (hn : ∀ i, u i ≠ -1) :
    (∏' i, exponentialJumpFactor (u i)) =
      (Complex.exp (∑' i, Complex.log (exponentialJumpFactor (u i) : ℂ))).re := by
  have hfactor (i : ι) : (StochLean.exponentialJumpFactor (u i) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact fun hz ↦ hn i ((_root_.Prove2MeSourceProof.h_8324dac51fdbfa267964d2a0 _).mp hz)
  have he := Complex.cexp_tsum_eq_tprod hfactor (_root_.Prove2MeSourceProof.h_61bad4bf4babd22e06805bca hu)
  have hm := (_root_.Prove2MeSourceProof.h_e53a0a54f0755719030aa5d3 hu).map_tprod
    Complex.ofRealHom Complex.continuous_ofReal
  exact (congrArg Complex.re hm).trans (congrArg Complex.re he.symm)
end StochLean


