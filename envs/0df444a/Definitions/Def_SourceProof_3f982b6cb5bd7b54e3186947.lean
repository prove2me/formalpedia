-- Prove2me | Definitions.Def_SourceProof_3f982b6cb5bd7b54e3186947
-- name    : SourceProof_3f982b6cb5bd7b54e3186947
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:51:32.108419+00:00
-- url     : https://prove2.me/theorems/43ca6056-ac63-448a-80ce-955086249ed8
-- title:
--   StochLean source theorem: StochLean.tprod_exponentialJumpFactor_eq_zero_guarded_complex_log

import Definitions.Def_SourceProof_6d4542e538e8d34d608590cc
import Definitions.Def_SourceProof_817411b79fe3291c478e9319
import Definitions.Def_SourceProof_eaaf8416a5e23b00c27d19aa

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

theorem _root_.Prove2MeSourceProof.h_3f982b6cb5bd7b54e3186947
    {ι : Type*} {u : ι → ℝ} (hu : Summable (fun i ↦ u i ^ 2)) :
    (∏' i, exponentialJumpFactor (u i)) =
      if (∑' i, if u i = -1 then (1 : ℝ) else 0) = 0 then
        (Complex.exp (∑' i, Complex.log (exponentialJumpFactor (u i) : ℂ))).re else 0 := by
  classical
  by_cases hn : ∀ i, u i ≠ -1
  · rw [if_pos ((_root_.Prove2MeSourceProof.h_eaaf8416a5e23b00c27d19aa hu).mpr hn)]
    exact _root_.Prove2MeSourceProof.h_817411b79fe3291c478e9319 hu hn
  · rw [if_neg (fun h ↦ hn ((_root_.Prove2MeSourceProof.h_eaaf8416a5e23b00c27d19aa hu).mp h))]
    push Not at hn
    obtain ⟨i, hi⟩ := hn
    exact tprod_of_exists_eq_zero ⟨i, by simp only [hi, _root_.Prove2MeSourceProof.h_6d4542e538e8d34d608590cc]⟩
end StochLean


