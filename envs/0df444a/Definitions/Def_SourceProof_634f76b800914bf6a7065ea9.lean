-- Prove2me | Definitions.Def_SourceProof_634f76b800914bf6a7065ea9
-- name    : SourceProof_634f76b800914bf6a7065ea9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:46:05.4953+00:00
-- url     : https://prove2.me/theorems/aa1b20ee-af62-4f8f-bdc3-5a8bccb9ce2a
-- title:
--   LevyStochCalc source proof: LevyStochCalc.abs_taylorRemainderNormed_le_affine
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_TaylorTwoModulus_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The second-order Taylor bound against a modulus of continuity

A Lipschitz second derivative is more than the Taylor bound needs: the remainder is controlled by
the oscillation of the second derivative on the segment alone, which is what a merely continuous
second derivative supplies. The affine form `A + K‖z − w‖` of the oscillation bound covers a
Lipschitz second derivative (`A = 0`) and a merely uniformly continuous one (`K` chosen from the
modulus at scale `A`) in one statement.

## Main statements

* `LevyStochCalc.abs_sub_taylor_two_le_modulus_normed` — the bound by the oscillation on the
  segment.
* `LevyStochCalc.abs_sub_taylor_two_le_affine` — the bound `A‖y − x‖² + K‖y − x‖³` under an
  affine oscillation bound.
* `LevyStochCalc.abs_taylorRemainderNormed_le_affine` — its telescoped form along a sequence.
-/

namespace LevyStochCalc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem _root_.Prove2MeSourceProof.h_634f76b800914bf6a7065ea9 {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hf'' : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖) (x : ℕ → E) (m : ℕ) :
    |taylorRemainderNormed f f' f'' x m|
      ≤ A * ∑ i ∈ Finset.range m, ‖x (i + 1) - x i‖ ^ 2
        + K * ∑ i ∈ Finset.range m, ‖x (i + 1) - x i‖ ^ 3 := by
  unfold LevyStochCalc.taylorRemainderNormed
  have htel : f (x m) - f (x 0) = ∑ i ∈ Finset.range m, (f (x (i + 1)) - f (x i)) :=
    (Finset.sum_range_sub (fun i => f (x i)) m).symm
  rw [htel, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have heq : f (x (i + 1)) - f (x i)
      - (f' (x i) (x (i + 1) - x i) + f'' (x i) (x (i + 1) - x i) (x (i + 1) - x i) / 2)
      = f (x (i + 1)) - f (x i) - f' (x i) (x (i + 1) - x i)
        - f'' (x i) (x (i + 1) - x i) (x (i + 1) - x i) / 2 := by ring
  rw [heq]
  exact LevyStochCalc.abs_sub_taylor_two_le_affine hA0 hK0 hf hf' hf'' (x i) (x (i + 1))
end LevyStochCalc


