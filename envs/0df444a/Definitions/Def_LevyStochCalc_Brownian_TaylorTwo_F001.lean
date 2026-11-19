-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_TaylorTwo_F001
-- name    : LevyStochCalc_Brownian_TaylorTwo_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:42:41.37821+00:00
-- url     : https://prove2.me/theorems/21ac4286-1708-4216-8742-0188cec16a6a
-- title:
--   Source declarations: LevyStochCalc.Brownian.TaylorTwo
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.TaylorTwo. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_5da8457f4c66732a5c2f52e6
import Mathlib.Analysis.Calculus.MeanValue

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Second-order Taylor bound with a Lipschitz second derivative

For a twice-differentiable real function whose second derivative is `K`-Lipschitz, the
second-order Taylor polynomial approximates the function to within `K|y − x|³`.

## Main statements

* `LevyStochCalc.abs_sub_taylor_one_le` — the first-order Taylor remainder bound.
* `LevyStochCalc.abs_sub_taylor_two_le` — the second-order Taylor remainder bound.
* `LevyStochCalc.abs_sub_sum_taylor_two_le` — the telescoped form along a sequence.
* `LevyStochCalc.taylorRemainder` — the telescoped remainder as a function of the sequence.
* `LevyStochCalc.abs_taylorRemainder_le` — its bound.
-/

namespace LevyStochCalc

/-- **Telescoped second-order Taylor expansion along a sequence.** -/
theorem abs_sub_sum_taylor_two_le {f f' f'' : ℝ → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ u v : ℝ, |f'' u - f'' v| ≤ K * |u - v|) (x : ℕ → ℝ) (m : ℕ) :
    |f (x m) - f (x 0)
        - ((∑ i ∈ Finset.range m, f' (x i) * (x (i + 1) - x i))
          + ∑ i ∈ Finset.range m, f'' (x i) * (x (i + 1) - x i) ^ 2 / 2)|
      ≤ K * ∑ i ∈ Finset.range m, |x (i + 1) - x i| ^ 3 := by
  have htel : f (x m) - f (x 0) = ∑ i ∈ Finset.range m, (f (x (i + 1)) - f (x i)) :=
    (Finset.sum_range_sub (fun i => f (x i)) m).symm
  rw [htel, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have heq : f (x (i + 1)) - f (x i)
      - (f' (x i) * (x (i + 1) - x i) + f'' (x i) * (x (i + 1) - x i) ^ 2 / 2)
      = f (x (i + 1)) - f (x i) - f' (x i) * (x (i + 1) - x i)
        - f'' (x i) * (x (i + 1) - x i) ^ 2 / 2 := by ring
  rw [heq]
  exact _root_.Prove2MeSourceProof.h_5da8457f4c66732a5c2f52e6 hK0 hf hf' hf'' (x i) (x (i + 1))
/-- The second-order Taylor remainder of `f` along the first `m` steps of the sequence `x`. -/
noncomputable def taylorRemainder (f f' f'' : ℝ → ℝ) (x : ℕ → ℝ) (m : ℕ) : ℝ :=
  f (x m) - f (x 0)
    - ((∑ i ∈ Finset.range m, f' (x i) * (x (i + 1) - x i))
      + ∑ i ∈ Finset.range m, f'' (x i) * (x (i + 1) - x i) ^ 2 / 2)
/-- The second-order Taylor remainder along a sequence is bounded by the Lipschitz constant of
`f''` times the sum of the cubed increments. -/
theorem abs_taylorRemainder_le {f f' f'' : ℝ → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ u v : ℝ, |f'' u - f'' v| ≤ K * |u - v|) (x : ℕ → ℝ) (m : ℕ) :
    |taylorRemainder f f' f'' x m| ≤ K * ∑ i ∈ Finset.range m, |x (i + 1) - x i| ^ 3 :=
  abs_sub_sum_taylor_two_le hK0 hf hf' hf'' x m
end LevyStochCalc


