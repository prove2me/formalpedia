-- Prove2me | Definitions.Def_SmoothedNash_Supplement_alg4Calls
-- name    : SmoothedNash_Supplement_alg4Calls
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:07:20.973333+00:00
-- url     : https://prove2.me/theorems/2425e5f6-f733-438e-9379-c98d4eb332a9
-- title:
--   Oracle calls of Algorithm 4: $1$ or $6N + 3$
-- statement:
--   The number of zeroth- and first-order oracle calls of a run of Algorithm 4 with $N$ loop iterations is $1$ if the algorithm returns at line 2; otherwise
--   $$
--   1 + 6N + 2 :
--   $$
--   one call for $F(0)$; per iteration two calls for $H(\bar x_i)$ (Lemma 4.4) and one call each to $F$ and $J_F$ at $\bar x_i$ and at $\bar y_i$; and two calls for the final $H(\bar x_N)$.
--
--   **Formalization Note** Each evaluation of $H$ is charged the upper bound of two queries from Lemma 4.4.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Algorithm 4 and Lemma 4.4, pp.27–28

import Mathlib
open MeasureTheory

namespace SmoothedNash.Supplement

/-- The number of zeroth- and first-order oracle calls of a run of Algorithm 4 with `N` loop
iterations (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), Algorithm 4 and Lemma 4.4, pp.27–28): one call for `F(0)` at line 1 (and nothing
else if `‖F(0)‖ ≤ ε/2`); otherwise, per iteration, two calls for `H(x̄_i)` (Lemma 4.4: at most two
zeroth-order queries) and one call each to `F` and `J_F` at `x̄_i` and at `ȳ_i` (to form `K`, `J_K` at
`x_i` and `y_i`), plus two calls for the final `H(x̄_N)`: `1 + 6N + 2` in total.

**Formalization Note** This charges the upper bound of Lemma 4.4 for every evaluation of `H`; the
count is exact up to that. -/
noncomputable def alg4Calls {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (ε : ℝ) (N : ℕ) : ℕ := by
  classical
  exact if ‖F 0‖ ≤ ε / 2 then 1 else 6 * N + 3

end SmoothedNash.Supplement


