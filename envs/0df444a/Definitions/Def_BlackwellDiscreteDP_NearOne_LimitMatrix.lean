-- Prove2me | Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
-- name    : BlackwellDiscreteDP_NearOne_LimitMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:46:03.221473+00:00
-- url     : https://prove2.me/theorems/448c6564-879d-4ed1-8a55-5ab262b53e9e
-- title:
--   Markov matrices, the Cesàro limit matrix Q*, H(β) = Σ βⁿ(Qⁿ − Q*) and H = (I − Q + Q*)⁻¹ − Q* (Lemma 1)
-- statement:
--   This file defines the matrix objects of Blackwell's Lemma 1 for a square real matrix $Q$ indexed by a finite set of states.
--
--   1. $Q$ is a **Markov matrix** if all its entries are nonnegative and every row sums to $1$.
--   2. The **Cesàro means** of $Q$ are
--   $$C_N(Q)=\frac{I+Q+\cdots+Q^N}{N+1},\qquad N=0,1,2,\dots$$
--   3. The **limit matrix** $Q^*$ is the limit of $C_N(Q)$ as $N\to\infty$, taken entrywise.
--   4. For a discount factor $\beta$, $H(\beta)=\sum_{n=0}^\infty \beta^n\,(Q^n-Q^*)$.
--   5. The **deviation matrix** is $H=(I-Q+Q^*)^{-1}-Q^*$.
--
--   These are the objects in terms of which Blackwell expresses the behaviour of discounted returns as the discount factor tends to $1$: $Q^*$ carries the long-run average and $H$ the transient correction.
--
--   **Formalization Note** The limit is taken with Lean's `limUnder`, which returns an arbitrary matrix if the limit does not exist, and $H(\beta)$ is a `tsum`, which is $0$ for a non-summable series. Neither definition assumes convergence: that the Cesàro means of a Markov matrix converge (Lemma 1(a)) and that the series converges for $0\le\beta<1$ (Lemma 1(d)) are separate theorems. The inverse is Mathlib's total matrix inverse; the nonsingularity of $I-Q+Q^*$ is part of Lemma 1(d).
-- source:
--   Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962), DOI 10.1214/aoms/1177704593, pp. 721–722, Lemma 1(a), (d)

import Mathlib
open Filter Topology Matrix

namespace BlackwellDiscreteDP.NearOne

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A **Markov matrix** (stochastic matrix): nonnegative entries and unit row sums.

Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593, p. 719, §2 and p. 721, Lemma 1. -/
def IsMarkovMatrix (P : Matrix n n ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j = 1

/-- The Cesàro mean `(I + P + ⋯ + P^N)/(N + 1)` of the powers of `P`.

Blackwell (1962), p. 721, Lemma 1(a) (printed "I + Q + ⋯ + Q^N/N + 1", which means
(I + Q + ⋯ + Q^N)/(N + 1)). -/
noncomputable def cesaroMean (P : Matrix n n ℝ) (N : ℕ) : Matrix n n ℝ :=
  ((N : ℝ) + 1)⁻¹ • ∑ k ∈ Finset.range (N + 1), P ^ k

/-- The **limit matrix** `Q*` of a square matrix `P`: the limit, as `N → ∞`, of the Cesàro means
`(I + P + ⋯ + P^N)/(N + 1)`, in the entrywise topology of `Matrix n n ℝ`.

Blackwell (1962), p. 721, Lemma 1(a).

**Formalization Note.** `limUnder` returns an arbitrary matrix when the limit does not exist;
the definition does not presuppose existence. That the Cesàro means of a Markov matrix
converge (so `limitMatrix P` is the true limit) is Lemma 1(a), a theorem. -/
noncomputable def limitMatrix (P : Matrix n n ℝ) : Matrix n n ℝ :=
  limUnder atTop (cesaroMean P)

/-- `H(β) = ∑_{k ≥ 0} β^k (P^k − Q*)`, a matrix-valued function of the discount factor.

Blackwell (1962), p. 721, Lemma 1(d).

**Formalization Note.** A real `tsum` of matrices (entrywise topology); it equals `0` if the
series is not summable. Summability for `0 ≤ β < 1` and a Markov matrix `P` is asserted in the
theorem formalizing Lemma 1(d). -/
noncomputable def deviationSum (P : Matrix n n ℝ) (β : ℝ) : Matrix n n ℝ :=
  ∑' k : ℕ, β ^ k • (P ^ k - limitMatrix P)

/-- `H = (I − P + Q*)⁻¹ − Q*` (the deviation matrix of the chain `P`).

Blackwell (1962), p. 721, Lemma 1(d).

**Formalization Note.** `⁻¹` is Mathlib's total matrix inverse (`0` for a singular matrix);
the nonsingularity of `I − P + Q*` for a Markov matrix `P` is part of the theorem formalizing
Lemma 1(d). -/
noncomputable def deviationMatrix (P : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 - P + limitMatrix P)⁻¹ - limitMatrix P

end BlackwellDiscreteDP.NearOne


