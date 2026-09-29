-- Prove2me | Definitions.Def_NonmonotoneSubmod_QueryLB_QueryAlgorithm
-- name    : NonmonotoneSubmod_QueryLB_QueryAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:13:49.24482+00:00
-- url     : https://prove2.me/theorems/027f2796-a7c7-45a7-a948-8bcab092faf9
-- title:
--   Adaptive value-query algorithms: deterministic runs and randomized expected value
-- statement:
--   A **deterministic adaptive algorithm with $q$ value queries** on a finite ground set $X$ consists of two decision rules on finite lists of real numbers:
--
--   1. $\mathrm{query}(a_1,\dots,a_i) \subseteq X$, the next set to query after receiving the answers $a_1,\dots,a_i$;
--   2. $\mathrm{output}(a_1,\dots,a_q) \subseteq X$, the returned set after all $q$ answers.
--
--   Run against a value oracle $h : 2^X \to \mathbb{R}$, it issues $Q_1 = \mathrm{query}()$, receives $a_1 = h(Q_1)$, issues $Q_2 = \mathrm{query}(a_1)$, and so on; after $q$ rounds it returns $A(h) = \mathrm{output}(a_1,\dots,a_q)$. Each query may depend on all earlier answers, and the algorithm sees $h$ only through these answers.
--
--   A **randomized algorithm** is a probability distribution $\mu$ over deterministic $q$-query algorithms (conditioning on its random bits). Its expected value on $h$ is
--
--   $$
--   \mathbb{E}_{A\sim\mu}\bigl[h(A(h))\bigr] = \sum_{S \subseteq X} \Pr_{A\sim\mu}\bigl[A(h) = S\bigr]\, h(S).
--   $$
--
--   This is the algorithm model of the query lower bound, Theorem 4.5: adaptive, possibly randomized, with access to $f$ only through a value oracle.
--
--   **Formalization Note** `DetAlg X q` is a structure with fields `query, output : List ℝ → Finset X`; `answers A h i` is the list of the first $i$ answers, `queryAt A h i` the $i$-th query, and `run A h` the returned set. Exactly $q$ queries are made; an algorithm that stops earlier can pad with dummy queries. Randomization is a `PMF` over `DetAlg X q`, i.e. a distribution with countable support.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1133 (value oracle access) and p. 1150, §4.2, proof of Theorem 4.5 ("Consider any algorithm, for now deterministic. (For a randomized algorithm, let us condition on its random bits.)")

import Mathlib

namespace NonmonotoneSubmod.QueryLB

/-- A deterministic adaptive algorithm that makes `q` value-oracle queries on subsets of `X`
(Feige–Mirrokni–Vondrák 2011, §4.2, p. 1150). `query a` is the next queried set given the list
`a` of oracle answers received so far; `output a` is the returned set given all `q` answers.
Each query may depend on every earlier answer, and answers are arbitrary reals. -/
structure DetAlg (X : Type) (q : ℕ) where
  query : List ℝ → Finset X
  output : List ℝ → Finset X

variable {X : Type} {q : ℕ}

/-- The list of the first `i` oracle answers when `A` runs against the oracle `h`. -/
def DetAlg.answers (A : DetAlg X q) (h : Finset X → ℝ) : ℕ → List ℝ
  | 0 => []
  | i + 1 => A.answers h i ++ [h (A.query (A.answers h i))]

/-- The `i`-th query (`i = 0, …, q − 1`) that `A` issues against the oracle `h`. -/
def DetAlg.queryAt (A : DetAlg X q) (h : Finset X → ℝ) (i : ℕ) : Finset X :=
  A.query (A.answers h i)

/-- The set `A` returns after its `q` queries to the oracle `h`. -/
def DetAlg.run (A : DetAlg X q) (h : Finset X → ℝ) : Finset X :=
  A.output (A.answers h q)

/-- The expected value `E[h(output)]` of a randomized algorithm, modelled as a probability
distribution `μ` over deterministic `q`-query algorithms (its random bits), on the oracle `h`. -/
noncomputable def expectedValue [Fintype X] (μ : PMF (DetAlg X q)) (h : Finset X → ℝ) : ℝ :=
  ∑ S : Finset X, ((μ.map (fun A => A.run h)) S).toReal * h S

end NonmonotoneSubmod.QueryLB


