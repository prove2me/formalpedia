-- Prove2me | Definitions.Def_BFAlmostLinear_sampleMass
-- name    : BFAlmostLinear_sampleMass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:37:52.393978+00:00
-- url     : https://prove2.me/theorems/492c591a-4936-46fa-8410-b1e5258b5d66
-- title:
--   Bernoulli$(1/b)$ sample of the negative vertices and the probability of an event
-- statement:
--   Let $N$ be a finite set and $b\ge1$. Sampling each element of $N$ independently with probability $1/b$ gives the random set $U\subseteq N$ with
--   $$\Pr[U]=\Big(\frac1b\Big)^{|U|}\Big(1-\frac1b\Big)^{|N\setminus U|}.$$
--   The probability of an event $\mathrm{Good}$ on subsets of $N$ is $\sum_{U\subseteq N,\ \mathrm{Good}(U)}\Pr[U]$.
--
--   "With high probability over the randomness of $U$" in §2 and §4.2 is a lower bound $1-n^{-c}$ on this quantity, for every $c>0$ with constants depending on $c$.
--
--   **Formalization Note** The sum is over the powerset of $N$, so the probability is a finite sum and needs no measure theory.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), Theorem 2.1, p.5 and Lemma 2.2, p.6: "U ⊆ N be a random sample where each vertex in N is sampled with probability 1/b"

import Mathlib

namespace BFAlmostLinear

/-- The probability that the random sample `U ⊆ N` equals a given set, when each vertex of `N` is sampled
independently with probability `1/b` (Theorem 2.1, p.5): `(1/b)^{|U|} (1 − 1/b)^{|N∖U|}`. It is a
probability vector on `N.powerset` for `b ≥ 1`. -/
noncomputable def sampleMass {V : Type} [DecidableEq V] (N U : Finset V) (b : ℝ) : ℝ :=
  (1 / b) ^ U.card * (1 - 1 / b) ^ (N \ U).card

open Classical in
/-- The probability, over the random sample `U ⊆ N`, of the event `Good`. "With high probability" in §2,
§4.2 is a lower bound `1 − n^{−c}` on this quantity for every `c > 0`. -/
noncomputable def goodMass {V : Type} (N : Finset V) (b : ℝ) (Good : Finset V → Prop) : ℝ :=
  ∑ U ∈ N.powerset.filter Good, sampleMass N U b

end BFAlmostLinear


