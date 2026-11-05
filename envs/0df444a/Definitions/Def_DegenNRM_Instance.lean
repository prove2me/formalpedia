-- Prove2me | Definitions.Def_DegenNRM_Instance
-- name    : DegenNRM_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:33:57.869221+00:00
-- url     : https://prove2.me/theorems/a16a187a-9e6b-4622-bc10-a3416369ab13
-- title:
--   Network revenue management instance: $m$ resources, $n$ query types $(a_j, p_j, F_j, [l_j,u_j])$
-- statement:
--   There are $m$ resources and $n$ query types. A query of type $j\in[n]$
--
--   1. has the size vector $a_j\in\mathbb R^m_{\ge0}$: serving it consumes $a_{j,i}$ units of resource $i$;
--   2. arrives with probability $p_j>0$, where $\sum_{j=1}^n p_j=1$;
--   3. carries a random reward with law $F_j$, a probability measure on $\mathbb R$;
--   4. has a reward interval $[l_j,u_j]$ with $0\le l_j\le u_j$.
--
--   These are the data of the network revenue management problem with finitely many query types. The support statement and the density bound on $[l_j,u_j]$ are Assumption 1, a separate definition.
--
--   **Formalization Note** Types are indexed by `Fin n` and resources by `Fin m`. The type of a query is observed (Algorithm 2 takes it as input), and its size is $a_j$. Positivity of $p_j$ is part of "$\tilde a_t$ is supported on $\{a_1,\dots,a_n\}$", and $\kappa_1$ divides by $p_j$.
-- source:
--   Jiang, Ma & Zhang, Degeneracy is OK: Logarithmic Regret for Network Revenue Management with Indiscrete Distributions, arXiv:2210.07996v5, §2, p.6; Assumption 1, p.10

import Mathlib

open MeasureTheory

namespace DegenNRM

/-- **An instance of network revenue management with finitely many query types**
(Jiang, Ma & Zhang, *Degeneracy is OK: Logarithmic Regret for Network Revenue Management with
Indiscrete Distributions*, arXiv:2210.07996v5, §2, p.6, and Assumption 1, p.10).

There are `m` resources and `n` query types. A query of type `j` has the size vector
`a j ∈ ℝᵐ_{≥0}` (`a j i` is how much of resource `i` it consumes if served), arrives with
probability `p j`, and carries a random reward drawn from the conditional reward law `F j`,
a probability measure on `ℝ`. The numbers `l j ≤ u j` are the endpoints of the reward interval
`[l_j, u_j]` of Assumption 1 (the support statement and the density bound are in
`Assumption1`).

**Formalization Note.** Types are `Fin n`, resources `Fin m`. A query's type `j` is part of
the arrival and is observed by the policy (Algorithm 2 takes "the type of query t, denoted by
j_t", p.15); its size is `a j`. The probabilities `p j` are positive and sum to `1`: "ã_t is
supported on A = {a1,...,an}" with `p_j = P(ã = a_j)` (p.6), and κ₁ of (15) divides by `p_j`.
Rewards are nonnegative (`r̃_t ∈ ℝ_{≥0}`, p.6), so `0 ≤ l j`. -/
structure Instance (m n : ℕ) where
  /-- The size vector `a_j` of a type-`j` query. -/
  a : Fin n → Fin m → ℝ
  a_nonneg : ∀ j i, 0 ≤ a j i
  /-- The arrival probability `p_j` of type `j`. -/
  p : Fin n → ℝ
  p_pos : ∀ j, 0 < p j
  p_sum : ∑ j, p j = 1
  /-- The lower end `l_j` of the reward interval of type `j`. -/
  l : Fin n → ℝ
  /-- The upper end `u_j` of the reward interval of type `j`. -/
  u : Fin n → ℝ
  l_nonneg : ∀ j, 0 ≤ l j
  l_le_u : ∀ j, l j ≤ u j
  /-- The conditional reward law `F_j = F(· | a_j)` of a type-`j` query. -/
  F : Fin n → Measure ℝ
  F_prob : ∀ j, IsProbabilityMeasure (F j)

instance {m n : ℕ} (inst : Instance m n) (j : Fin n) : IsProbabilityMeasure (inst.F j) :=
  inst.F_prob j

end DegenNRM


