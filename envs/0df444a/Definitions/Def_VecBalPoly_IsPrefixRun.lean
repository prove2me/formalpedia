-- Prove2me | Definitions.Def_VecBalPoly_IsPrefixRun
-- name    : VecBalPoly_IsPrefixRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T23:17:39.95254+00:00
-- url     : https://prove2.me/theorems/ff89af5b-6929-4395-a94f-75c58562b042
-- title:
--   Prefixes and complete runs of Algorithm 2.2
-- statement:
--   A **prefix run** with $N$ updates is a sequence of states $s_0,\dots,s_N$ and directions $h_0,\dots,h_{N-1}$ such that $s_0$ is the initial cleanup of the initial state and, for every $k<N$, $|V(s_k)|>K$, $h_k$ is a good direction at $s_k$, and $s_{k+1}$ is the iteration of $s_k$ along $h_k$. A **run** is a prefix run with $|V(s_N)|\le K$.
--
--   **Formalization Note** Step 1 of Algorithm 2.2 ("compute an update direction h using Lemma 2.1") is modelled as any direction meeting the conclusion of Lemma 2.1, so runs range over all such choices.
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), Algorithm 2.2, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_VecBalPoly_GoodDir
import Definitions.Def_VecBalPoly_step

namespace VecBalPoly

variable {m n : ℕ}

/-- **A prefix of a run of Algorithm 2.2** with `N` updates. `sts k` is the state after the
`k`-th cleanup and `hs k` the direction of the `(k+1)`-st update:
`sts 0` is the initial cleanup of the initial state, and for every `k < N` the loop condition
`|V| > K` holds at `sts k`, `hs k` has the guarantees of Lemma 2.1 at `sts k`, and
`sts (k+1)` is the result of the update with `hs k` followed by cleanup.
Source: Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), Algorithm 2.2, p.6 (PDF p.7).

**Formalization Note** Step 1 of the algorithm ("compute an update direction h using
Lemma 2.1") is any direction meeting Lemma 2.1's conclusion (`GoodDir`), so prefixes quantify over
all such choices; the paper's procedure is one of them. The branch `n ≤ K` of the algorithm
performs no update. -/
def IsPrefixRun (A : Matrix (Fin m) (Fin n) ℝ) (N : ℕ) (sts : ℕ → St m n)
    (hs : ℕ → Fin n → ℝ) : Prop :=
  sts 0 = cleanup A true (initState A) ∧
  ∀ k < N, K < ((sts k).V.card : ℝ) ∧ GoodDir A (sts k) (hs k) ∧
    sts (k + 1) = step A (sts k) (hs k)

/-- **A complete run of Algorithm 2.2**: a prefix whose last state has `|V| ≤ K`, so the loop
stops. Source: ibid., Algorithm 2.2, p.6 (PDF p.7). -/
def IsRun (A : Matrix (Fin m) (Fin n) ℝ) (N : ℕ) (sts : ℕ → St m n)
    (hs : ℕ → Fin n → ℝ) : Prop :=
  IsPrefixRun A N sts hs ∧ ((sts N).V.card : ℝ) ≤ K

end VecBalPoly


