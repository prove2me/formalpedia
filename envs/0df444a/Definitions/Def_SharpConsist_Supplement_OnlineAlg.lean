-- Prove2me | Definitions.Def_SharpConsist_Supplement_OnlineAlg
-- name    : SharpConsist_Supplement_OnlineAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:21:51.476937+00:00
-- url     : https://prove2.me/theorems/7c118754-0080-4454-8efc-35bb3bdbceda
-- title:
--   Randomized online value-oracle algorithm (query-counting model)
-- statement:
--   A **randomized online value-oracle algorithm** is run on a stream whose elements arrive one at a time. Its randomness is a seed $\omega$ from a probability space $(\Omega,\mu)$ chosen with the algorithm. At the arrival that brings the number of arrived elements to $t$ (so $X_t=\{0,\dots,t-1\}$), the algorithm repeatedly either issues a value query $f(Q)$ for a set $Q\subseteq X_t$ or stops and outputs $S_t\subseteq X_t$. Each decision may depend on the seed, the capacity $k$, the count $t$, all query answers at earlier arrivals, the answers received so far at this arrival, and side information revealed with the arrived elements (used only for the modular weights $\ell_i$ of Theorem 8.2). It never sees the stream length, future elements, or the objective other than through query answers; $S_0=\emptyset$.
--
--   The derived quantities are the maintained set $S_t$ after $t$ arrivals and the predicate that arrival $t$ makes at most $B$ value queries.
--
--   **Formalization Note** Computation and sampling are free (the decision is an arbitrary function of the data above); only value queries are counted. A query is answered on its intersection with $X_t$ and the output is clipped to $X_t$. An arrival at which the algorithm never stops is assigned the output $\emptyset$; the theorems exclude this through their query bounds.
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §1, p.1; §2.1, p.4

import Mathlib

universe u

namespace SharpConsist.Supplement

/-- **A randomized online value-oracle algorithm** (query-counting model). Fu–Zhang–Tao, *A Sharp
Barrier of Consistent Submodular Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…),
§1, p.1 (elements arrive one by one, `S_t ⊆ X_t`, `|S_t| ≤ k`; "the algorithm may store and revisit
the value of f on entire history of arrivals X_t"); §2.1, p.4 (no advance knowledge of the stream
length, unit-cost value queries, termination after every arrival).

The randomness is a seed `ω` of a seed space `Ω` (a probability space chosen with the algorithm).
At the arrival that brings the number of arrived elements to `t` (so `X_t = {0, …, t − 1}`),
`step ω k t hist sides cur` either issues the next value query `inl Q` or stops with the output
`inr S`. It sees only: the seed, the capacity `k`, the count `t`, the answers `hist` of all queries
at earlier arrivals (one list per arrival), the side information `sides` revealed with the arrived
elements (used only in Theorem 8.2, where it is the modular weight `ℓ_i`), and the answers `cur` at
the present arrival. A query `Q` is answered by the value on `Q ∩ X_t`, and the output is clipped to
`X_t`.

**Formalization Note.** Computation and sampling are free (a Lean function of the data above);
only value queries are counted. The algorithm never sees the stream length, the future elements,
or the objective other than through query answers, and the same algorithm must work on every
stream. Its earlier queries and outputs are functions of `ω` and the answers it has seen, so they are
available to it. -/
structure OnlineAlg (Ω : Type u) where
  /-- The next action at the current arrival: a query (`inl`) or the output (`inr`). -/
  step : Ω → ℕ → ℕ → List (List ℝ) → List ℝ → List ℝ → Finset ℕ ⊕ Finset ℕ

namespace OnlineAlg

variable {Ω : Type u}

/-- The answers received at one arrival after `j` steps of `step` (they stop growing once the
algorithm outputs). `F` is the value oracle; a query `Q` is answered by `F (Q ∩ X_t)`. -/
def answers (A : OnlineAlg Ω) (ω : Ω) (k t : ℕ) (hist : List (List ℝ)) (sides : List ℝ)
    (F : Finset ℕ → ℝ) : ℕ → List ℝ
  | 0 => []
  | j + 1 =>
    match A.step ω k t hist sides (A.answers ω k t hist sides F j) with
    | .inl Q => A.answers ω k t hist sides F j ++ [F (Q.filter (· < t))]
    | .inr _ => A.answers ω k t hist sides F j

/-- The algorithm has stopped at this arrival after at most `B` value queries. -/
def StopsWithin (A : OnlineAlg Ω) (ω : Ω) (k t : ℕ) (hist : List (List ℝ)) (sides : List ℝ)
    (F : Finset ℕ → ℝ) (B : ℕ) : Prop :=
  ∃ S, A.step ω k t hist sides (A.answers ω k t hist sides F B) = .inr S

open Classical in
/-- The transcript of answers and the output (clipped to `X_t`) of one arrival; `([], ∅)` if the
algorithm never stops (excluded by the query bounds of the theorems). -/
noncomputable def arrival (A : OnlineAlg Ω) (ω : Ω) (k t : ℕ) (hist : List (List ℝ))
    (sides : List ℝ) (F : Finset ℕ → ℝ) : List ℝ × Finset ℕ :=
  if h : ∃ B, A.StopsWithin ω k t hist sides F B then
    (A.answers ω k t hist sides F (Nat.find h),
      match A.step ω k t hist sides (A.answers ω k t hist sides F (Nat.find h)) with
      | .inr S => S.filter (· < t)
      | .inl _ => ∅)
  else ([], ∅)

/-- The side information of the first `t` arrivals. -/
def sidesUpTo (sd : ℕ → ℝ) (t : ℕ) : List ℝ := (List.range t).map sd

/-- The answer transcripts of the first `t` arrivals. -/
noncomputable def history (A : OnlineAlg Ω) (ω : Ω) (k : ℕ) (F : Finset ℕ → ℝ) (sd : ℕ → ℝ) :
    ℕ → List (List ℝ)
  | 0 => []
  | t + 1 => A.history ω k F sd t ++
      [(A.arrival ω k (t + 1) (A.history ω k F sd t) (sidesUpTo sd (t + 1)) F).1]

/-- The maintained set `S_t ⊆ X_t` after `t` arrivals, with `S_0 = ∅`. -/
noncomputable def out (A : OnlineAlg Ω) (ω : Ω) (k : ℕ) (F : Finset ℕ → ℝ) (sd : ℕ → ℝ) :
    ℕ → Finset ℕ
  | 0 => ∅
  | t + 1 => (A.arrival ω k (t + 1) (A.history ω k F sd t) (sidesUpTo sd (t + 1)) F).2

/-- At arrival `t ≥ 1` (seed `ω`), the algorithm makes at most `B` value queries. -/
def QueriesAtMost (A : OnlineAlg Ω) (ω : Ω) (k : ℕ) (F : Finset ℕ → ℝ) (sd : ℕ → ℝ)
    (t B : ℕ) : Prop :=
  A.StopsWithin ω k t (A.history ω k F sd (t - 1)) (sidesUpTo sd t) F B

end OnlineAlg

end SharpConsist.Supplement


