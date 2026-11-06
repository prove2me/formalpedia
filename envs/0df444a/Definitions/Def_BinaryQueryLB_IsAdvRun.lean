-- Prove2me | Definitions.Def_BinaryQueryLB_IsAdvRun
-- name    : BinaryQueryLB_IsAdvRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:47:56.63151+00:00
-- url     : https://prove2.me/theorems/f080d654-83b2-43db-8452-016d676e209a
-- title:
--   A run of an algorithm against the adversary
-- statement:
--   A run of length $T$ of the algorithm $A$ against the adversary is a sequence of adversary states $s_0,s_1,\dots$ and answers $\beta_0,\beta_1,\dots$ such that $s_0$ has every $P_i=\tau\mathbb B_m$ and no committed index, and for every $t<T$ the algorithm, given the answers $\beta_0,\dots,\beta_{t-1}$, asks a query that the adversary answers with $\beta_t$ by one admissible step from $s_t$ to $s_{t+1}$.
--
--   **Formalization Note** Queries and answers are counted from $0$. Every run obeying the rules is allowed.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), §3.1, p.16

import Mathlib
import Definitions.Def_BinaryQueryLB_IsAdvStep
import Definitions.Def_BinaryQueryLB_Algorithm
import Definitions.Def_BinaryQueryLB_tau

namespace BinaryQueryLB

/-- **A run of the algorithm against the adversary (§3.1).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), §3.1, p.16: "Fix `A` as in
Proposition 3.1. We now describe how an adversary answers the queries of `A` … initially
`P_i = τB_m`."

`IsAdvRun d R M A T s β` says that `s t` is the adversary's state and `β t` its answer to the
`t`-th query (counted from `0`) for `t < T`: the initial state has every `P_i = τ𝔹_m` and no
committed index, and for each `t < T` the algorithm, given the answers `β 0, …, β (t−1)`, asks a
query, which the adversary answers with `β t` by one admissible step from `s t` to `s (t+1)`.

**Formalization Note.** Every run obeying the rules is allowed (any admissible levels and bits);
the answer history after `t` steps is `(List.range t).map β`. -/
def IsAdvRun (d : ℕ) (R M : ℝ) (A : Algorithm d) (T : ℕ) (s : ℕ → AdvState d) (β : ℕ → Bool) :
    Prop :=
  s 0 = (fun _ => Metric.closedBall 0 (tau (d / 2)), fun _ => none) ∧
    ∀ t < T, ∃ qr : LocalQuery d,
      A ((List.range t).map β) = Sum.inl qr ∧ IsAdvStep d R M (s t) qr (β t) (s (t + 1))

end BinaryQueryLB


