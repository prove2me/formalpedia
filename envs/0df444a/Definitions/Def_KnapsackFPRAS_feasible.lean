-- Prove2me | Definitions.Def_KnapsackFPRAS_feasible
-- name    : KnapsackFPRAS_feasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:29:42.239008+00:00
-- url     : https://prove2.me/theorems/b097abac-a1fa-4071-81fd-c04321c9adc8
-- title:
--   Feasible subsets $\Omega$ of a knapsack instance
-- statement:
--   Let $w_1,\dots,w_n$ be nonnegative integer weights and $T$ a nonnegative integer capacity. For $X\subseteq[n]$ write $w(X)=\sum_{i\in X}w_i$. The **feasible subsets** are
--
--   $$
--   \Omega := \{X\subseteq[n] : w(X)\le T\}.
--   $$
--
--   The counting knapsack problem asks for $|\Omega|$. Since $w(\emptyset)=0\le T$, the empty set is always feasible and $|\Omega|\ge1$.
--
--   **Formalization Note** The index set $[n]$ is `Fin n` (indices $0,\dots,n-1$) and $\Omega$ is a finite family of finite subsets of `Fin n`; weights and capacity are natural numbers, so $w(X)\le T$ is an exact integer comparison.
-- source:
--   Jin–Park–Saha, A Nearly Linear-Time FPRAS for Counting Knapsack, STOC 2027 submission (manuscript sha256 c117260b…), Eq. (1), p.1 (PDF p.2)

import Mathlib

set_option autoImplicit false

namespace KnapsackFPRAS

/-- **Eq. (1)**, p.1. The feasible subsets of a knapsack instance:
`Ω := {X ⊆ [n] : w(X) ≤ T}`, where `w(X) := ∑_{i ∈ X} wᵢ`.

Jin–Park–Saha, *A Nearly Linear-Time FPRAS for Counting Knapsack*, STOC 2027 submission
(manuscript sha256 c117260b…4af0), Eq. (1), p.1 (PDF p.2).

**Formalization Note.** The index set `[n] = {1, …, n}` is `Fin n` (shifted to `0, …, n − 1`).
Weights and the capacity are natural numbers, and `w(X)` is the natural-number sum, so the
comparison `w(X) ≤ T` is exact. `Finset.univ : Finset (Finset (Fin n))` is the power set of
`Fin n`; the empty set is always feasible, so `(feasible w T).card ≥ 1`. -/
def feasible {n : ℕ} (w : Fin n → ℕ) (T : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun X => ∑ i ∈ X, w i ≤ T)

end KnapsackFPRAS


