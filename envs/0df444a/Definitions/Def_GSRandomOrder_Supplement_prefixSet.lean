-- Prove2me | Definitions.Def_GSRandomOrder_Supplement_prefixSet
-- name    : GSRandomOrder_Supplement_prefixSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:08:14.28165+00:00
-- url     : https://prove2.me/theorems/5bdf5eee-92a5-4760-9b1d-893732fce863
-- title:
--   Arrived set $S_k$, arrival list and decision prefixes in random order
-- statement:
--   The items arrive in uniformly random order, given by a bijection $\sigma$ of $N=\{1,\dots,n\}$: the item at arrival position $j$ ($j=0,\dots,n-1$) is $g_{j+1}=\sigma(j)$. The **arrived set** after $t$ arrivals is
--   $$
--   S_t=\{\sigma(j): j<t\},
--   $$
--   so $S_k$ is the set of the first $k$ arrivals and $g_k$ the $k$-th arrival. Two auxiliary lists are also defined: the list $(g_1,\dots,g_t)$ of the first $t$ arrivals, and the list of the first $t$ entries of a sequence of decisions indexed by arrival position.
--
--   **Formalization Note** The uniformly random order is the uniform law on the $n!$ bijections `Fin n ≃ Fin n`; probabilities over the order are finite sums $\frac1{n!}\sum_\sigma$.
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), §4.3, p.15 ("Let $S_k$ be the set of the first $k$ arrivals and $g_k$ the $k$-th arrival")

import Mathlib

set_option autoImplicit false

namespace GSRandomOrder.Supplement

/-- **Arrived set** `S_t` (R. Paes Leme, M. Pál, N. Patel, *Gross Substitutes Welfare in Random
Order*, STOC 2027 submission, manuscript sha256 69787f50…, §4.3, p.15: "Let `S_k` be the set of
the first `k` arrivals and `g_k` the `k`-th arrival"). The arrival order is a bijection
`σ : Fin n ≃ Fin n`: `σ j` is the item arriving at position `j` (0-based), i.e. `g_{j+1} = σ j`,
and `S_t = {σ j : j < t}`.

**Formalization Note.** The uniformly random order is the uniform law on the `n!` bijections
`σ`; probabilities are finite sums `(1/n!) Σ_σ`. -/
def prefixSet {n : ℕ} (σ : Fin n ≃ Fin n) (t : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter fun j : Fin n => j.val < t).image σ

/-- The list of the first `t` arrivals `g_1, …, g_t`, in arrival order. -/
def prefixList {n : ℕ} (σ : Fin n ≃ Fin n) (t : ℕ) : List (Fin n) :=
  ((List.finRange n).map σ).take t

/-- The list of the first `t` entries `d_0, …, d_{t−1}` of a sequence of decisions indexed by
arrival position. -/
def decisionList {n : ℕ} {β : Type} (d : Fin n → β) (t : ℕ) : List β :=
  ((List.finRange n).map d).take t

end GSRandomOrder.Supplement


