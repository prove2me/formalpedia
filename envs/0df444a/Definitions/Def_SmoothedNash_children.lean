-- Prove2me | Definitions.Def_SmoothedNash_children
-- name    : SmoothedNash_children
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:51:06.957962+00:00
-- url     : https://prove2.me/theorems/4c6de515-7648-4211-b046-b8b940b8ba78
-- title:
--   Children of a grid point (Lemma 2.1)
-- statement:
--   For a point $c \in N_t(A)$, its **children** are the feasible points of $N_{t+1}(A)$ obtained by replacing each numerator $q_t c_i(a)$, for $a \in A_i \setminus \{\max A_i\}$, by either $2 q_t c_i(a)$ or $2 q_t c_i(a) + 1$, and then setting the last coordinate of each player so that its coordinates sum to $1$.
--
--   On numerators: the children of $k$ are the vectors $k'$ of the level-$(t+1)$ grid with
--   $$
--   k'_i(a) \in \{2 k_i(a),\ 2 k_i(a) + 1\} \qquad \text{for all } i \text{ and } a \in A_i \setminus \{\max A_i\}.
--   $$
--   Algorithm 2 replaces each passing center at a level $t \ge 1$ by its children.
--
--   **Formalization Note** Membership in the level-$(t+1)$ grid fixes the last coordinate $k'_i(\max A_i) = q_{t+1} - \sum_{a \ne \max A_i} k'_i(a)$ and requires it to be nonnegative, which is the meaning of "feasible".
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Lemma 2.1, p.14

import Mathlib
import Definitions.Def_SmoothedNash_SupportProfile
import Definitions.Def_SmoothedNash_maxAct
import Definitions.Def_SmoothedNash_grid

namespace SmoothedNash

/-- The **children** of a level-`t` grid point `c` (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), Lemma 2.1, p.14): the feasible points of
`N_{t+1}(A)` obtained by replacing each numerator `q_t c_i(a)`, for `a ∈ A_i ∖ {max A_i}`, by
`2 q_t c_i(a)` or `2 q_t c_i(a) + 1`, and then setting the last coordinate of each player so that its
coordinates sum to `1`.

**Formalization Note** On numerators (`grid`): the `k' ∈ grid A (t+1)` with
`k'_i(a) ∈ {2 k_i(a), 2 k_i(a) + 1}` for every `a ∈ A_i ∖ {max A_i}`. Membership in
`grid A (t+1)` fixes the last coordinate `k'_i(max A_i) = q_{t+1} − Σ_{a ≠ max A_i} k'_i(a)` and
requires it to be nonnegative, which is "feasible". -/
def children {m n : ℕ} (A : SupportProfile m n) (t : ℕ) (k : Fin m → Fin n → ℕ) :
    Finset (Fin m → Fin n → ℕ) :=
  (grid A (t + 1)).filter fun k' =>
    ∀ i, ∀ a ∈ A.1 i, a ≠ maxAct A i → (k' i a = 2 * k i a ∨ k' i a = 2 * k i a + 1)

end SmoothedNash


