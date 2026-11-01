-- Prove2me | Definitions.Def_SubmodOrder_IsRightOf
-- name    : SubmodOrder_IsRightOf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:55.474641+00:00
-- url     : https://prove2.me/theorems/7c4755e8-080a-47af-9d63-aefb4f8b9f1b
-- title:
--   A set to the right of another in the order $\pi$
-- statement:
--   Let $\pi$ be an order (a permutation) of the ground set $N$, which indexes the elements from left to right; write $\pi(e)$ for the index of $e$, $l_\pi(S)$ for the leftmost and $r_\pi(S)$ for the rightmost element of $S$. A set $C$ lies **to the right of** a set $A$ if
--
--   $$
--   l_\pi(C)>r_\pi(A),
--   $$
--
--   that is, every element of $C$ comes after every element of $A$.
--
--   This is the position condition in the definitions of submodular and weak submodular orders.
--
--   **Formalization Note** The order is a bijection $\pi:\alpha\simeq\{0,\dots,n-1\}$. The condition is written as $\pi(a)<\pi(c)$ for all $a\in A$, $c\in C$; it agrees with $l_\pi(C)>r_\pi(A)$ for nonempty sets and holds vacuously when one of them is empty.
-- source:
--   Udwani, Submodular Order Functions and Assortment Optimization, arXiv:2107.02743v5, p.3, "Let rπ(S) denote the element in S with the largest index and lπ(S) the element with the smallest index … C to the right of A i.e., lπ(C) > rπ(A)"

import Mathlib

namespace SubmodOrder

/-- The set `C` lies to the right of the set `A` in the order `π`: `lπ(C) > rπ(A)` (Udwani,
arXiv:2107.02743v5, p.3: "Let rπ(S) denote the element in S with the largest index and lπ(S)
the element with the smallest index … C to the right of A i.e., lπ(C) > rπ(A)").

**Formalization Note.** The order is a bijection `π : α ≃ Fin n`, and `π e` is the index of
`e`. The condition `lπ(C) > rπ(A)` is written as `π a < π c` for all `a ∈ A`, `c ∈ C`; it is
the same condition when `A` and `C` are nonempty and holds vacuously when one of them is empty
(where `lπ`, `rπ` are undefined in the paper). -/
def IsRightOf {α : Type*} {n : ℕ} (π : α ≃ Fin n) (A C : Finset α) : Prop :=
  ∀ a ∈ A, ∀ c ∈ C, π a < π c

end SubmodOrder


