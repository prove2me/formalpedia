-- Prove2me | Definitions.Def_SubmodOrder_IsPiNested
-- name    : SubmodOrder_IsPiNested
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:58.001431+00:00
-- url     : https://prove2.me/theorems/6cc745dd-6ab4-4bbd-ae73-e5ed6125bf94
-- title:
--   $\pi$-nested sets
-- statement:
--   Let $\pi$ be an order of the ground set. Sets $B\subseteq A$ are **$\pi$-nested** if the leftmost element of $A\setminus B$ is to the right of $B$:
--
--   $$
--   l_\pi(A\setminus B)>r_\pi(B).
--   $$
--
--   In words, $A$ is obtained from $B$ by adding elements that all come after every element of $B$. The weak submodular order requires the diminishing-returns inequality only for such pairs.
--
--   **Formalization Note** The condition is written as $B\subseteq A$ and $\pi(b)<\pi(a)$ for all $b\in B$, $a\in A\setminus B$. It is vacuous when $B=\emptyset$ or $A=B$; the paper itself uses $B=E(0)=\emptyset$ in the proof of Lemma 1.
-- source:
--   Udwani, Submodular Order Functions and Assortment Optimization, arXiv:2107.02743v5, p.4, "Sets B ⊆ A are π-nested if the left most element of A\B is to the right of B i.e., lπ(A\B) > rπ(B)."

import Mathlib

namespace SubmodOrder

/-- `π`-nested sets (Udwani, arXiv:2107.02743v5, p.4: "Sets B ⊆ A are π-nested if the left most
element of A\B is to the right of B i.e., lπ(A\B) > rπ(B).").

**Formalization Note.** `π : α ≃ Fin n` gives the index of each element. The condition
`lπ(A \ B) > rπ(B)` is written as `π b < π a` for all `b ∈ B` and `a ∈ A \ B`, which is vacuous
when `B = ∅` or `A = B` (where `lπ`, `rπ` are undefined in the paper); the paper itself uses
`B = E(0) = ∅` in the proof of Lemma 1. -/
def IsPiNested {α : Type*} [DecidableEq α] {n : ℕ} (π : α ≃ Fin n) (B A : Finset α) : Prop :=
  B ⊆ A ∧ ∀ b ∈ B, ∀ a ∈ A \ B, π b < π a

end SubmodOrder


