-- Prove2me | Definitions.Def_MatroidEquitability_IsExchangeable
-- name    : MatroidEquitability_IsExchangeable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:48.728496+00:00
-- url     : https://prove2.me/theorems/33e60740-3151-435b-906e-df7ce273947f
-- title:
--   $(t,S)$-exchangeable set for two bases
-- statement:
--   Let $B,D$ be bases of $M$ and let $t\in(B\cup D)\setminus S$. A set $X\subseteq B\cup D$ is **$(t,S)$-exchangeable for $B$ and $D$** if
--
--   $$
--   t\in X\subseteq S+t
--   $$
--
--   and both $B\triangle X$ and $D\triangle X$ are bases of $M$.
--
--   So $X$ exchanges elements between the two bases, using at most one element, namely $t$, from outside $S$. This is the object of the exchange theorem of Akrami, Liu, Raj and Végh.
--
--   **Formalization Note** The page defines the notion for $S\subseteq B\cup D$, while the exchange theorem takes $S\subseteq E$. Here $S$ is an arbitrary set: since $t\in B\cup D$ and $X\subseteq B\cup D$, this is the same as the page's definition applied to $S\cap(B\cup D)$. Disjointness of $B$ and $D$ is left to the statements that use the predicate.
-- source:
--   Bérczi, Liu, Reis, Tarnawski, Weighted Equitability and Matroid-Constrained Discrepancy, arXiv:2608.13983 (held version sha256 0675891a…), §2, p.8 (PDF p.10)

import Mathlib

open scoped symmDiff

namespace MatroidEquitability

/-- `X` is `(t, S)`-exchangeable for `B` and `D`: `X ⊆ B ∪ D`, `t ∈ X ⊆ S + t`, and both `B △ X` and
`D △ X` are bases (§2, printed p.8 = PDF p.10 of
Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…)).

**Formalization Note.** The paper's domain condition `t ∈ (B ∪ D) \ S` is the clause
`t ∈ (B ∪ D) \ S`; that `B, D` are disjoint bases is left to the statements using this predicate.
The page defines the notion for `S ⊆ B ∪ D`, while Theorem 3 takes `S ⊆ E`; here `S` is arbitrary, and
for `t ∈ B ∪ D` and `X ⊆ B ∪ D` the condition `X ⊆ S + t` is the same as `X ⊆ (S ∩ (B ∪ D)) + t`. -/
def IsExchangeable {α : Type*} (M : Matroid α) (B D : Set α) (t : α) (S X : Set α) : Prop :=
  t ∈ (B ∪ D) \ S ∧ X ⊆ B ∪ D ∧ t ∈ X ∧ X ⊆ insert t S ∧ M.IsBase (B ∆ X) ∧ M.IsBase (D ∆ X)

end MatroidEquitability


