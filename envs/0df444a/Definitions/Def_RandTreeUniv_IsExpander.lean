-- Prove2me | Definitions.Def_RandTreeUniv_IsExpander
-- name    : RandTreeUniv_IsExpander
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:11:08.074379+00:00
-- url     : https://prove2.me/theorems/fad912f9-2ef9-468a-bd6b-a1ead481c5e8
-- title:
--   $(f,A_1,B_1,\eta,t)$-expander (Definition 2.7)
-- statement:
--   Let $(A,B)$ be a bipartite graph with finite parts, let $1\le\eta\le t$ be integers, $A_1\subseteq A$ with $|A_1|\le\eta$, $B_1\subseteq B$, and $f:A\to\mathbb N$ a function with values in the positive integers and $f(A)=|B|$, where $f(U)=\sum_{v\in U}f(v)$. The graph is an **$(f,A_1,B_1,\eta,t)$-expander** if all of the following hold:
--
--   1. $|N(U)\cap B_1|\ge f(U)$ for every $U\subseteq A_1$;
--   2. $|N(U)\setminus B_1|\ge f(U)$ for every $U\subseteq A\setminus A_1$ with $|U|\le\eta$;
--   3. $|N(U)|\ge f(U\cup A_1)$ for every $U\subseteq A$ with $\eta+1\le|U|\le t$;
--   4. $|N(U)\setminus A_1|\ge|U|$ for every $U\subseteq B$ with $|U|\le t$;
--   5. for all $A'\subseteq A$ and $B'\subseteq B$ with $|A'|=|B'|=t$ there is an edge between $A'$ and $B'$.
--
--   Conditions 1–3 are Hall-type conditions for small sets on the $A$ side, condition 4 is a small-set condition on the $B$ side, and condition 5 says the graph is $t$-joined. Lemma 2.8 shows that together they give an $f$-matching in which the stars of $A_1$ stay inside $B_1$.
--
--   **Formalization Note** The side conditions $1\le\eta\le t$, $|A_1|\le\eta$, $f\ge1$ and $f(A)=|B|$ are part of the predicate, as in the preamble of the definition.
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), Definition 2.7, p.11 (PDF 12)

import Mathlib
import Definitions.Def_RandTreeUniv_bipNbr

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- `(A, B)` is an `(f, A₁, B₁, η, t)`-expander (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), Definition 2.7, p.11 (PDF 12)).
The data are integers `1 ≤ η ≤ t`, sets `A₁ ⊆ A` with `|A₁| ≤ η` and `B₁ ⊆ B`, and a function
`f : A → ℕ` (positive integers, §2.1) with `f(A) = |B|`, where `f(U) = ∑_{v ∈ U} f(v)`; and
(i) `|N(U) ∩ B₁| ≥ f(U)` for every `U ⊆ A₁`;
(ii) `|N(U) \ B₁| ≥ f(U)` for every `U ⊆ A \ A₁` with `|U| ≤ η`;
(iii) `|N(U)| ≥ f(U ∪ A₁)` for every `U ⊆ A` with `|U| ∈ [η + 1, t]`;
(iv) `|N(U) \ A₁| ≥ |U|` for every `U ⊆ B` with `|U| ≤ t`;
(v) there is an edge between any `A' ⊆ A` and `B' ⊆ B` with `|A'| = |B'| = t`.

**Formalization Note** The bipartite graph is `r : A → B → Prop` with finite parts. The side
conditions of the definition's preamble (`1 ≤ η ≤ t`, `|A₁| ≤ η`, `f ≥ 1`, `f(A) = |B|`) are part
of the predicate. `N(U)` is `bipNbr r U` for `U ⊆ A` and `bipNbr (flip r) U` for `U ⊆ B`. -/
def IsExpander {A B : Type*} [Fintype A] [Fintype B] (r : A → B → Prop) (f : A → ℕ)
    (A₁ : Finset A) (B₁ : Finset B) (η t : ℕ) : Prop :=
  1 ≤ η ∧ η ≤ t ∧ A₁.card ≤ η ∧ (∀ v, 1 ≤ f v) ∧ (∑ v, f v = Fintype.card B) ∧
  (∀ U ⊆ A₁, ∑ v ∈ U, f v ≤ (bipNbr r U ∩ B₁).card) ∧
  (∀ U : Finset A, Disjoint U A₁ → U.card ≤ η → ∑ v ∈ U, f v ≤ (bipNbr r U \ B₁).card) ∧
  (∀ U : Finset A, η + 1 ≤ U.card → U.card ≤ t → ∑ v ∈ U ∪ A₁, f v ≤ (bipNbr r U).card) ∧
  (∀ U : Finset B, U.card ≤ t → U.card ≤ (bipNbr (flip r) U \ A₁).card) ∧
  (∀ (A' : Finset A) (B' : Finset B), A'.card = t → B'.card = t → ∃ a ∈ A', ∃ b ∈ B', r a b)

end RandTreeUniv


