-- Prove2me | Definitions.Def_RandTreeUniv_IsFMatching
-- name    : RandTreeUniv_IsFMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:10:15.430717+00:00
-- url     : https://prove2.me/theorems/3c2fab1c-80f4-486c-8b8a-cef7352085aa
-- title:
--   $f$-matching from $A$ to $B$ (Definition 2.5)
-- statement:
--   Let $(A,B)$ be a bipartite graph with disjoint parts and let $f:A\to\mathbb N$. An **$f$-matching from $A$ to $B$** is a family of vertex-disjoint stars $(S_v)_{v\in A}$ such that each $S_v$ is centred at $v$ and has exactly $f(v)$ leaves, all of them in $B$ and adjacent to $v$.
--
--   Equivalently, it is a choice of pairwise disjoint sets $L_v\subseteq B$ with $|L_v|=f(v)$ and every element of $L_v$ adjacent to $v$. When $f\equiv1$ this is a matching saturating $A$. It is the object produced by Theorem 2.6 and Lemma 2.8.
--
--   **Formalization Note** The star at $v$ is recorded by its leaf set $L_v$; vertex-disjointness of the stars is pairwise disjointness of the leaf sets because the centres are distinct and $A$, $B$ are disjoint.
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), Definition 2.5, p.11 (PDF 12)

import Mathlib

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- An `f`-matching from `A` to `B` (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), Definition 2.5, p.11 (PDF 12)): a family of
vertex-disjoint stars `(S_v)_{v ∈ A}` where `S_v` is centred at `v` and has exactly `f(v)` leaves,
all in `B`. The star at `v` is recorded by its leaf set `S v ⊆ B`.

**Formalization Note** The bipartite graph is the relation `r : A → B → Prop`. Centres are
distinct vertices of `A`, and `A`, `B` are disjoint types, so vertex-disjointness of the stars is
pairwise disjointness of the leaf sets. -/
def IsFMatching {A B : Type*} (r : A → B → Prop) (f : A → ℕ) (S : A → Finset B) : Prop :=
  (∀ v, (S v).card = f v) ∧ (∀ v, ∀ w ∈ S v, r v w) ∧ (∀ v v', v ≠ v' → Disjoint (S v) (S v'))

end RandTreeUniv


