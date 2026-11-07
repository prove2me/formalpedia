-- Prove2me | Definitions.Def_SubmodSparsify_blockMinCut
-- name    : SubmodSparsify_blockMinCut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:21:37.710439+00:00
-- url     : https://prove2.me/theorems/0954257c-bd52-4fcc-affc-9566927dce52
-- title:
--   Definition 2.1 — directed block min-cut function $f^{\to}(A,B)$
-- statement:
--   Let $f : 2^V \to \mathbb R$ be a set function on a finite ground set $V$, and let $A, B \subseteq V$ be disjoint. The **directed block min-cut function** of $f$ is
--
--   $$f^{\to}(A,B) := \min_{T \subseteq V:\ A \subseteq T,\ T \cap B = \emptyset} f(T),$$
--
--   the smallest value of $f$ over the sets that contain $A$ and avoid $B$. When $A = \{u\}$ (or $B = \{v\}$) one writes $f^{\to}(u,B)$ (or $f^{\to}(A,v)$). In particular $f^{\to}(S, \bar S) = f(S)$ for every $S$, where $\bar S = V \setminus S$.
--
--   The block min-cut extends Fujishige's $\min_{T \subseteq S} f(T)$ and the pairwise directed min-cut $f_{u \to v}$ to two disjoint blocks. Its monotonicity and submodularity in each argument (Lemma 3.3) are what make the positive chaining argument of the paper work.
--
--   **Formalization Note** The ground set is a finite type $\alpha$ (the paper's $[n]$ is `Fin n`), and the minimum is the infimum over the finite type of feasible sets $T$. For disjoint $A, B$ this type contains $A$, so the infimum is attained. For overlapping $A, B$ the paper does not define $f^{\to}(A,B)$ and Lean returns the junk value $0$; the mission only applies it to disjoint pairs.
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6…), Definition 2.1, p.8 (PDF p.10); display (13), p.17 (PDF p.19)

import Mathlib

namespace SubmodSparsify

/-- **Directed block min-cut function** (Definition 2.1, p.8; display (13), p.17).

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held).

"Given a submodular function f : {0, 1}ⁿ → R≥0 and disjoint subsets A, B ⊆ [n], define
f→(A, B) := min_{T⊆[n]: A⊆T, T∩B=∅} f(T)."

`blockMinCut f A B` is the minimum of `f T` over all sets `T` with `A ⊆ T` and `T ∩ B = ∅`.

**Formalization Note.**
* The ground set is an arbitrary finite type `α` (the paper's `[n]` is `Fin n`, paper index =
  value + 1); sets are `Finset α`.
* The minimum is the infimum over the finite subtype of feasible `T`. For disjoint `A`, `B`
  the subtype contains `A`, so the infimum is attained and equals the paper's minimum. For
  overlapping `A`, `B` the paper leaves `f→(A, B)` undefined and Lean returns the junk value `0`
  (infimum over an empty type); every statement of the mission applies `blockMinCut` only to
  disjoint pairs.
* When `A = {u}` (or `B = {v}`) the paper writes `f→(u, B)` (or `f→(A, v)`); here these are
  `blockMinCut f {u} B` and `blockMinCut f A {v}`. -/
noncomputable def blockMinCut {α : Type} [Fintype α] [DecidableEq α] (f : Finset α → ℝ)
    (A B : Finset α) : ℝ :=
  ⨅ T : {T : Finset α // A ⊆ T ∧ Disjoint T B}, f T.1

end SubmodSparsify


