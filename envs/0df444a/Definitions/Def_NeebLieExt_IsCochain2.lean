-- Prove2me | Definitions.Def_NeebLieExt_IsCochain2
-- name    : NeebLieExt_IsCochain2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:17.710155+00:00
-- url     : https://prove2.me/theorems/ebca4c23-9496-4a6e-b636-e79ad4a72d28
-- title:
--   Continuous alternating cochains $C^2(\mathfrak g,V)$ and $C^3(\mathfrak g,V)$
-- statement:
--   Let $\mathfrak g$ and $V$ be topological vector spaces over $\mathbb K$. For $p\in\{2,3\}$, the space $C^p(\mathfrak g,V)$ of **continuous $p$-cochains** consists of the maps $\omega\colon\mathfrak g^p\to V$ that are
--
--   1. $\mathbb K$-linear in each argument,
--   2. alternating, i.e. $\omega(x_1,\dots,x_p)=0$ whenever two arguments coincide, and
--   3. continuous as maps on the product space $\mathfrak g^p$.
--
--   The module provides the two predicates "$\omega\in C^2(\mathfrak g,V)$" and "$\eta\in C^3(\mathfrak g,V)$". Two-cochains carry the twist $\omega$ of a factor system and the cocycles of $H^2$; three-cochains receive the covariant differential $d_S\omega$.
--
--   **Formalization Note** Cochains are plain functions `g → g → V`, `g → g → g → V` with these predicates. Continuity is *joint* continuity on $\mathfrak g\times\mathfrak g$ (resp. $\mathfrak g\times\mathfrak g\times\mathfrak g$), as in the paper, not separate continuity in each variable. One-cochains $C^1(\mathfrak g,V)=\mathrm{Lin}(\mathfrak g,V)$ are continuous linear maps `g →L[K] V`.
-- source:
--   Neeb, Non-abelian extensions of topological Lie algebras, arXiv:math/0411256v1, Definition I.1, p. 4 ("let C^p(g, V) denote the space of continuous alternating maps g^p → V")

import Mathlib

namespace NeebLieExt

/-- **Continuous Lie algebra 2-cochains** `C²(g, V)`. Neeb, arXiv:math/0411256v1, Definition I.1,
p. 4: "For p ∈ ℕ₀, let C^p(g, V) denote the space of continuous alternating maps g^p → V".

`IsCochain2 K ω` says that `ω : g → g → V` is K-bilinear, alternating (`ω x x = 0`) and jointly
continuous as a map `g × g → V`.

**Formalization Note** Cochains are plain functions together with this predicate. Continuity is
*joint* continuity on `g × g` (the paper's "continuous alternating map g² → V"), not separate
continuity in each argument, so `g →L[K] g →L[K] V` is deliberately not used. -/
def IsCochain2 (K : Type*) {g V : Type*} [CommRing K] [AddCommGroup g] [Module K g]
    [AddCommGroup V] [Module K V] [TopologicalSpace g] [TopologicalSpace V]
    (ω : g → g → V) : Prop :=
  (∀ x, IsLinearMap K (ω x)) ∧ (∀ y, IsLinearMap K (fun x => ω x y)) ∧ (∀ x, ω x x = 0) ∧
    Continuous (fun p : g × g => ω p.1 p.2)

/-- **Continuous Lie algebra 3-cochains** `C³(g, V)`. Neeb, arXiv:math/0411256v1, Definition I.1,
p. 4 (`p = 3`).

`IsCochain3 K η` says that `η : g → g → g → V` is K-linear in each of its three arguments, vanishes
whenever two of its arguments coincide (alternating), and is jointly continuous as a map
`g × g × g → V`.

**Formalization Note** Companion of `IsCochain2` in the same module. The three vanishing
conditions `η x x z = 0`, `η x y y = 0`, `η x y x = 0` cover every pair of equal arguments. -/
def IsCochain3 (K : Type*) {g V : Type*} [CommRing K] [AddCommGroup g] [Module K g]
    [AddCommGroup V] [Module K V] [TopologicalSpace g] [TopologicalSpace V]
    (η : g → g → g → V) : Prop :=
  (∀ x y, IsLinearMap K (η x y)) ∧ (∀ x z, IsLinearMap K (fun y => η x y z)) ∧
    (∀ y z, IsLinearMap K (fun x => η x y z)) ∧
    (∀ x z, η x x z = 0) ∧ (∀ x y, η x y y = 0) ∧ (∀ x y, η x y x = 0) ∧
    Continuous (fun p : g × g × g => η p.1 p.2.1 p.2.2)

end NeebLieExt


