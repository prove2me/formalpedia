-- Prove2me | Definitions.Def_DiscreteConvex_LConvexSets_LConvexSet
-- name    : DiscreteConvex_LConvexSets_LConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:34:53.900778+00:00
-- url     : https://prove2.me/theorems/d298411c-2623-489c-875c-90d13f2c99c2
-- title:
--   L-convex set (axioms SBS[Z], TRS[Z])
-- statement:
--   A set $D \subseteq \mathbb Z^V$ is an **L-convex set** if it satisfies the sublattice axiom **(SBS[Z])**: $p, q \in D \Rightarrow p \vee q,\ p \wedge q \in D$ (componentwise max/min), and the translation axiom **(TRS[Z])**: $p \in D \Rightarrow p \pm \mathbf 1 \in D$. Nonemptiness is required separately.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.121, axioms (SBS[Z]), (TRS[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.121, axioms (SBS[Z]), (TRS[Z])

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.121, axioms (SBS[Z]) and (TRS[Z]): L-convex
sets, in `DiscreteConvex.LConvexSets`.
-/

namespace DiscreteConvex.LConvexSets

/-- A set `D ⊆ Zⱽ` is an **L-convex set** if it satisfies the sublattice axiom
**(SBS[Z])**: `p, q ∈ D ⟹ p ∨ q, p ∧ q ∈ D` and the translation axiom **(TRS[Z])**:
`p ∈ D ⟹ p ± 1 ∈ D`. Nonemptiness is required separately (the book: "a nonempty set of integer
points"). -/
def LConvexSet {V : Type*} (D : Set (V → ℤ)) : Prop :=
  (∀ p ∈ D, ∀ q ∈ D, p ⊔ q ∈ D ∧ p ⊓ q ∈ D) ∧
  (∀ p ∈ D, (fun v => p v + 1) ∈ D ∧ (fun v => p v - 1) ∈ D)

end DiscreteConvex.LConvexSets


