-- Prove2me | Definitions.Def_PhyloCSP_IsFraisseLimit
-- name    : PhyloCSP_IsFraisseLimit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:23:52.524211+00:00
-- url     : https://prove2.me/theorems/1c357b84-2ebc-4314-8407-dd77f128992d
-- title:
--   Fraïssé limits of finite binary tree structures
-- statement:
--   A countable binary tree structure $(X,C)$ is a **Fraïssé limit of finite binary tree structures** if
--
--   1. **Universality.** every finite binary tree structure embeds into $(X,C)$, and
--   2. **Homogeneity.** for any two finite induced substructures $Y_1,Y_2$ and any isomorphism $f:Y_1\to Y_2$ there is an automorphism $\hat f$ of $(X,C)$ with $\hat f(y)=f(y)$ for every $y\in Y_1$.
--
--   Embeddings, isomorphisms and automorphisms preserve both truth and falsity of the relation (Definition 7.2).
--
--   **Formalization Note** The structure is required to be countable, nonempty and to satisfy the axioms of `IsTreeRel`. Finite binary tree structures are, up to isomorphism, the patterns on $\{0,\dots,n-1\}$.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Definition 7.3, p.19 (PDF p.21); Definition 7.2, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_PhyloCSP_Pattern

set_option autoImplicit false

namespace PhyloCSP

/-- **The Fraïssé limit of finite binary tree structures (Definition 7.3).**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Definition 7.3, p.19 (PDF p.21): "A countable binary tree
structure F = (Z, C) is called the Fraïssé limit of finite binary tree structures if it satisfies
the following properties: • Universality. Every finite binary tree structure embeds into F.
• Homogeneity. For every two finite induced substructures Y1, Y2 of F and every isomorphism
f : Y1 → Y2, there is an automorphism f̂ of F such that f̂(y) = f(y) for every y ∈ Y1."
Embeddings and isomorphisms preserve both truth and falsity of the relation (Definition 7.2, p.18).

**Formalization Note.** A binary tree structure is a nonempty domain with a relation satisfying
the axioms of Section 7.1 (`IsTreeRel`). Finite binary tree structures are, up to isomorphism, the
patterns on `Fin n` (`n = 0` is included harmlessly). Finite induced substructures are given by
finite subsets `Y₁, Y₂` (the empty one is harmless). -/
def IsFraisseLimit (X : Type) (C : X → X → X → Bool) : Prop :=
  Countable X ∧ Nonempty X ∧ IsTreeRel C ∧
    (∀ (n : ℕ) (P : Pattern (Fin n)), ∃ f : Fin n ↪ X,
      ∀ a b c, C (f a) (f b) (f c) = P.1 a b c) ∧
    (∀ (Y₁ Y₂ : Finset X) (f : ↥Y₁ ≃ ↥Y₂),
      (∀ a b c : ↥Y₁, C ↑(f a) ↑(f b) ↑(f c) = C ↑a ↑b ↑c) →
      ∃ g : X ≃ X, (∀ a b c, C (g a) (g b) (g c) = C a b c) ∧ ∀ y : ↥Y₁, g ↑y = ↑(f y))

end PhyloCSP


