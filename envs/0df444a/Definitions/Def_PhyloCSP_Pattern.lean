-- Prove2me | Definitions.Def_PhyloCSP_Pattern
-- name    : PhyloCSP_Pattern
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:22:54.242543+00:00
-- url     : https://prove2.me/theorems/ecb1fbd9-4dc7-4925-ae82-c6e3d5f30a01
-- title:
--   Patterns: rooted binary trees on a labeled leaf set
-- statement:
--   For a finite set $S$ of leaf labels, a **pattern** is a rooted binary tree with leaf set exactly $S$, considered up to isomorphism preserving the root and every leaf label. A pattern is represented by its rooted-triplet relation, a binary tree structure on $S$; by Section 1, each pattern is determined by its rooted triplets, and by Section 7.1 every relation satisfying the axioms comes from a tree.
--
--   Two operations are attached:
--
--   1. **Pull-back** $T\mapsto T\circ f$ along an injection $f:Y\hookrightarrow X$: the induced tree on the image of $f$, relabeled by $f$. For an inclusion $A\subseteq S$ this is the **restriction** $T{\restriction}A$ (Section 1: $a\mid_T bc$ iff $a\mid_{T\restriction A} bc$ for distinct $a,b,c\in A$); for $f$ from $\{x_1,\dots,x_k\}$ it is the pattern of the leaves $f(x_1),\dots,f(x_k)$ in $T$.
--   2. **Relabeling** along a bijection $\sigma : X\to Y$.
--
--   The inclusion $A\hookrightarrow S$ of finite sets of natural numbers is also recorded.
--
--   **Formalization Note** A pattern on $X$ is a subtype of relations satisfying `IsTreeRel`. On the empty type there is exactly one pattern (the empty relation), which is never used as a tree.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Section 1, p.1 (PDF p.3): restriction $T\restriction S$ and patterns; Section 7.1, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_PhyloCSP_IsTreeRel

set_option autoImplicit false

namespace PhyloCSP

/-- **Patterns: finite rooted binary trees up to label-preserving isomorphism.**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Section 1, p.1 (PDF p.3): "For a fixed set of leaf labels
S = {x1, . . . , xk}, a pattern is a rooted binary tree with leaf set exactly S, considered up to
isomorphism preserving the root and every leaf label." Restriction `T↾S` (p.1) and the pattern
of a set of leaves in a tree are recorded by `Pattern.comap`; relabeling (Definition 1.5) by
`Pattern.relabel`.

**Formalization Note.** A pattern on the leaf set `X` is represented by its rooted-triplet
relation, i.e. a relation satisfying the axioms of `IsTreeRel` (Section 7.1, p.18). This is the
paper's own identification: "each pattern is uniquely determined by its rooted triplet relations"
(p.1) and the axioms "characterize binary tree structures" (p.18). On the empty type there is
exactly one pattern (the empty relation); it is never used as a tree. Restriction to a nonempty
subset `A ⊆ S` is `comap` along the inclusion: "a |T bc if and only if a |T↾S bc for all
distinct a, b, c ∈ S" (p.1). -/
abbrev Pattern (X : Type) : Type := {C : X → X → X → Bool // IsTreeRel C}

/-- Pull a pattern back along an injection `f : Y ↪ X`: the induced tree on the image,
relabeled by `f`. With `f` an inclusion this is the restriction `T↾A`; with `f : Fin k ↪ X` it is
the pattern of the leaves `f 0, …, f (k-1)` in `T`. -/
def Pattern.comap {X Y : Type} (f : Y ↪ X) (T : Pattern X) : Pattern Y :=
  ⟨fun a b c => T.1 (f a) (f b) (f c), T.2.comap f⟩

/-- Relabel the leaves of a pattern along a bijection `σ : X ≃ Y`. -/
def Pattern.relabel {X Y : Type} (σ : X ≃ Y) (T : Pattern X) : Pattern Y :=
  T.comap σ.symm.toEmbedding

/-- The inclusion `↥A ↪ ↥S` of finite leaf sets `A ⊆ S ⊆ ℕ`. -/
def inclEmb {S A : Finset ℕ} (h : A ⊆ S) : ↥A ↪ ↥S :=
  ⟨fun a => ⟨a.1, h a.2⟩, by
    intro a b hab
    simp only [Subtype.mk.injEq] at hab
    exact Subtype.ext hab⟩

end PhyloCSP


