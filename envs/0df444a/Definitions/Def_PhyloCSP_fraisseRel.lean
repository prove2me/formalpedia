-- Prove2me | Definitions.Def_PhyloCSP_fraisseRel
-- name    : PhyloCSP_fraisseRel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:22:10.24489+00:00
-- url     : https://prove2.me/theorems/8aac30b0-8519-4b0d-a5e1-d883c3eb0943
-- title:
--   The concrete Fraïssé limit $(Z,C)$ of Definition 7.5
-- statement:
--   Let $Z$ be the set of all finite subsets of $\mathbb Q$, the empty set included. Each leaf $A\in Z$ is identified with the pair $(+\infty,A)$, and branchpoints $(q,A)$ are added for $q\in\mathbb Q$ and finite $A\subseteq(-\infty,q)\cap\mathbb Q$, with the ancestry order
--   $$
--   (q,A)<(q',A')\iff q>q'\ \text{and}\ A\cap(-\infty,q')=A'
--   $$
--   ($u<v$ means $v$ is a proper ancestor of $u$). For distinct leaves $A,B$ with $r=\min(A\triangle B)$, the lowest common ancestor is $A\vee B=(r,A\cap(-\infty,r))$ (eq. (4)). The rooted-triplet relation is
--   $$
--   C(A;B,E)\iff B\vee E<A\vee B=A\vee E\qquad(A,B,E\text{ distinct}),
--   $$
--   and false when arguments repeat (eq. (5)). Appendix B.1 shows that this is equivalent to $\min(A\triangle E)<\min(B\triangle E)$ and that $(Z,C)$ is the Fraïssé limit of finite binary tree structures.
--
--   **Formalization Note** $Z$ is a type synonym of finite sets of rationals carrying the discrete topology. Only the relation $C$ is structure; the rational coordinates are a realization.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Definition 7.5 and eqs. (4)–(5), p.20 (PDF p.22); Appendix B.1, pp.44–45 (PDF pp.46–47)

import Mathlib

set_option autoImplicit false

namespace PhyloCSP

/-- **The leaves `Z` of the concrete Fraïssé limit (Definition 7.5).**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Definition 7.5, p.20 (PDF p.22): "Let Z be the collection of
all finite subsets of Q, including the empty set."

**Formalization Note.** `Z` is a type synonym of `Finset ℚ`, so that it can carry the discrete
topology used for the pointwise-convergence topology on `Aut(F)` (Section 7.1, p.19) without
putting a topology on `Finset ℚ` itself. -/
def Z : Type := Finset ℚ

instance : DecidableEq Z := inferInstanceAs (DecidableEq (Finset ℚ))
instance : Encodable Z := inferInstanceAs (Encodable (Finset ℚ))
instance : Countable Z := inferInstanceAs (Countable (Finset ℚ))
instance : Inhabited Z := inferInstanceAs (Inhabited (Finset ℚ))
instance : TopologicalSpace Z := ⊥
instance : DiscreteTopology Z := ⟨rfl⟩

/-- The vertices of the tree-like structure `F̂` of Definition 7.5: pairs `(q, A)` with
`q ∈ ℚ ∪ {+∞}`; the leaf `A ∈ Z` is identified with `(+∞, A)`. -/
abbrev Vtx : Type := WithTop ℚ × Finset ℚ

/-- The ancestry order of Definition 7.5: "(q, A) < (q′, A′) if q > q′ and A ∩ (−∞, q′) = A′. Here
u < v means that v is a proper ancestor of u". -/
def VtxLt (u v : Vtx) : Prop :=
  v.1 < u.1 ∧ u.2.filter (fun a : ℚ => ((a : ℚ) : WithTop ℚ) < v.1) = v.2

instance (u v : Vtx) : Decidable (VtxLt u v) := by unfold VtxLt; infer_instance

/-- The lowest common ancestor of two distinct leaves, eq. (4): "For distinct leaves A, B, let
r = min(A △ B) … Then A ∨ B = (r, A ∩ (−∞, r))". (For `A = B`, `min ∅ = +∞` and the value is the
leaf `(+∞, A)` itself.) -/
def leafJoin (A B : Finset ℚ) : Vtx :=
  ((symmDiff A B).min, A.filter (fun a : ℚ => ((a : ℚ) : WithTop ℚ) < (symmDiff A B).min))

/-- **The rooted-triplet relation `C` of the concrete Fraïssé limit, eq. (5).**

Definition 7.5, p.20 (PDF p.22): "On distinct leaves, we define the rooted triplet relation by
C(A; B, E) if B ∨ E < A ∨ B = A ∨ E, (5) and let it be false when arguments repeat."

**Formalization Note.** The rational coordinates are only a realization; automorphisms are
required to preserve `fraisseRel` only (`AutF`). -/
def fraisseRel (A B E : Z) : Bool :=
  decide (A ≠ B ∧ A ≠ E ∧ B ≠ E ∧ VtxLt (leafJoin B E) (leafJoin A B) ∧
    leafJoin A B = leafJoin A E)

end PhyloCSP


