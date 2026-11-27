-- Prove2me | Definitions.Def_SubmodMFG_Supplement_DedekindOrder
-- name    : SubmodMFG_Supplement_DedekindOrder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:19:48.591557+00:00
-- url     : https://prove2.me/theorems/4793f1b8-d900-4a4a-98df-c39815da628b
-- title:
--   Dedekind σ-complete and Dedekind super complete ordered sets (Definition A.1)
-- statement:
--   Let $L$ be an ordered set.
--
--   1. $L$ is **Dedekind σ-complete** if every countable nonempty subset that is bounded above (below) has a least upper bound (greatest lower bound).
--   2. $L$ is **Dedekind complete** if every nonempty subset bounded above (below) has a least upper bound (greatest lower bound).
--   3. $L$ is **Dedekind super complete** if every nonempty subset $S$ that is bounded above has a least upper bound $b$ and a countable subset $C\subseteq S$ whose least upper bound is also $b$, and dually for subsets bounded below and greatest lower bounds.
--   4. $L$ is **complete** if every nonempty subset has a least upper bound and a greatest lower bound.
--   5. A set $M\subseteq L$ is directed upwards (downwards) when every pair $x,y\in M$ has some $z\in M$ with $x\vee y\le z$ (respectively, $z\le x\wedge y$).
--
--   These are the completeness notions of Appendix A used in §3 for lattices of flows of measures, which are in general not complete lattices.
--
--   **Formalization Note** Both notions are stated for a preorder, so that they apply to sets of almost-everywhere classes represented by functions; least upper and greatest lower bounds are invariant under the identification of equivalent elements. Unlike the published `SubmodMFG.DedekindSuperComplete`, no complete-lattice structure is assumed, and the existence of the bound (presupposed by "the same least upper bound") is part of the definition.
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, Appendix A, Definition A.1 a), p.33

import Mathlib

namespace SubmodMFG.Supplement

/-- **Dedekind σ-complete** (Definition A.1 a)), for an ordered set that need not be complete.
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, Appendix A, Definition A.1 a), p.33: "We say that L is Dedekind σ-complete
if every countable nonempty subset, that is bounded above or below, has a least upper bound or a
greatest lower bound, respectively."

**Formalization Note.** Stated for a `Preorder` so that it applies both to lattices (Lemma A.3)
and to sets of a.e.-classes represented by functions (Theorem 3.3), where the order is a
preorder whose antisymmetrization is the paper's lattice; `IsLUB`/`IsGLB` are invariant under
that identification. -/
def DedekindSigmaComplete (α : Type*) [Preorder α] : Prop :=
  ∀ C : Set α, C.Countable → C.Nonempty →
    (BddAbove C → ∃ b, IsLUB C b) ∧ (BddBelow C → ∃ b, IsGLB C b)

/-- **Dedekind complete** (Definition A.1 a)): every nonempty subset bounded above (below)
has a least upper (greatest lower) bound. -/
def DedekindCompleteOrd (α : Type*) [Preorder α] : Prop :=
  ∀ S : Set α, S.Nonempty →
    (BddAbove S → ∃ b, IsLUB S b) ∧ (BddBelow S → ∃ b, IsGLB S b)

/-- **Dedekind super complete** (Definition A.1 a)), for an ordered set that need not be
complete. Appendix A, Definition A.1 a), p.33: "We say that L is Dedekind super complete if
every nonempty subset, that is bounded above or below, has a countable subset with the same
least upper bound or greatest lower bound, respectively."

**Formalization Note.** "The same least upper bound" presupposes that the bound exists, so the
definition asks for a least upper bound `b` of `S` and a countable `C ⊆ S` with least upper bound
`b` (dually below). Unlike the published `SubmodMFG.DedekindSuperComplete`, no
`CompleteLattice` structure is assumed and the boundedness proviso is kept. -/
def DedekindSuperCompleteOrd (α : Type*) [Preorder α] : Prop :=
  (∀ S : Set α, S.Nonempty → BddAbove S →
      ∃ b, IsLUB S b ∧ ∃ C ⊆ S, C.Countable ∧ IsLUB C b) ∧
  (∀ S : Set α, S.Nonempty → BddBelow S →
      ∃ b, IsGLB S b ∧ ∃ C ⊆ S, C.Countable ∧ IsGLB C b)

/-- **Complete** (Definition A.1 a)): every nonempty subset has a least upper bound and a
greatest lower bound. -/
def CompleteOrd (α : Type*) [Preorder α] : Prop :=
  ∀ S : Set α, S.Nonempty → (∃ b, IsLUB S b) ∧ ∃ b, IsGLB S b

/-- **Directed upwards** (Definition A.1 b)): every pair in `M` has an element of `M` above
their join. -/
def DirectedUpOrd (α : Type*) [Lattice α] (M : Set α) : Prop :=
  ∀ x ∈ M, ∀ y ∈ M, ∃ z ∈ M, x ⊔ y ≤ z

/-- **Directed downwards** (Definition A.1 b)): every pair in `M` has an element of `M` below
their meet. -/
def DirectedDownOrd (α : Type*) [Lattice α] (M : Set α) : Prop :=
  ∀ x ∈ M, ∀ y ∈ M, ∃ z ∈ M, z ≤ x ⊓ y

end SubmodMFG.Supplement


