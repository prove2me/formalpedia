-- Prove2me | Definitions.Def_ChapterA
-- name    : ChapterA
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T05:37:44.266899+00:00
-- url     : https://prove2.me/theorems/79428996-fab2-4f3a-84dc-5a0ef93a9e55
-- title:
--   Chapter A
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA.lean`): generated def bundle for ChapterA. See BookProof/ChapterA.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA.lean

import Mathlib


/-!
# Chapter A — Systems on real and complex Hilbert spaces (foundational core)

This file formalizes the self-contained foundational core of Chapter A of
`book.tex` (see `FORMALIZATION_ROADMAP.md` §A.0–A.2): the notion of a **system**
`(M, V)`, its commutant, subsystems and irreducibility, normal systems, and the
two elementary high-value results the roadmap marks "do in Lean directly":

* **Lemma 26** — for a *normal* system, the orthogonal complement of a subsystem
  is again a subsystem.
* **Lemma 27** — a **Schur** normal system (one whose self-adjoint commuting
  operators are all scalars) is *irreducible*.

The genuinely external representation-theoretic inputs (Schur for unitary /
imprimitivity representations, Weyl complete reducibility, Mackey imprimitivity,
Wigner little-group theory, Pauli's fundamental theorem) are, per the roadmap,
introduced as *named hypotheses* where used — never as `axiom`s.  Here the "Schur"
property is taken as an explicit hypothesis of Lemma 27, matching Def. 13.
-/

open scoped ComplexConjugate InnerProductSpace

namespace BookProof.ChapterA

/-- **Def 1 (System).** A system `(M, V)`: a set `M` of bounded endomorphisms of a
Hilbert space `V` over `𝔽`. -/
structure System (𝔽 : Type*) [RCLike 𝔽] (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace 𝔽 V] [CompleteSpace V] where
  /-- The set of bounded operators comprising the system. -/
  ops : Set (V →L[𝔽] V)

namespace System

variable {𝔽 : Type*} [RCLike 𝔽] {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace 𝔽 V] [CompleteSpace V]

/-- An operator `S` **commutes with** the system `M` iff it commutes with every
`m ∈ M` (composition is `*` in the endomorphism ring). -/
def Commutes (M : System 𝔽 V) (S : V →L[𝔽] V) : Prop :=
  ∀ m ∈ M.ops, S * m = m * S

/-- **Def 24 (normal system).** `M` is **normal** iff it is closed under the
adjoint `†`. -/
def IsNormal (M : System 𝔽 V) : Prop :=
  ∀ m ∈ M.ops, ContinuousLinearMap.adjoint m ∈ M.ops

/-- **Def 7 (subsystem).** A closed subspace `W` is a **subsystem** of `(M, V)`
iff it is invariant under every `m ∈ M`. -/
def IsSubsystem (M : System 𝔽 V) (W : Submodule 𝔽 V) : Prop :=
  IsClosed (W : Set V) ∧ ∀ m ∈ M.ops, ∀ w ∈ W, m w ∈ W

/-- **Def 7 (irreducibility).** `(M, V)` is **irreducible** iff its only
subsystems are `⊥` and `⊤`. -/
def IsIrreducible (M : System 𝔽 V) : Prop :=
  ∀ W : Submodule 𝔽 V, IsSubsystem M W → W = ⊥ ∨ W = ⊤

/-
**Lemma 26.** For a *normal* system `M`, the orthogonal complement of a
subsystem is a subsystem.
-/


/-
**Lemma 27.** A **Schur** normal system is irreducible.  Here the Schur
hypothesis (Def. 13: the algebra of self-adjoint operators commuting with `M`
is `𝔽`) is stated directly: every self-adjoint operator commuting with `M` is a
scalar multiple of the identity.
-/


end System

end BookProof.ChapterA


