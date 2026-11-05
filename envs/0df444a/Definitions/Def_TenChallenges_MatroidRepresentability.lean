-- Prove2me | Definitions.Def_TenChallenges_MatroidRepresentability
-- name    : TenChallenges_MatroidRepresentability
-- status  : Definition
-- author  : @utkuokur
-- created : 2026-11-04T21:54:28.695322+00:00
-- url     : https://prove2.me/theorems/940e9a77-7b9c-4cb5-b2a8-6aace9c00efb
-- title:
--   Representability over $\mathrm{GF}(p^m)$, excluded minors, matroid isomorphism
-- statement:
--   The definitions behind Challenge 2 of the Ten Challenges benchmark, on top of Mathlib's matroids (`Matroid α`, ground set $E\subseteq\alpha$, independence predicate) and finite fields.
--
--   1. **Representability.** For a prime $p$ and $m\ge 1$, a matroid $M$ is *$\mathrm{GF}(p^m)$-representable* if there are a vector space $W$ over $\mathrm{GF}(p^m)$ and a map $v\colon\alpha\to W$ such that for every set $I\subseteq\alpha$,
--   $$I \text{ is independent in } M \iff (v(x))_{x\in I} \text{ is linearly independent over } \mathrm{GF}(p^m).$$
--   Since sets meeting the complement of the ground set are never independent, such a $v$ vanishes outside $E$.
--   2. **Excluded minors.** For a property $P$ of matroids on $\alpha$, $M$ is an *excluded minor for $P$* if $M$ fails $P$ while every strict minor of $M$ (in Mathlib's minor order $N <_m M$) satisfies $P$.
--   3. **Isomorphism.** Matroids $M$ on $\alpha$ and $N$ on $\beta$ are *isomorphic* if some bijection $e\colon E(M)\to E(N)$ carries a subset $I\subseteq E(M)$ to an independent set of $N$ exactly when $I$ is independent in $M$.
--   4. **Bounded excluded-minor count.** $\mathrm{ExcludedMinorsAtMost}(p,m,B)$ holds if there is a finite set $S$ of at most $B$ matroids on the ground type $\mathbb N$ such that every finite matroid $M$ (on any ground type in the lowest universe) which is an excluded minor for $\mathrm{GF}(p^m)$-representability is isomorphic to a member of $S$. Equivalently, the class of $\mathrm{GF}(p^m)$-representable matroids has at most $B$ excluded minors up to isomorphism.
--
--   These definitions are reusable for any excluded-minor statement about representable matroids.
--
--   **Formalization Note.** The field is Mathlib's `GaloisField p m`, which requires the instance `Fact p.Prime`. Linear independence is `LinearIndepOn`. The representatives in $S$ live on the fixed ground type $\mathbb N$ so that $S$ can be a `Finset`.
-- source:
--   Ten Challenges repository, file Defs_and_Lems/MatroidRepresentability.lean (commit ff14a56), https://github.com/TenChallenges/ten-challenges/blob/main/Defs_and_Lems/MatroidRepresentability.lean; definitions following J. Oxley, Matroid Theory, 2nd ed., Chapters 1, 3 and 6.

import Mathlib.Combinatorics.Matroid.Minor.Order
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.LinearIndependent.Defs

open Matroid

variable {α β : Type*}

/-- `M` is representable over the Galois field `GF(pᵐ)`: some assignment of
vectors to the elements of `M` makes a set independent exactly when its vectors
are linearly independent. -/
def IsGFRepresentable (p m : ℕ) [Fact p.Prime] (M : Matroid α) : Prop :=
  ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (GaloisField p m) W) (v : α → W),
    ∀ I, M.Indep I ↔ LinearIndepOn (GaloisField p m) v I

/-- `M` fails `P`, but every proper minor satisfies `P`. -/
def IsExcludedMinorFor (P : Matroid α → Prop) (M : Matroid α) : Prop :=
  ¬ P M ∧ ∀ N : Matroid α, N <m M → P N

/-- `M` and `N` are isomorphic: a bijection between their ground sets carries
independent sets exactly to independent sets. -/
def Matroid.IsIso (M : Matroid α) (N : Matroid β) : Prop :=
  ∃ e : M.E ≃ N.E, ∀ I : Set M.E,
    M.Indep (Subtype.val '' I) ↔ N.Indep (Subtype.val '' (e '' I))

/-- Given a prime power `pᵐ` and a number `B`, the following says that the
class of `GF(pᵐ)`-representable matroids has at most `B` excluded minors, up
to isomorphism. Equivalently, there is a set `S` of at most `B` matroids that
contains, up to isomorphism, every excluded minor for `GF(pᵐ)`-representability. -/
def ExcludedMinorsAtMost (p m : ℕ) [Fact p.Prime] (B : ℕ) : Prop :=
  ∃ S : Finset (Matroid ℕ), S.card ≤ B ∧
    ∀ {β : Type} (M : Matroid β), M.Finite →
      IsExcludedMinorFor (IsGFRepresentable p m) M →
      ∃ N ∈ S, N.IsIso M


