-- Prove2me | Definitions.Def_AlgebraicGeometry_HilbertFunctor
-- name    : AlgebraicGeometry_HilbertFunctor
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/009b9cdf-ee90-5f89-80c4-bc8275f3a5c5
-- title:
--   Points of the Hilbert functor of projective space
-- statement:
--   Over a commutative ring $A$ and for $n : \mathbb{N}$, the graded pieces of a homogeneous quotient are given a name: for an ideal $I$ of $A[x_0,\dots,x_n] =$ `MvPolynomial (Fin (n+1)) A` and $d : \mathbb{N}$, `piece I d` is the quotient of the $A$-submodule `homogeneousSubmodule (Fin (n+1)) A d` of degree-$d$ homogeneous polynomials by the preimage of $I$ (viewed as an $A$-submodule via `restrictScalars`) under the inclusion of that submodule — that is, the $A$-module of degree-$d$ forms modulo the degree-$d$ forms lying in $I$.
--
--   The structure `Point A n h`, for $h : \mathbb{N} \to \mathbb{N}$, is the type of $A$-valued points of the Hilbert functor with Hilbert function $h$. Its data is a single ideal $I \subseteq A[x_0,\dots,x_n]$, and its remaining fields are propositions: $I$ is homogeneous in the sense that for every $p \in I$ and every $d$ the homogeneous component `homogeneousComponent d p` again lies in $I$; each `piece I d` is a finite $A$-module; each `piece I d` is a projective $A$-module; and for every $d$ and every prime $p$ of $A$, `Module.rankAtStalk (piece I d) p` equals $h(d)$, so the pieces have constant rank prescribed by $h$. Since the three conditions are proof-irrelevant, two points with the same ideal coincide; this is recorded as an `@[ext]` lemma.
--
--   Finally, `hilbertFunctionOf n P D₀`, for a rational polynomial $P$ and a truncation bound $D_0$, is the function sending $d$ to $\binom{n+d}{n}$ when $d < D_0$ and to the non-negative part of $\lfloor P(d) \rfloor$ otherwise: the Hilbert function of an ideal generated in degrees $\geq D_0$ whose Hilbert polynomial is $P$.
--
--   **Relation to Mathlib.** Mathlib has no Hilbert functor or Hilbert scheme; this is the project's own vocabulary, phrased in the same style as Mathlib's `Module.Grassmannian` (a submodule with finite projective quotient of constant `Module.rankAtStalk`) and built from Mathlib's `MvPolynomial.homogeneousSubmodule` and `MvPolynomial.homogeneousComponent`.
--
--   **Where it is used.** These definitions supply the language in which the project states and uses the Hilbert functor of $\mathbb{P}^n$ — its points over a base ring, base change of the defining ideal, and its representability by a projective scheme together with the universal family — as part of the moduli-theoretic infrastructure underlying the modularity arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_HilbertFunctor.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace AlgebraicGeometry.HilbertFunctor

open MvPolynomial

variable {A : Type*} [CommRing A] {n : ℕ}

abbrev piece (I : Ideal (MvPolynomial (Fin (n + 1)) A)) (d : ℕ) : Type _ :=
  ↥(homogeneousSubmodule (Fin (n + 1)) A d) ⧸
    Submodule.comap (homogeneousSubmodule (Fin (n + 1)) A d).subtype (I.restrictScalars A)

variable (A n)

structure Point (h : ℕ → ℕ) where

  I : Ideal (MvPolynomial (Fin (n + 1)) A)

  homogeneous : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I

  finite_piece : ∀ d : ℕ, Module.Finite A (piece I d)

  projective_piece : ∀ d : ℕ, Module.Projective A (piece I d)

  rankAtStalk_piece : ∀ (d : ℕ) (p : PrimeSpectrum A), Module.rankAtStalk (piece I d) p = h d

variable {A}

@[ext] theorem Point.ext {h : ℕ → ℕ} {P Q : Point A n h} (e : P.I = Q.I) : P = Q := by
  cases P; cases Q; cases e; rfl

noncomputable def hilbertFunctionOf (P : Polynomial ℚ) (D₀ : ℕ) : ℕ → ℕ :=
  fun d => if d < D₀ then Nat.choose (n + d) n else Int.toNat ⌊P.eval (d : ℚ)⌋

end AlgebraicGeometry.HilbertFunctor


