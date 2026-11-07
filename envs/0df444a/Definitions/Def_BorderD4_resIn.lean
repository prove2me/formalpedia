-- Prove2me | Definitions.Def_BorderD4_resIn
-- name    : BorderD4_resIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:58:32.859519+00:00
-- url     : https://prove2.me/theorems/879723e1-2e89-470d-a84d-e43c099362fd
-- title:
--   The resultant $\mathrm{Res}_{x_a}(Q,\partial_{x_a}Q)$ and the fiber $Q(0,b,x_a)$
-- statement:
--   `toUniv a` views a polynomial in $x$ as a polynomial in the distinguished variable $x_a$. `resIn a Q` is the resultant of $Q$ and $\partial_{x_a}Q$ with respect to $x_a$. `fiberAt a b` sends $Q\in F[[\varepsilon]][x]$ to the univariate polynomial $Q(0,b,x_a)\in F[x_a]$.
--
--   **Formalization Note** The resultant is Mathlib's `Polynomial.resultant`, the determinant of a Sylvester matrix, as in Definition 4.11 up to a sign, which affects no statement that uses it.
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Definition 4.11, p.42; Lemma 6.11, p.57

import Mathlib
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

section

variable {σ : Type*} [DecidableEq σ]

/-- A polynomial in `x` viewed as a polynomial in the distinguished variable `x_a` over the same polynomial
ring, with `x_i ↦ x_i` for `i ≠ a` as coefficients. -/
noncomputable def toUniv {R : Type*} [CommRing R] (a : σ) :
    MvPolynomial σ R →+* Polynomial (MvPolynomial σ R) :=
  eval₂Hom (Polynomial.C.comp MvPolynomial.C) fun i =>
    if i = a then Polynomial.X else Polynomial.C (X i)

/-- The resultant `Res_{x_a}(Q, ∂_{x_a} Q)`. Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Definition 4.11, p.42; Lemma 6.11, p.57.

**Formalization Note** This is Mathlib's `Polynomial.resultant` with its default degree arguments, the degrees in
`x_a`. It is the determinant of a Sylvester matrix, as on the page, up to a sign, which affects none of the
statements that use it (vanishing, a power of `ε` times a factor, the degree). -/
noncomputable def resIn {R : Type*} [CommRing R] (a : σ) (Q : MvPolynomial σ R) : MvPolynomial σ R :=
  Polynomial.resultant (toUniv a Q) (Polynomial.derivative (toUniv a Q))

/-- The univariate polynomial `Q(0, b, x_a) ∈ F[x_a]`: `ε ↦ 0`, `x_i ↦ b_i` for `i ≠ a`, and `x_a` kept.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Lemma 6.11, Item 1, p.57. -/
noncomputable def fiberAt {F : Type*} [Field F] (a : σ) (b : σ → F) :
    MvPolynomial σ F⟦X⟧ →+* Polynomial F :=
  eval₂Hom (Polynomial.C.comp PowerSeries.constantCoeff) fun i =>
    if i = a then Polynomial.X else Polynomial.C (b i)

end

end BorderD4


