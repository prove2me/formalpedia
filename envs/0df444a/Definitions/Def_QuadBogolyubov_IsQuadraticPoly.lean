-- Prove2me | Definitions.Def_QuadBogolyubov_IsQuadraticPoly
-- name    : QuadBogolyubov_IsQuadraticPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:21.057794+00:00
-- url     : https://prove2.me/theorems/2c5dcfce-05a9-43c6-a29f-cc5d2ac8d873
-- title:
--   Quadratic polynomials and polynomials of degree at most one on $\mathbb F_2^n$
-- statement:
--   A function $q:\mathbb F_2^n\to\mathbb F_2$ is a **quadratic polynomial** if it is the evaluation of a polynomial in $n$ variables over $\mathbb F_2$ of total degree at most two; constant and linear terms are allowed. It is an **affine polynomial** if the total degree is at most one.
--
--   These are the test functions of the seven-point identity in the quadratic Bogolyubov theorem and the building blocks of quadratic varieties.
--
--   **Formalization Note** $\mathbb F_2^n$ is `Fin n → ZMod 2`. A quadratic function on an affine subspace $V$ is represented by a global quadratic polynomial agreeing with it on $V$; the paper notes (p.68) that every such function extends.
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), §1, p.2; §3, p.9; p.68

import Mathlib

set_option autoImplicit false

namespace QuadBogolyubov

/-- A function `q : 𝔽₂ⁿ → 𝔽₂` is a **quadratic polynomial** if it is the evaluation of a
polynomial in `n` variables over `𝔽₂` of total degree at most two (constant and linear terms
allowed).

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…), §1, p.2
("for every quadratic polynomial q : F₂ⁿ → F₂") and §3, p.9 ("quadratic functions").

**Formalization Note.** `𝔽₂ⁿ` is `Fin n → ZMod 2`. A quadratic function `q : V → 𝔽₂` on an
affine subspace `V` is represented by a global quadratic polynomial agreeing with it on `V`;
every quadratic function on `V` extends to one (p.68). -/
def IsQuadraticPoly {n : ℕ} (q : (Fin n → ZMod 2) → ZMod 2) : Prop :=
  ∃ p : MvPolynomial (Fin n) (ZMod 2), p.totalDegree ≤ 2 ∧ ∀ x, q x = MvPolynomial.eval x p

/-- A function `p : 𝔽₂ⁿ → 𝔽₂` is a **polynomial of degree at most one** (an affine function:
a linear function plus a constant). Used for the "quadratic parts are linearly independent"
condition of §3, p.9. -/
def IsAffinePoly {n : ℕ} (p : (Fin n → ZMod 2) → ZMod 2) : Prop :=
  ∃ P : MvPolynomial (Fin n) (ZMod 2), P.totalDegree ≤ 1 ∧ ∀ x, p x = MvPolynomial.eval x P

end QuadBogolyubov


