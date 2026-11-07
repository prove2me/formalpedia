-- Prove2me | Definitions.Def_ApproxDegComp_IsMultilinear
-- name    : ApproxDegComp_IsMultilinear
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:30:44.459215+00:00
-- url     : https://prove2.me/theorems/fd33193e-cff4-4b25-bba1-edb164b65fd0
-- title:
--   Multilinear real polynomial
-- statement:
--   A real polynomial in variables indexed by $\iota$ is **multilinear** if every monomial with a nonzero coefficient has every exponent equal to $0$ or $1$, i.e. it is of the form $\sum_{S\subseteq\iota}c_S\prod_{i\in S}x_i$.
--
--   Multilinear polynomials are the canonical representatives of functions on the Boolean cube; Lemma 5 and Lemma 22 ask for multilinear approximants.
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Lemma 5, p.16; Lemma 22, p.22

import Mathlib

namespace ApproxDegComp

/-- **Multilinear polynomial** (used in Lemma 5, p.16, and Lemma 22, p.22).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Lemma 5, p.16: "there exists a multilinear polynomial q …"; Lemma 22, p.22: "Let Q be a
real multilinear polynomial on n disjoint blocks of m bits each."

A real polynomial is multilinear when every monomial occurring in it has every exponent at
most 1.

**Formalization Note** Stated on the support of the `MvPolynomial`: for every monomial `s`
with nonzero coefficient, `s i ≤ 1` for every variable `i`. -/
def IsMultilinear {ι : Type} (q : MvPolynomial ι ℝ) : Prop :=
  ∀ s ∈ q.support, ∀ i, s i ≤ 1

end ApproxDegComp


