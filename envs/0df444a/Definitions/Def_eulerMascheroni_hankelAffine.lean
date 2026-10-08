-- Prove2me | Definitions.Def_eulerMascheroni_hankelAffine
-- name    : eulerMascheroni_hankelAffine
-- status  : Definition
-- author  : @shivm
-- created : 2026-10-04T13:51:47.739988+00:00
-- url     : https://prove2.me/theorems/2103efb0-5ddd-4f03-ac9d-89b6e1fb1fda
-- title:
--   Hankel matrix with entries affine in $X$
-- statement:
--   For $h\in\mathbb N$ and rational sequences $a=(a_k)_{k\ge0}$, $b=(b_k)_{k\ge0}$, the matrix $\mathrm{hankelAffine}(h,a,b)\in\mathbb Q[X]^{h\times h}$ is the Hankel matrix
--   $$\big(a_{i+j}+b_{i+j}\,X\big)_{0\le i,j<h}.$$
--   Its entries are affine polynomials in $X$, so its determinant is a polynomial of degree at most $h$. This is the shape of the matrix $G_K(X)$ in Fauzan's proof that $\zeta(5)$ is irrational: there the entries $\mu_X(\cdot)$ of a rational functional are affine in the variable $X$, and at $X=\zeta(5)$ the matrix becomes a positive moment (Gram) matrix.
-- source:
--   A. Fauzan, "ζ(5) is irrational" (2026), https://zenodo.org/records/22826419, §2.1, eq. (2.4) (the Hankel matrix $G_K(X)$ with entries affine in $X$); Lean development https://github.com/mo271/zeta5 (Apery/Construction.lean).

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Matrix.Basic

open Polynomial

namespace EulerMascheroni.Hankel

/-- The `h × h` Hankel matrix whose `(i, j)` entry is the affine polynomial
`a (i + j) + b (i + j) * X ∈ ℚ[X]`. -/
noncomputable def hankelAffine (h : ℕ) (a b : ℕ → ℚ) : Matrix (Fin h) (Fin h) ℚ[X] :=
  Matrix.of fun i j => C (a ((i : ℕ) + j)) + C (b ((i : ℕ) + j)) * X

end EulerMascheroni.Hankel


