-- Prove2me | Definitions.Def_TranscendenceTheory_BoundedBivariateSystem
-- name    : TranscendenceTheory_BoundedBivariateSystem
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-07T09:28:38.980258+00:00
-- url     : https://prove2.me/theorems/0115c89d-f656-4441-b0ee-1cda763d2c0b
-- title:
--   Bounded polynomial systems for auxiliary-function arguments
-- statement:
--   Fix complex numbers $\theta,\nu$, real constants $a,c$, and a nonnegative integer $N$. A bounded bivariate system consists of an $m\times n$ matrix $B$ and a $q\times n$ matrix $Q$ over $\mathbb Z[X,Y]$, with degree bounds $D,E$, satisfying
--
--   $$
--   n>0,\quad 8m\le n,\quad D,E\le aN,\quad
--   n(E+1)(D+1)\le e^{aN}.
--   $$
--
--   Every entry of both matrices has $X$-degree at most $D$, $Y$-degree at most $E$, and integer coefficients of absolute value at most $e^{aN}$. For every nonzero polynomial vector $p$ with those degree bounds, coefficient bound $e^{2aN}$, and $Bp=0$ as a polynomial identity, some row of $Q$ satisfies
--
--   $$
--   0<\left|\sum_i Q_{ri}(\theta,\nu)p_i(\theta,\nu)\right|
--   \le e^{-cN^2\log N}.
--   $$
--
--   The matrices encode vanishing equations and candidate derivative values in an auxiliary-function proof. The final property is an explicit obligation for a system constructor: the record does not prove the analytic interpolation or zero estimate. A separate coefficient-selection theorem constructs a bounded nonzero vector in the kernel.
--
--   **Formalization Note.** The outer polynomial variable is $Y$. Matrix sizes and degree bounds may depend on $N$. The test matrix is chosen before the coefficient vector; its successful row may depend on that vector.
-- source:
--   Finite polynomial-system interface extracted from Senthil Kumar K (2026), Section 3 Lemma 2 and Section 5 Lemmas 7-10, equations (29), (34)-(35). This is an explicit interface adaptation, not a separately named definition in the source. https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Matrix.Basic

open scoped Polynomial

namespace TranscendenceTheory

/-- The finite linear equations and test linear forms in an auxiliary-function argument.
The last field records the analytic nonvanishing and small-value estimates; constructing
such a system is a separate mathematical obligation. -/
structure BoundedBivariateSystem (θ ν : ℂ) (a c : ℝ) (N : ℕ) where
  rows : ℕ
  cols : ℕ
  tests : ℕ
  xDegree : ℕ
  yDegree : ℕ
  cols_pos : 0 < cols
  dimension_gap : 8 * rows ≤ cols
  xDegree_le : (xDegree : ℝ) ≤ a * N
  yDegree_le : (yDegree : ℝ) ≤ a * N
  size_le : (cols : ℝ) * (yDegree + 1) * (xDegree + 1) ≤ Real.exp (a * N)
  equations : Matrix (Fin rows) (Fin cols) ℤ[X][X]
  testForms : Matrix (Fin tests) (Fin cols) ℤ[X][X]
  equations_yDegree : ∀ r i, (equations r i).natDegree ≤ yDegree
  equations_xDegree : ∀ r i j, ((equations r i).coeff j).natDegree ≤ xDegree
  equations_height : ∀ r i j k, ‖((equations r i).coeff j).coeff k‖ ≤ Real.exp (a * N)
  testForms_yDegree : ∀ r i, (testForms r i).natDegree ≤ yDegree
  testForms_xDegree : ∀ r i j, ((testForms r i).coeff j).natDegree ≤ xDegree
  testForms_height : ∀ r i j k, ‖((testForms r i).coeff j).coeff k‖ ≤ Real.exp (a * N)
  small_nonzero : ∀ p : Fin cols → ℤ[X][X], p ≠ 0 →
    (∀ i, (p i).natDegree ≤ yDegree) →
    (∀ i j, ((p i).coeff j).natDegree ≤ xDegree) →
    (∀ i j k, ‖((p i).coeff j).coeff k‖ ≤ Real.exp (2 * a * N)) →
    (∀ r, ∑ i, equations r i * p i = 0) →
    ∃ r : Fin tests,
      (∑ i, testForms r i * p i).eval₂ (Polynomial.aeval θ).toRingHom ν ≠ 0 ∧
      ‖(∑ i, testForms r i * p i).eval₂ (Polynomial.aeval θ).toRingHom ν‖ ≤
        Real.exp (-c * (N : ℝ) ^ 2 * Real.log N)

end TranscendenceTheory


