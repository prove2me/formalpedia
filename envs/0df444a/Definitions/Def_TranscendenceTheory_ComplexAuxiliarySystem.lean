-- Prove2me | Definitions.Def_TranscendenceTheory_ComplexAuxiliarySystem
-- name    : TranscendenceTheory_ComplexAuxiliarySystem
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-07T09:51:32.347509+00:00
-- url     : https://prove2.me/theorems/dc34f902-447d-4ffb-80bc-1b116dbc6a61
-- title:
--   Auxiliary equations and tests for bounded complex coefficients
-- statement:
--   Fix $\theta,\nu\in\mathbb C$, $a,b,c\in\mathbb R$ and $N\in\mathbb N$. A complex auxiliary system consists of polynomial matrices $B\in M_{m,n}(\mathbb Z[X,Y])$ and $Q\in M_{q,n}(\mathbb Z[X,Y])$, with degree bounds $D,E$, satisfying
--
--   $$
--   n>0,\quad 8m\le n,\quad D,E\le aN,\quad n(E+1)(D+1)\le e^{aN}.
--   $$
--
--   Every matrix entry has $X$-degree at most $D$, $Y$-degree at most $E$, and integer coefficient magnitude at most $e^{aN}$. For every complex vector $z\ne0$ such that
--
--   $$
--   |z_i|\le e^{bN},\qquad B(\theta,\nu)z=0,
--   $$
--
--   some test row satisfies
--
--   $$
--   0<|(Q(\theta,\nu)z)_r|\le e^{-cN^2\log N}.
--   $$
--
--   This record isolates the finite equations and the uniform analytic test property. The equation and test matrices are chosen before $z$. Their existence, including the small nonzero test property, is a separate theorem obligation. A reduced-degree condition may be imposed externally when relating complex coefficients to polynomial coefficients.
-- source:
--   Finite interface extracted from Senthil Kumar K (2026), Section 5 Lemmas 7-10 and equation (29), with the bounded complex coefficient estimate of Lemma 6. This is an explicit interface adaptation, not a separately named definition in the source. https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Matrix.Basic

open scoped Polynomial

namespace TranscendenceTheory

/-- Polynomial presentations of finite linear equations and tests, together with
the analytic estimate for bounded complex coefficient vectors. -/
structure ComplexAuxiliarySystem (θ ν : ℂ) (a b c : ℝ) (N : ℕ) where
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
  small_nonzero : ∀ z : Fin cols → ℂ, z ≠ 0 →
    (∀ i, ‖z i‖ ≤ Real.exp (b * N)) →
    (∀ r, ∑ i, (equations r i).eval₂ (Polynomial.aeval θ).toRingHom ν * z i = 0) →
    ∃ r : Fin tests,
      (∑ i, (testForms r i).eval₂ (Polynomial.aeval θ).toRingHom ν * z i) ≠ 0 ∧
      ‖∑ i, (testForms r i).eval₂ (Polynomial.aeval θ).toRingHom ν * z i‖ ≤
        Real.exp (-c * (N : ℝ) ^ 2 * Real.log N)

end TranscendenceTheory


