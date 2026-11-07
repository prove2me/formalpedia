-- Prove2me | Definitions.Def_LineVsPoint_agr
-- name    : LineVsPoint_agr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:03:03.125334+00:00
-- url     : https://prove2.me/theorems/4c3b104b-a40d-41dc-bed7-695f30144b62
-- title:
--   Agreement $\mathrm{agr}(f,Q)$ of a point table with a global polynomial
-- statement:
--   Let $\mathbb F$ be a finite field with $q$ elements, $f:\mathbb F^m\to\mathbb F$ and $Q\in\mathbb F[X_1,\dots,X_m]$ a formal polynomial. The **agreement** of $f$ with $Q$ is the fraction of points at which they coincide:
--
--   $$
--   \mathrm{agr}(f,Q):=\Pr_{x\in\mathbb F^m}\bigl[Q(x)=f(x)\bigr]=\frac{\#\{x\in\mathbb F^m : Q(x)=f(x)\}}{q^m}.
--   $$
--
--   Soundness of a low-degree test is a lower bound on $\max_Q \mathrm{agr}(f,Q)$ over polynomials $Q$ of total degree at most $d$.
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), Theorem 1.1, p.4

import Mathlib

set_option autoImplicit false

namespace LineVsPoint

open Classical in
/-- The **agreement** of a point table with a global polynomial: Dao, Kominers, Thaler, Zheng,
*Cube-Root Soundness Is Optimal for the Line–versus–Point Test* (manuscript, sha256 328a8943…),
Theorem 1.1, p.4: `agr(f, Q) := Pr_{x ∈ F^m_q}[Q(x) = f(x)]`, the fraction of the `q^m` points of
`F^m` at which the formal polynomial `Q ∈ F[X₁, …, X_m]` evaluates to `f(x)`. -/
noncomputable def agr {F : Type*} [Field F] [Fintype F] {m : ℕ} (f : (Fin m → F) → F)
    (Q : MvPolynomial (Fin m) F) : ℝ :=
  ((Finset.univ.filter fun x : Fin m → F => MvPolynomial.eval x Q = f x).card : ℝ) /
    ((Fintype.card F : ℝ) ^ m)

end LineVsPoint


