-- Prove2me | Definitions.Def_SmoothedNash_Supplement_rowSigma
-- name    : SmoothedNash_Supplement_rowSigma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:02:42.471458+00:00
-- url     : https://prove2.me/theorems/034821cc-00c1-4642-8cec-0ecc69d6c58b
-- title:
--   Smallest row singular value $\sigma_n(J_K(x,t))$
-- statement:
--   For an $n \times (n+1)$ matrix $A$, the smallest row singular value is
--   $$
--   \sigma_n(A) = \min_{u \in \mathbb R^n,\ \|u\| = 1} \|A^\top u\| ,
--   $$
--   the smallest of its $n$ singular values. For $A = J_K(x,t)$,
--   $A^\top u = \bigl((1-t)u - \tfrac{t}{a} J_F(x)^\top u,\; -\langle x + F(x)/a, u\rangle\bigr)$.
--   This is the regularity quantity of Property 4.1 and Theorem 4.5.
--
--   **Formalization Note** An infimum over the unit sphere of $\mathbb R^n$, with the Euclidean norm of $\mathbb R^{n+1} = \mathbb R^n \times \mathbb R$ written out. For $n = 0$ the sphere is empty and the value is $0$; theorems using it assume $n \ge 1$.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), §4.1.2 and Property 4.1, p.26

import Mathlib
open MeasureTheory

namespace SmoothedNash.Supplement

/-- The smallest row singular value `σ_n(J_K(x, t))` of the `n × (n+1)` homotopy Jacobian
(Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), §4.1.2 and Property 4.1, p.26): `σ_n(A) = min_{‖u‖ = 1} ‖A^⊤ u‖` for `u ∈ ℝ^n`. With
`A = J_K(x,t)`, `A^⊤ u = ((1 − t) u − (t/a) J_F(x)^⊤ u, −⟨x + F(x)/a, u⟩) ∈ ℝ^n × ℝ`.

**Formalization Note** The Euclidean norm on `ℝ^{n+1} = ℝ^n × ℝ` is written out as
`√(‖·‖² + (·)²)`. The minimum is an infimum over the unit sphere of `ℝ^n` (attained, since the
sphere is compact); it is the smallest of the `n` singular values. At `n = 0` the sphere is empty and
the value is the junk `0`; the theorems using it assume `n ≥ 1`. -/
noncomputable def rowSigma {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (a : ℝ) (p : EuclideanSpace ℝ (Fin n) × ℝ) : ℝ :=
  ⨅ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
    Real.sqrt (‖(1 - p.2) • (u : EuclideanSpace ℝ (Fin n)) - (p.2 / a) •
        ContinuousLinearMap.adjoint (fderivWithin ℝ F (Metric.closedBall 0 1) p.1) u‖ ^ 2
      + (inner ℝ (u : EuclideanSpace ℝ (Fin n)) (p.1 + a⁻¹ • F p.1)) ^ 2)

end SmoothedNash.Supplement


