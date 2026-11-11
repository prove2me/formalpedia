-- Prove2me | Definitions.Def_SumReLU_IsTopEigenvector
-- name    : SumReLU_IsTopEigenvector
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:25:26.989929+00:00
-- url     : https://prove2.me/theorems/6de9e2d9-69bb-4a16-a8ea-3a8d2c140431
-- title:
--   The spectral norm $\|M\|_2$ and top eigenvectors $r_1(M)$
-- statement:
--   For a real $d\times d$ matrix $M$, $\|M\|_2$ is its spectral (operator) norm on $\mathbb R^d$ with the Euclidean norm. A top eigenvector of $M$ is a unit vector $r$ with $Mr=(r^\top Mr)\,r$ and $x^\top Mx\le r^\top Mr$ for every unit vector $x$; for symmetric $M$ these are exactly the unit eigenvectors of the largest eigenvalue $\lambda_1(M)$.
--
--   **Formalization Note** When $\lambda_1(M)$ is not simple, "the" top eigenvector $r_1(M)$ is any of them; statements about $r_1(M)$ are made for every top eigenvector.
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), §2, p.9 (PDF p.11)

import Mathlib

namespace SumReLU

/-- The spectral (`ℓ² → ℓ²` operator) norm `‖M‖₂` of a real `d × d` matrix (§2, p.9, PDF p.11):
the operator norm of `M` acting on `EuclideanSpace ℝ (Fin d)`. -/
noncomputable def specNorm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖

/-- `r` is **a top eigenvector** `r₁(M)` of `M`: a unit eigenvector of `M` whose Rayleigh quotient
is maximal over the unit sphere, i.e. a unit eigenvector of the largest eigenvalue `λ₁(M)`.

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), §2, p.9 (PDF p.11): "For a symmetric matrix M, λ_i(M) denotes its ith largest eigenvalue and
r_i(M) denotes the corresponding (unit) eigenvector".

**Formalization Note.** When `λ₁(M)` is not simple, "the" top eigenvector is any of them; a
statement about `r₁(M)` is stated for every `r` with `IsTopEigenvector M r`. -/
def IsTopEigenvector {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (r : EuclideanSpace ℝ (Fin d)) :
    Prop :=
  ‖r‖ = 1 ∧
    Matrix.toEuclideanCLM (𝕜 := ℝ) M r = (inner ℝ r (Matrix.toEuclideanCLM (𝕜 := ℝ) M r)) • r ∧
    ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ = 1 →
      inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) M x) ≤
        inner ℝ r (Matrix.toEuclideanCLM (𝕜 := ℝ) M r)

end SumReLU


