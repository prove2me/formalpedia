-- Prove2me | Definitions.Def_CubeSampling_empCov
-- name    : CubeSampling_empCov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:16:01.629135+00:00
-- url     : https://prove2.me/theorems/6edc6a30-8344-4305-876b-04173633c1c7
-- title:
--   Empirical covariance $\hat\Sigma_V = \frac1n\sum_i \Phi_V(X_i)\Phi_V(X_i)^\top$
-- statement:
--   For inputs $X_1,\dots,X_n$ and an orthonormal family $\Phi_V$, the **empirical covariance** is the symmetric $m\times m$ matrix
--   $$
--   \hat\Sigma_V = \frac1n \sum_{i=1}^n \Phi_V(X_i)\Phi_V(X_i)^\top .
--   $$
--   $\hat\Sigma_V \succeq cI_m$ means $a^\top(\hat\Sigma_V - cI_m)a \ge 0$ for all $a \in \mathbb R^m$. Its population counterpart is $I_m$.
--
--   **Formalization Note** The module also proves that $\hat\Sigma_V$ is symmetric, so its eigenvalues (with multiplicity) are defined.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 1.1, p.3

import Mathlib
import Definitions.Def_CubeSampling_Cube

namespace CubeSampling

/-- The empirical covariance `Σ̂_V = (1/n) ∑_i Φ_V(X_i) Φ_V(X_i)^⊤` of inputs `X_1, …, X_n`
(Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §1.1, p.3). `Σ̂_V ⪰ c I_m` is written `(empCov Φ n X - c • 1).PosSemidef`. -/
noncomputable def empCov {d m : ℕ} (Φ : Fin m → Cube d → ℝ) (n : ℕ) (X : Fin n → Cube d) :
    Matrix (Fin m) (Fin m) ℝ :=
  (n : ℝ)⁻¹ • ∑ i, Matrix.vecMulVec (fun j => Φ j (X i)) (fun j => Φ j (X i))

/-- `Σ̂_V` is symmetric, so its eigenvalues (with multiplicity) are defined. -/
theorem empCov_isHermitian {d m : ℕ} (Φ : Fin m → Cube d → ℝ) (n : ℕ) (X : Fin n → Cube d) :
    (empCov Φ n X).IsHermitian := by
  ext i j
  simp [empCov, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, mul_comm]

end CubeSampling


