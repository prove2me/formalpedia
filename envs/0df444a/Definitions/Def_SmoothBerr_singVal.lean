-- Prove2me | Definitions.Def_SmoothBerr_singVal
-- name    : SmoothBerr_singVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:12.176299+00:00
-- url     : https://prove2.me/theorems/3401e852-c48e-4939-ab6b-d2bd60c8ca4c
-- title:
--   Singular values $\sigma_1\ge\dots\ge\sigma_n$ in decreasing order
-- statement:
--   For a square matrix $M\in\mathbb R^{n\times n}$, the **singular values** are the square roots of the eigenvalues of the symmetric positive semidefinite matrix $M^\top M$. They are sorted in decreasing order,
--   $$
--   \sigma_{\max}(M)=\sigma_1(M)\ge\sigma_2(M)\ge\dots\ge\sigma_n(M)=\sigma_{\min}(M)\ge0,
--   \qquad \sigma_j(M)=\sqrt{\lambda_j(M^\top M)},
--   $$
--   where $\lambda_1(M^\top M)\ge\dots\ge\lambda_n(M^\top M)$ are the eigenvalues of $M^\top M$ in decreasing order (the published sorted-eigenvalue map `MaxEntSampling.eigDesc`). Lemma 5.8 sums $\sigma_j(\hat A)^{-2}$ over the $n-2$ largest singular values.
--
--   **Formalization Note** The index is 0-based: the paper's $\sigma_j$ with $1\le j\le n$ is `singVal M ⟨j-1, _⟩`. The sorted eigenvalues are those of the published `MaxEntSampling.eigDesc`, i.e. Mathlib's antitone `IsHermitian.eigenvalues₀`; since $M^\top M$ is symmetric, its junk branch for non-symmetric input is never used.
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), §3, p.4 ("The singular values of a matrix A ∈ ℝ^{n×d} are sorted in decreasing order")

import Mathlib
import Definitions.Def_MaxEntSampling_eigDesc

open Matrix

namespace SmoothBerr

/-- The singular values of a square real matrix in decreasing order (Dereziński, Mahoney, Meyer,
Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*,
manuscript of 3 Nov 2026, sha256 9575cd20…, §3, p.4: "The singular values of a matrix A ∈ ℝ^{n×d}
are sorted in decreasing order: σ_max(A) = σ_1(A) ≥ . . . ≥ σ_{min{n,d}}(A) = σ_min(A)").

`singVal M j = √λ_j(MᵀM)`, where `λ_0 ≥ λ_1 ≥ … ≥ λ_{n−1}` are the eigenvalues of the symmetric
positive semidefinite matrix `MᵀM`, sorted in decreasing order (the published
`MaxEntSampling.eigDesc`).

**Formalization Note** The index is 0-based: the paper's `σ_j` (`1 ≤ j ≤ n`) is
`singVal M ⟨j − 1, _⟩`. `MᵀM` is symmetric, so `eigDesc` returns its sorted eigenvalues (Mathlib's
`IsHermitian.eigenvalues₀`, which are antitone) and never its junk value. -/
noncomputable def singVal {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : ℝ :=
  Real.sqrt (MaxEntSampling.eigDesc (Mᵀ * M) j)

end SmoothBerr


