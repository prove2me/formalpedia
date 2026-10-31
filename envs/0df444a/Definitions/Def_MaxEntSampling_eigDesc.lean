-- Prove2me | Definitions.Def_MaxEntSampling_eigDesc
-- name    : MaxEntSampling_eigDesc
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:44.928207+00:00
-- url     : https://prove2.me/theorems/ec933469-d8e5-4e50-a915-3c816641f567
-- title:
--   Eigenvalues sorted decreasingly, $\lambda_1\ge\cdots\ge\lambda_d$
-- statement:
--   For a real symmetric $d\times d$ matrix $X$, let $\lambda_1(X)\ge\lambda_2(X)\ge\cdots\ge\lambda_d(X)$ be its eigenvalues, listed with multiplicity in decreasing order. This is the eigenvalue vector used throughout the paper for $X\succeq 0$ (Definitions 1 and 2, Lemma 3).
--
--   **Formalization Note** The vector is Mathlib's `Matrix.IsHermitian.eigenvalues₀`, which is sorted decreasingly, reindexed by `Fin d`; the paper's $\lambda_i$ is the entry with 0-based index $i-1$. On a non-symmetric matrix the vector is $0$; the paper never applies it there.
-- source:
--   Li, Xie, Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem, arXiv:2001.08537v3, Definition 1, p.6 (PDF p.6)

import Mathlib

namespace MaxEntSampling

open Matrix

/-- **Eigenvalues sorted decreasingly, `λ₁ ≥ ⋯ ≥ λ_d`.**
Li, Xie, *Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem*,
arXiv:2001.08537v3, Definition 1, p.6 (PDF p.6): "For a d × d matrix X ⪰ 0 of its eigenvalues
λ1 ≥ ··· ≥ λd ≥ 0"; also Definition 2, p.8, and Lemma 3, p.8.

`eigDesc X i` is the `(i+1)`-st largest eigenvalue of the real symmetric matrix `X`, counted with
multiplicity: `eigDesc X ⟨0, _⟩ = λ₁` is the largest and `eigDesc X ⟨d-1, _⟩ = λ_d` the smallest.

**Formalization Note.** Mathlib's `Matrix.IsHermitian.eigenvalues₀` lists the eigenvalues of a
Hermitian matrix in decreasing order (`eigenvalues₀_antitone`), indexed by
`Fin (Fintype.card (Fin d))`; it is transported to `Fin d` here once. The paper's 1-based index
`i ∈ [d]` is the 0-based `Fin d` index `i - 1`. For a non-symmetric `X` (never used: the paper
applies the eigenvalue map only to `X ⪰ 0` or `Λ ≻ 0`) the value is the junk vector `0`. -/
noncomputable def eigDesc {d : ℕ} (X : Matrix (Fin d) (Fin d) ℝ) : Fin d → ℝ :=
  if hX : X.IsHermitian then fun i => hX.eigenvalues₀ (Fin.cast (Fintype.card_fin d).symm i)
  else 0

end MaxEntSampling


