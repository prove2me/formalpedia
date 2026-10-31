-- Prove2me | Definitions.Def_MaxEntSampling_kIdx
-- name    : MaxEntSampling_kIdx
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:44.592452+00:00
-- url     : https://prove2.me/theorems/00e6e6ae-ee41-4259-a287-d66354d8fba0
-- title:
--   The unique index $k$ of Lemma 2
-- statement:
--   For $\lambda_1\ge\cdots\ge\lambda_d\ge0$ and $s\in[d]$, $k=k_s(\lambda)$ is the unique integer $0\le k<s$ with $\lambda_k>\frac1{s-k}\sum_{i\in[k+1,d]}\lambda_i\ge\lambda_{k+1}$ (Lemma 2, $\lambda_0=\infty$). The paper writes $k$ for it throughout.
--
--   **Formalization Note** Defined as the least $k$ satisfying the index condition; the fallback value $0$ is used only if no such $k$ exists, which Lemma 2 excludes for nonnegative sorted vectors and $1\le s\le d$.
-- source:
--   Li, Xie, Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem, arXiv:2001.08537v3, Lemma 2, p.8 (PDF p.8)

import Mathlib
import Definitions.Def_MaxEntSampling_IsKIndex

namespace MaxEntSampling

/-- **The unique integer `k` of Lemma 2.**
Li, Xie, *Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem*,
arXiv:2001.08537v3, Lemma 2, p.8 (PDF p.8): "Throughout this paper, we use k to denote the unique
integer in Lemma 2."

`kIdx s lam` is the least `k` with `IsKIndex s lam k` (the only one, by Lemma 2, when
`lam` is sorted decreasingly, nonnegative, and `1 ≤ s ≤ d`).

**Formalization Note.** Defined by `Nat.find` under a test of existence; the fallback value `0`
is used only when no such `k` exists, which Lemma 2 rules out for every vector of eigenvalues of
a positive semidefinite matrix with `1 ≤ s ≤ d`. -/
noncomputable def kIdx {d : ℕ} (s : ℕ) (lam : Fin d → ℝ) : ℕ := by
  classical
  exact if h : ∃ k, IsKIndex s lam k then Nat.find h else 0

end MaxEntSampling


