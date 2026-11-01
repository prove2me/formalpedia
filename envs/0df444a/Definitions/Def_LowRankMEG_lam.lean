-- Prove2me | Definitions.Def_LowRankMEG_lam
-- name    : LowRankMEG_lam
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:27.996448+00:00
-- url     : https://prove2.me/theorems/874f55a2-52e2-483e-bcdb-964201ed7e73
-- title:
--   The $i$-th largest eigenvalue $\lambda_i(X)$, 1-based
-- statement:
--   For a real symmetric $n\times n$ matrix $X$, $\lambda_i(X)$ denotes its $i$-th largest eigenvalue, counted with multiplicity, so that
--   $$
--   \lambda_1(X)\ge\lambda_2(X)\ge\cdots\ge\lambda_n(X).
--   $$
--   These are the sorted eigenvalues on which every spectral inequality of the mission is stated.
--
--   **Formalization Note** The value is the published `MaxEntSampling.eigDesc X` at the 0-based position $i-1$, for $1\le i\le n$, and $0$ outside that range. Every statement of the mission uses an index in range.
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, §2.1, p.5

import Mathlib
import Definitions.Def_MaxEntSampling_eigDesc

namespace LowRankMEG

/-- **The `i`-th largest eigenvalue `λ_i(X)`** of a real symmetric matrix, with the paper's 1-based index.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, §2.1, p.5.

**Formalization Note.** `lam X i` is `MaxEntSampling.eigDesc X` at the 0-based position `i - 1`, for
`1 ≤ i ≤ n`, so `lam X 1` is the largest and `lam X n` the smallest eigenvalue, counted with
multiplicity. Outside that range the value is `0`; every statement of this mission uses an index in
range, which each statement's hypotheses guarantee (`1 ≤ r*`, `r* ≤ r < n`). -/
noncomputable def lam {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (i : ℕ) : ℝ :=
  if h : 1 ≤ i ∧ i ≤ n then MaxEntSampling.eigDesc X ⟨i - 1, by omega⟩ else 0

end LowRankMEG


