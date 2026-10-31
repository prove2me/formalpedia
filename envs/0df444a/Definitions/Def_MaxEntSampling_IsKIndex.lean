-- Prove2me | Definitions.Def_MaxEntSampling_IsKIndex
-- name    : MaxEntSampling_IsKIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:46.77974+00:00
-- url     : https://prove2.me/theorems/f56c84d2-1ead-4057-89a4-1ac07894eba2
-- title:
--   The index condition of Lemma 2: $\lambda_k>\frac1{s-k}\sum_{i>k}\lambda_i\ge\lambda_{k+1}$
-- statement:
--   For a vector $\lambda\in\mathbb R^d$ with $\lambda_1\ge\cdots\ge\lambda_d$ and an integer $s\in[d]$, an integer $k$ **satisfies the index condition** when $0\le k<s$ and
--
--   $$
--   \lambda_k \;>\; \frac{1}{s-k}\sum_{i\in[k+1,d]}\lambda_i \;\ge\; \lambda_{k+1},
--   $$
--
--   with the convention $\lambda_0=\infty$ (so for $k=0$ only the right inequality is required). Lemma 2 says that exactly one such $k$ exists when $\lambda\ge 0$; it determines $\Gamma_s$ (Definition 2).
--
--   **Formalization Note** Indices are 0-based: $\lambda_k$ is the entry with index $k-1$, $\lambda_{k+1}$ the entry with index $k$, and $[k+1,d]$ is $k\le i$. The condition on $\lambda_k$ is quantified over the entries with index $k-1$, hence vacuous for $k=0$.
-- source:
--   Li, Xie, Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem, arXiv:2001.08537v3, Lemma 2, p.8 (PDF p.8)

import Mathlib

open Finset

namespace MaxEntSampling

/-- **The index condition of Lemma 2.**
Li, Xie, *Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem*,
arXiv:2001.08537v3, Lemma 2 (lemma 14 of Nikolov 2015), p.8 (PDF p.8): for λ1 ≥ ··· ≥ λd and
s ∈ [d], the integer `0 ≤ k < s` with
"λk > (1/(s−k)) Σ_{i∈[k+1,d]} λi ≥ λk+1, where by convention λ0 = ∞."

`IsKIndex s lam k` says: `k < s`; the tail average `(1/(s−k)) Σ_{i∈[k+1,d]} λ_i` is strictly
below `λ_k` (no condition when `k = 0`, which is the convention `λ₀ = ∞`); and it is at least
`λ_{k+1}`.

**Formalization Note.** `lam : Fin d → ℝ` is `(λ₁,…,λ_d)` with 0-based indices: `λ_k` is the
entry `j` with `j.val + 1 = k`, `λ_{k+1}` the entry with `j.val = k`, and `[k+1, d]` is
`k ≤ i.val`. The conditions on `λ_k` and `λ_{k+1}` are quantified over the entries with that
index, so the `k = 0` clause is vacuous exactly as with `λ₀ = ∞`. Since `k < s ≤ d`, the entry
`λ_{k+1}` always exists when `s ≤ d`. The division is by `s − k > 0`. -/
def IsKIndex {d : ℕ} (s : ℕ) (lam : Fin d → ℝ) (k : ℕ) : Prop :=
  k < s ∧
    (∀ j : Fin d, j.val + 1 = k →
      (∑ i ∈ univ.filter (fun i : Fin d => k ≤ i.val), lam i) / ((s : ℝ) - k) < lam j) ∧
    (∀ j : Fin d, j.val = k →
      lam j ≤ (∑ i ∈ univ.filter (fun i : Fin d => k ≤ i.val), lam i) / ((s : ℝ) - k))

end MaxEntSampling


