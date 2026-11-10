-- Prove2me | Definitions.Def_KnownFidelity_Rank_eigDesc
-- name    : KnownFidelity_Rank_eigDesc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:46:04.715341+00:00
-- url     : https://prove2.me/theorems/1672e978-4ff1-4bba-bdad-3bb94c5ff9f8
-- title:
--   Eigenvalues $\lambda_1\ge\lambda_2\ge\cdots$ of the reference, 1-indexed
-- statement:
--   For a Hermitian $\sigma$ on $\mathbb C^d$ and $1\le i\le d$, $\lambda_i$ is the $i$-th largest eigenvalue of $\sigma$, counted with multiplicity. For a state of rank $r$, the positive eigenvalues are exactly $\lambda_1\ge\cdots\ge\lambda_r>0$, and $t_k=\sum_{k<i\le r}\lambda_i$.
--
--   **Formalization Note** The value is Mathlib's sorted eigenvalue list `eigenvalues₀` at position $i-1$; outside $1\le i\le d$ it is $0$.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §1.2 (unnumbered), p. 2 (PDF p. 4)

import Mathlib

namespace KnownFidelity.Rank

/-- **The eigenvalues `λ₁ ≥ λ₂ ≥ ⋯` of the reference, 1-indexed.**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §1.2 (unnumbered), printed p. 2 (PDF p. 4): "Write its positive eigenvalues as
λ₁ ≥ · · · ≥ λ_r > 0 and let t_k = Σ_{i>k} λ_i."

For a Hermitian `σ` on `ℂ^d` and `1 ≤ i ≤ d`, `eigDesc σ i` is the `i`-th largest eigenvalue
(with multiplicity). For a state of rank `r` the positive eigenvalues are exactly
`eigDesc σ 1 ≥ ⋯ ≥ eigDesc σ r > 0`.

**Formalization Note.** The value is Mathlib's sorted (nonincreasing) eigenvalue list
`IsHermitian.eigenvalues₀` at position `i − 1`. Outside `1 ≤ i ≤ d`, or for a non-Hermitian
matrix, where the paper never uses it, the value is `0`. -/
noncomputable def eigDesc {d : ℕ} (σ : Matrix (Fin d) (Fin d) ℂ) (i : ℕ) : ℝ :=
  if h : σ.IsHermitian ∧ 1 ≤ i ∧ i ≤ d then
    h.1.eigenvalues₀ ⟨i - 1, by rw [Fintype.card_fin]; omega⟩
  else 0

end KnownFidelity.Rank


