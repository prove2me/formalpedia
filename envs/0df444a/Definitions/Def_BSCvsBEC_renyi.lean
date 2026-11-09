-- Prove2me | Definitions.Def_BSCvsBEC_renyi
-- name    : BSCvsBEC_renyi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:29:48.83323+00:00
-- url     : https://prove2.me/theorems/ca3b3a82-ff45-481e-9175-f37096fc8af7
-- title:
--   Rényi entropy $H_\alpha$ of a quantum state, $0<\alpha\le\infty$
-- statement:
--   For a quantum register in a state $\sigma$ (a Hermitian matrix with eigenvalues $\lambda_1,\dots,\lambda_m$) and $0<\alpha\le\infty$, the **Rényi entropy** in bits is the Rényi entropy of the spectrum:
--   $$H_\alpha(\sigma)=\frac{1}{1-\alpha}\log_2\Big(\sum_i\lambda_i^\alpha\Big)\quad(\alpha\ne1,\infty),$$
--   $H_1(\sigma)=S(\sigma)=-\sum_i\lambda_i\log_2\lambda_i$ (von Neumann entropy), and the min-entropy $H_\infty(\sigma)=\log_2\min_i(1/\lambda_i)=-\log_2\max_i\lambda_i$.
--
--   These entropies appear in the paper's tensorization lemma (Lemma 2.3), which holds for every $0<\alpha\le\infty$.
--
--   **Formalization Note** $\alpha$ ranges over $[0,\infty]$ (`ℝ≥0∞`), $\alpha=\infty$ is `⊤`; the value at $\alpha=0$ is never used. Eigenvalues are counted with multiplicity and zero eigenvalues contribute $0^\alpha=0$. On a non-Hermitian matrix the value is $0$; every use is on a state.
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), §2.1, pp.5–6 (H_α, H_∞, H_α(X) := H_α(spec(σ_X)))

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy

namespace BSCvsBEC

/-- The Rényi entropy `H_α` (bits) of a quantum register in state `σ`, for `0 < α ≤ ∞`, computed on
the spectrum: for `α ≠ 1, ∞`, `H_α = (1/(1 − α)) log₂ ∑ᵢ λᵢ^α`; `H_1` is the von Neumann entropy;
`H_∞ = log₂ (minᵢ 1/λᵢ) = −log₂ maxᵢ λᵢ`.
Hązła–O'Donnell, manuscript of November 3, 2026 (sha256 a44ed926…), §2.1, pp.5–6: "its `α`-Rényi
entropy, `0 < α < ∞, α ≠ 1`, is given by `H_α(X) := 1/(1−α) log(∑ₓ P_X(x)^α)` … If instead `X` is a
quantum register in state `σ_X`, we have the definition `H_α(X) := H_α(spec(σ_X))`."

**Formalization Note.** `α : ℝ≥0∞`, with `α = ⊤` the min-entropy and `α = 1` the von Neumann entropy
(`ShadowTomography.QuantumLB.vnEntropy`). Eigenvalues `0` contribute `0^α = 0` (`α > 0`), so the sum
runs over the spectrum with multiplicity. The value is `0` on a non-Hermitian matrix, and the value at
`α = 0` is never used (every theorem assumes `α ≠ 0`). -/
noncomputable def renyi (α : ENNReal) {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Matrix ι ι ℂ) : ℝ :=
  if h : σ.IsHermitian then
    if α = ⊤ then -Real.logb 2 (⨆ i, h.eigenvalues i)
    else if α = 1 then ShadowTomography.QuantumLB.vnEntropy σ
    else (1 / (1 - α.toReal)) * Real.logb 2 (∑ i, h.eigenvalues i ^ α.toReal)
  else 0

end BSCvsBEC


