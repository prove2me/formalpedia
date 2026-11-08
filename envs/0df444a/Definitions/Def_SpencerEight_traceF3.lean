-- Prove2me | Definitions.Def_SpencerEight_traceF3
-- name    : SpencerEight_traceF3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:11:21.17197+00:00
-- url     : https://prove2.me/theorems/21470c5e-27b0-4dd1-8c3e-a6a376df3cb2
-- title:
--   Spectral trace $\operatorname{tr}[f_3(X)]$
-- statement:
--   For a symmetric matrix $X$ with eigenvalues $\lambda_i$, counted with multiplicity,
--   $$\operatorname{tr}[f_3(X)]:=\sum_i f_3(\lambda_i)\in[0,\infty].$$
--   It equals $+\infty$ as soon as $\|X\|\ge1$, so its finite sublevel sets exclude the spectral boundary.
--
--   **Formalization Note** A non-symmetric argument, which never occurs, gets the value $+\infty$.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 8.19, p.118 (PDF p.118); Lemma 8.65, p.128 (PDF p.128)

import Mathlib
import Definitions.Def_SpencerEight_f3
open scoped ENNReal

namespace SpencerEight

/-- The extended-valued spectral trace `tr[f₃(X)] = ∑ᵢ f₃(λᵢ(X))` (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 8.19, p.118 (PDF p.118); Lemma 8.65, p.128 (PDF p.128)).

**Formalization Note** The sum runs over the eigenvalues with multiplicity. It is `⊤` as soon as one eigenvalue has modulus at least one, so a sublevel set excludes the spectral boundary. A non-symmetric `X`, which never occurs, gets `⊤`. -/
noncomputable def traceF3 {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : ℝ≥0∞ :=
  if h : X.IsHermitian then ∑ i, f3 (h.eigenvalues i) else ⊤

end SpencerEight


