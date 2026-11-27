-- Prove2me | Definitions.Def_ImpliedAmbiguity_Supplement_Q
-- name    : ImpliedAmbiguity_Supplement_Q
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:01:40.201283+00:00
-- url     : https://prove2.me/theorems/ba2f7ae8-2a79-4bf4-a935-b71dbb1917cb
-- title:
--   The matrix $Q = \Sigma_R^{-1}\Sigma_M$ whose eigenvectors are the basis portfolios
-- statement:
--   Let $\Sigma_R \in \mathcal S^N_{++}$ be the total covariance matrix of the returns of the $N$ risky assets and let $\Sigma_M$, with $0 \le \Sigma_M \le \Sigma_R$ in the Loewner order, be the investor's second-order belief (the covariance of the expected returns attributed to model uncertainty). Define the $N\times N$ matrix
--
--   $$
--   Q \equiv \Sigma_R^{-1}\Sigma_M .
--   $$
--
--   An eigenvector $v$ of $Q$ with eigenvalue $\lambda$ satisfies $\Sigma_M v = \lambda\,\Sigma_R v$: the covariances of the expected returns with portfolio $v$ are a scaled-down copy of the covariances of the returns with $v$. These eigenvectors are the basis portfolios of Theorem 1.
--
--   **Formalization Note** Assets are indexed by `Fin N`. $\Sigma_R^{-1}$ is Mathlib's matrix inverse, the true inverse whenever $\Sigma_R$ is positive definite. $Q$ is in general not symmetric.
-- source:
--   Hara & Honda, Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors, working paper (October 9, 2018; published version doi:10.1287/mnsc.2021.4097), §3, p.14 (definition of Q)

import Mathlib

open Matrix

namespace ImpliedAmbiguity.Supplement

/-- Hara & Honda, *Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors*, working
paper (October 9, 2018; published version Management Science 2022, doi:10.1287/mnsc.2021.4097),
§3, p.14: the matrix `Q ≡ Σ_R⁻¹ Σ_M`, where `Σ_R ∈ S^N_++` is the total covariance matrix of the
asset returns and `Σ_M` (with `0 ≤ Σ_M ≤ Σ_R`) is the second-order belief. Its eigenvectors are
the basis portfolios of Theorem 1.

**Formalization Note.** Assets are indexed by `Fin N`. `Σ_R⁻¹` is Mathlib's matrix inverse
`SigmaR⁻¹`, the true inverse whenever `SigmaR` is positive definite (as Theorem 1 assumes). `Q`
need not be symmetric. -/
noncomputable def Q {N : ℕ} (SigmaR SigmaM : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  SigmaR⁻¹ * SigmaM

end ImpliedAmbiguity.Supplement


