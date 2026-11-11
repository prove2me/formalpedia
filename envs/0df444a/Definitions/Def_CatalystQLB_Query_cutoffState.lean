-- Prove2me | Definitions.Def_CatalystQLB_Query_cutoffState
-- name    : CatalystQLB_Query_cutoffState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:21:25.450797+00:00
-- url     : https://prove2.me/theorems/ad102015-8e14-4271-ab33-23dc5b027d9b
-- title:
--   Spectral cutoff $\gamma$ of $\eta_{\ell,p}$
-- statement:
--   For $z\in\{0,1\}^\ell$ let $I_\ell(z)=-\log_2\mu_p(z)$ (Eq. (93)). For $\delta\in\mathbb R$,
--   $$\gamma=\sum_{z\in\{0,1\}^\ell:\ I_\ell(z)\ge\ell(h_2(p)-\delta)}\mu_p(z)\,|z\rangle\langle z|:$$
--   the part of $\eta_{\ell,p}$ whose eigenvalues are at most $2^{-\ell(h_2(p)-\delta)}$. It is used to replace the operator norm $\|\eta_{\ell,p}\|_\infty=(1-p)^\ell$ by the much smaller cutoff, at the price of the excluded weight.
--
--   **Formalization Note** $h_2$ is the published `WildeQIT.binaryEntropy` in bits; $\log_2$ is `Real.logb 2`.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Eqs. (93), (95), p.74 (PDF 77)

import Mathlib
import Definitions.Def_CatalystQLB_Query_catalystWeight
import Definitions.Def_WildeQIT_binaryEntropy

namespace CatalystQLB.Query

open QAlgorithms

/-- The spectral cutoff of `η_{ℓ,p}` (Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of 2026-11-03), Eqs. (93) and (95), p.74 (PDF 77)):
`γ := Σ_{z ∈ {0,1}^ℓ : I_ℓ(z) ≥ ℓ(h₂(p) − δ)} µ_p(z) |z⟩⟨z|`, with
`I_ℓ(z) := −log₂ µ_p(z)` (Eq. (93)). It keeps the eigenvalues of `η_{ℓ,p}` at or below the cutoff
`2^{−ℓ(h₂(p)−δ)}`.

**Formalization Note** `h₂` is `WildeQIT.binaryEntropy` (base-2 logarithm); `log₂` is
`Real.logb 2`. A diagonal matrix in the basis `Qubits ℓ`. -/
noncomputable def cutoffState (ℓ : ℕ) (p δ : ℝ) : Matrix (Qubits ℓ) (Qubits ℓ) ℂ :=
  Matrix.diagonal fun z =>
    if (ℓ : ℝ) * (WildeQIT.binaryEntropy p - δ) ≤ -Real.logb 2 (catalystWeight ℓ p z) then
      ((catalystWeight ℓ p z : ℝ) : ℂ) else 0

end CatalystQLB.Query


