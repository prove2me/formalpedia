-- Prove2me | Definitions.Def_CatalystQLB_Query_Supplement_expectedWork
-- name    : CatalystQLB_Query_Supplement_expectedWork
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:02:03.080939+00:00
-- url     : https://prove2.me/theorems/706384bf-b535-4af6-be91-c02136783c9e
-- title:
--   Average extracted work $\mathbb E_{\mathcal D}\mathcal W^{(\ell)}_{\rho,H,\mathcal A}[\eta,H_C](\lambda)$
-- statement:
--   Fix $\lambda$, the catalyst state $\eta=\eta_\lambda$ and the catalyst Hamiltonian $H_C=H_{C,\lambda}$. An instance $(\rho,H,O)$ is drawn from a distribution $\mathcal D$, and an extractor $\mathcal A$ outputs (using internal randomness) a circuit $U$ on system and catalyst. The **average extracted work** is
--   $$\mathbb E_{\mathcal D}\,\mathcal W^{(\ell)}_{\rho,H,\mathcal A}[\eta,H_C](\lambda) = \mathbb E_{(\rho,H,O)\leftarrow\mathcal D}\ \mathbb E_{U\leftarrow\mathcal A}\ \mathrm{tr}\Big[H^{\mathrm{tot}}\big(\rho\otimes\eta-U(\rho\otimes\eta)U^\dagger\big)\Big].$$
--
--   **Formalization Note** One measure space $(\Omega,\mu)$ carries the joint law of the instance and of the extractor's randomness, with $\rho(\omega)$, $H(\omega)$ and $U(\omega)$ the sampled state, Hamiltonian and generated circuit; the iterated expectation is the integral over $\mu$. Theorems that use it assume $\mu$ is a probability measure and the integrand integrable.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Definition 142, Eq. (176), p.96 (PDF 99); Theorem 144(2), Eq. (178), p.97 (PDF 100)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_CatalystQLB_Query_Supplement_extractedWork

open MeasureTheory

namespace CatalystQLB.Query.Supplement

open QAlgorithms

/-- The **average extracted work** `E_D W^{(ℓ)}_{ρ,H,A}[η, H_C](λ)` at one value of `λ`
(Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity
of Catalysts*, arXiv:2609.40323 (version of 2026-11-03), Definition 142, Eq. (176), p.96
(PDF 99), averaged over `(ρ, H, O) ← D` as in Theorem 144(2), Eq. (178), p.97 (PDF 100)).

**Formalization Note** One measure space `(Ω, μ)` carries the joint law of the instance
`(ρ, H, O) ← D` and of the extractor's internal randomness; `ρ ω`, `H ω` are the sampled
`n`-qubit state and Hamiltonian and `U ω` the generated circuit. The iterated expectation
`E_D E_A` is the integral over `μ` (Bochner; theorems using it assume `μ` is a probability
measure and the integrand integrable). The catalyst state `η = η_λ` and Hamiltonian
`H_C = H_{C,λ}` are fixed, as in the paper. -/
noncomputable def expectedWork {n ℓ : ℕ} {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (ρ H : Ω → Matrix (Qubits n) (Qubits n) ℂ)
    (U : Ω → Matrix.unitaryGroup (Qubits n × Qubits ℓ) ℂ)
    (η HC : Matrix (Qubits ℓ) (Qubits ℓ) ℂ) : ℝ :=
  ∫ ω, extractedWork (ρ ω) (H ω) η HC (U ω) ∂μ

end CatalystQLB.Query.Supplement


