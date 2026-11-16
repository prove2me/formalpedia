-- Prove2me | Definitions.Def_CatalystQLB_Query_Supplement_catChannel
-- name    : CatalystQLB_Query_Supplement_catChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:57:05.270673+00:00
-- url     : https://prove2.me/theorems/ced57e15-cfbe-4a2f-b1cb-3cf9f549c1d4
-- title:
--   The catalytic channel $C^\sigma_U(\rho)=\mathrm{tr}_{\mathrm{catalyst}}[U(\rho\otimes\sigma)U^\dagger]$
-- statement:
--   Let $\mathcal H_{\mathrm{IO}}=(\mathbb C^2)^{\otimes n}$ and $\mathcal H_{\mathrm{catalyst}}=(\mathbb C^2)^{\otimes \ell}$. For a unitary $U$ on $\mathcal H_{\mathrm{IO}}\otimes\mathcal H_{\mathrm{catalyst}}$ and a catalyst state $\sigma$, the **channel associated with $(U,\sigma)$** acts on an $n$-qubit operator $\rho$ by
--   $$C^\sigma_U(\rho) := \mathrm{tr}_{\mathrm{catalyst}}\big[U(\rho\otimes\sigma)U^\dagger\big].$$
--   It is the reduced state of the input/output register after the catalytic computation.
--
--   **Formalization Note** The joint basis is indexed by pairs (IO string, catalyst string), IO first; $\otimes$ is the Kronecker product in that order and the partial trace over the catalyst is the published `WildeQIT.partialTraceRight`.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Notation 59, p.36 (PDF 39)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_WildeQIT_partialTrace

open scoped Matrix Kronecker

namespace CatalystQLB.Query.Supplement

open QAlgorithms

/-- The channel of a unitary `U` on `IO ⊗ catalyst` with catalyst state `σ`,
`C^σ_U(ρ) := tr_catalyst[U (ρ ⊗ σ) U†]` (Arora, Chakraborty, Cojocaru, Saminathan, Singh,
*Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of
2026-11-03), Notation 59, p.36 (PDF 39)). Here `H_IO = (ℂ²)^{⊗n}` and `H_catalyst = (ℂ²)^{⊗ℓ}`
(§5.1, p.36 (PDF 39)).

**Formalization Note** The joint basis is indexed by `Qubits n × Qubits ℓ`, IO first and catalyst
second; `ρ ⊗ σ` is the Kronecker product `ρ ⊗ₖ σ` in that order, and `tr_catalyst` is the
published `WildeQIT.partialTraceRight`, which traces out the second factor. -/
noncomputable def catChannel {n ℓ : ℕ} (U : Matrix.unitaryGroup (Qubits n × Qubits ℓ) ℂ)
    (σ : Matrix (Qubits ℓ) (Qubits ℓ) ℂ) (ρ : Matrix (Qubits n) (Qubits n) ℂ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  WildeQIT.partialTraceRight ((U : Matrix _ _ ℂ) * (ρ ⊗ₖ σ) * (U : Matrix _ _ ℂ)ᴴ)

end CatalystQLB.Query.Supplement


