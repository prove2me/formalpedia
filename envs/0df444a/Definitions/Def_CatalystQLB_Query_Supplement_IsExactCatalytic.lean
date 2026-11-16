-- Prove2me | Definitions.Def_CatalystQLB_Query_Supplement_IsExactCatalytic
-- name    : CatalystQLB_Query_Supplement_IsExactCatalytic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:57:54.96319+00:00
-- url     : https://prove2.me/theorems/e629125c-4c06-4d94-a396-4ed073992e1a
-- title:
--   Exact catalytic unitaries $\mathsf{cat}\text{-}\mathcal U_{|\eta\rangle}(n,\ell)$ for a pure catalyst
-- statement:
--   Let $|\eta\rangle\in\mathcal H_{\mathrm{catalyst}}$. A unitary $U\in\mathcal U(n+\ell)$ is a **catalytic unitary given the catalyst $|\eta\rangle$**, $U\in\mathsf{cat}\text{-}\mathcal U_{|\eta\rangle}(n,\ell)$, if for every $|\phi\rangle\in\mathcal H_{\mathrm{IO}}$ there is $|\psi\rangle\in\mathcal H_{\mathrm{IO}}$ with
--   $$U\big(|\phi\rangle\otimes|\eta\rangle\big)=|\psi\rangle\otimes|\eta\rangle .$$
--   The catalyst is restored exactly, whatever the input. This is the set over which the catalytic ergotropy of Definition 84 is maximized.
--
--   **Formalization Note** An identity of vectors on the joint basis (IO first); $(|\phi\rangle\otimes|\eta\rangle)_{(i,j)}=\phi_i\eta_j$.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Definition 65, p.40 (PDF 43)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

open scoped Matrix

namespace CatalystQLB.Query.Supplement

open QAlgorithms

/-- **Catalytic unitaries given a catalyst `|η⟩`**, `U ∈ cat-U_{|η⟩}(n, ℓ)` (Arora,
Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of
Catalysts*, arXiv:2609.40323 (version of 2026-11-03), Definition 65, p.40 (PDF 43)):
`U ∈ U(n + ℓ)` such that for every `|ϕ⟩ ∈ H_IO` there is `|ψ⟩ ∈ H_IO` with
`U (|ϕ⟩ ⊗ |η⟩) = |ψ⟩ ⊗ |η⟩` (an identity of vectors: the catalyst is restored exactly).

**Formalization Note** Vectors are functions on the basis `Qubits n × Qubits ℓ` (IO first);
`(|ϕ⟩ ⊗ |η⟩)(i, j) = ϕᵢ ηⱼ`, and `U` acts by `Matrix.mulVec`. As in the definition, `ϕ` ranges
over all of `H_IO`; since the identity is linear in `ϕ` (with `ψ` scaled alike), this is the same
set as quantifying over unit vectors only. -/
def IsExactCatalytic {n ℓ : ℕ} (U : Matrix.unitaryGroup (Qubits n × Qubits ℓ) ℂ)
    (η : Qubits ℓ → ℂ) : Prop :=
  ∀ ϕ : Qubits n → ℂ, ∃ ψ : Qubits n → ℂ,
    (U : Matrix (Qubits n × Qubits ℓ) (Qubits n × Qubits ℓ) ℂ).mulVec
        (fun p : Qubits n × Qubits ℓ => ϕ p.1 * η p.2) =
      fun p : Qubits n × Qubits ℓ => ψ p.1 * η p.2

end CatalystQLB.Query.Supplement


