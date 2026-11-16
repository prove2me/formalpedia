-- Prove2me | Definitions.Def_CatalystQLB_Query_Supplement_IsApproxCatalytic
-- name    : CatalystQLB_Query_Supplement_IsApproxCatalytic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:58:33.617685+00:00
-- url     : https://prove2.me/theorems/03d94b8b-7cc7-4175-b6da-f12af10cad3d
-- title:
--   Approximately catalytic unitaries $\mathsf{cat}\text{-}\mathcal U_\eta(n,\ell,\varepsilon)$
-- statement:
--   Let $\eta$ be a catalyst state on $\ell$ qubits and $\varepsilon\ge0$. A unitary $U\in\mathcal U(n+\ell)$ belongs to $\mathsf{cat}\text{-}\mathcal U_\eta(n,\ell,\varepsilon)$ if for every pure state $|\phi\rangle\in\mathcal H_{\mathrm{IO}}$ there is a pure state $|\psi\rangle\in\mathcal H_{\mathrm{IO}}$ (which may depend on $\phi$) with
--   $$\mathrm{TD}\big(U(\phi\otimes\eta)U^\dagger,\ \psi\otimes\eta\big)\le\varepsilon .$$
--   The catalyst is restored up to error $\varepsilon$ and may stay slightly correlated with the input/output register.
--
--   This is Eq. (71) of Definition 115 (mixed $\eta$). Definition 62's $\mathsf{cat}\text{-}\mathcal U(n,\ell,\varepsilon)$ consists of the $U$ that satisfy this condition for **some** pure catalyst $\eta=|\eta\rangle\langle\eta|$; Theorem 64 names that catalyst.
--
--   **Formalization Note** $\phi,\psi$ are unit vectors and $\phi$ stands for $|\phi\rangle\langle\phi|$; $\mathrm{TD}$ is the halved trace distance. The predicate is stated for any matrix $\eta$; the theorems assume $\eta$ is a density operator.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Definition 62, p.37 (PDF 40); Definition 115, Eq. (71), p.69 (PDF 72)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_CatalystQLB_Query_Supplement_IsUnitVec
import Definitions.Def_CatalystQLB_Query_Supplement_ketbra
import Definitions.Def_CatalystQLB_Query_Supplement_TD

open scoped Matrix Kronecker

namespace CatalystQLB.Query.Supplement

open QAlgorithms

/-- **Approximately catalytic unitaries for a catalyst state `η`**, `U ∈ cat-U_η(n, ℓ, ε)`
(Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity
of Catalysts*, arXiv:2609.40323 (version of 2026-11-03), Definition 115, Eq. (71), p.69 (PDF 72);
Definition 62, p.37 (PDF 40)): `U ∈ U(n + ℓ)` such that for every pure state `|ϕ⟩ ∈ H_IO` there
is a pure state `|ψ⟩ ∈ H_IO` with
`TD(U (ϕ ⊗ η) U†, ψ ⊗ η) ≤ ε`.

Definition 62's `cat-U(n, ℓ, ε)` is the set of `U` for which this holds for **some** pure catalyst
`η = |η⟩⟨η|`; Theorem 64's "with the catalyst state `η = |η⟩⟨η|`" names that witness, so
Theorem 64 assumes `IsApproxCatalytic U (ketbra η) ε` for a unit vector `η`.

**Formalization Note** `ϕ`, `ψ` are unit vectors (`IsUnitVec`) and `ϕ = |ϕ⟩⟨ϕ|` is `ketbra ϕ`;
`ψ` may depend on `ϕ`. The register order is `IO × catalyst` (`Qubits n × Qubits ℓ`); `TD` is the
paper's halved trace distance. The predicate is stated for any matrix `η`; the theorems assume
`η ∈ Den(ℓ)`. For `ε < 0` no unitary satisfies it. -/
def IsApproxCatalytic {n ℓ : ℕ} (U : Matrix.unitaryGroup (Qubits n × Qubits ℓ) ℂ)
    (η : Matrix (Qubits ℓ) (Qubits ℓ) ℂ) (ε : ℝ) : Prop :=
  ∀ ϕ : Qubits n → ℂ, IsUnitVec ϕ → ∃ ψ : Qubits n → ℂ, IsUnitVec ψ ∧
    TD ((U : Matrix _ _ ℂ) * (ketbra ϕ ⊗ₖ η) * (U : Matrix _ _ ℂ)ᴴ) (ketbra ψ ⊗ₖ η) ≤ ε

end CatalystQLB.Query.Supplement


