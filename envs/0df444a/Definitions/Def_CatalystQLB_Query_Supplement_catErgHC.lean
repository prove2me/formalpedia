-- Prove2me | Definitions.Def_CatalystQLB_Query_Supplement_catErgHC
-- name    : CatalystQLB_Query_Supplement_catErgHC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:02:41.044993+00:00
-- url     : https://prove2.me/theorems/c8ee4d41-fb8b-4b1e-8941-ddcd4ba3b9a0
-- title:
--   Catalytic ergotropy with a catalyst Hamiltonian, $\mathsf{cat}\text{-}\mathrm{erg}^\varepsilon_{\rho,H}[\eta,H_C]$
-- statement:
--   Let $\rho\in\mathrm{Den}(n)$, $H\in\mathrm{Herm}(n)$, $\eta\in\mathrm{Den}(\ell)$, $H_C\in\mathrm{Herm}(\ell)$ and $\varepsilon\ge0$. The **catalytic ergotropy with catalyst Hamiltonian $H_C$ and restoration error $\varepsilon$** is
--   $$\mathsf{cat}\text{-}\mathrm{erg}^\varepsilon_{\rho,H}[\eta,H_C] := \sup_{U\in\mathsf{cat}\text{-}\mathcal U_\eta(n,\ell,\varepsilon)}\mathrm{tr}\Big[H^{\mathrm{tot}}\big(\rho\otimes\eta-U(\rho\otimes\eta)U^\dagger\big)\Big],\qquad H^{\mathrm{tot}}=H\otimes I_C+I_{\mathrm{IO}}\otimes H_C .$$
--   With $H_C=0$ it is the catalytic ergotropy with a trivial catalyst Hamiltonian (not the ergotropy $\mathrm{erg}_{\rho,H}$).
--
--   **Formalization Note** The real supremum over the unitaries in $\mathsf{cat}\text{-}\mathcal U_\eta(n,\ell,\varepsilon)$; for $\varepsilon\ge0$ the identity belongs to the set and the values are bounded, so the supremum is the paper's.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Definition 141, Eq. (175), p.96 (PDF 99)

import Mathlib
import Definitions.Def_CatalystQLB_Query_Supplement_IsApproxCatalytic
import Definitions.Def_CatalystQLB_Query_Supplement_extractedWork

open scoped Matrix Kronecker

namespace CatalystQLB.Query.Supplement

open QAlgorithms

/-- **Catalytic ergotropy with a catalyst Hamiltonian** (Arora, Chakraborty, Cojocaru,
Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323
(version of 2026-11-03), Definition 141, Eq. (175), p.96 (PDF 99)): for `ρ ∈ Den(n)`,
`H ∈ Herm(n)`, `η ∈ Den(ℓ)`, `H_C ∈ Herm(ℓ)` and `ε ≥ 0`,
`cat-erg^ε_{ρ,H}[η, H_C] := sup_{U ∈ cat-U_η(n, ℓ, ε)} tr[H^tot (ρ ⊗ η − U (ρ ⊗ η) U†)]`,
`H^tot = H ⊗ I_C + I_IO ⊗ H_C`.

**Formalization Note** The real supremum over the unitaries with `IsApproxCatalytic U η ε`
(Definition 115). For `ε ≥ 0` the set contains `U = I` and the values are bounded, so `⨆` is the
paper's supremum; `cat-erg^ε[η, 0]` is the same with `H_C = 0` (not the ergotropy). -/
noncomputable def catErgHC {n ℓ : ℕ} (ρ H : Matrix (Qubits n) (Qubits n) ℂ)
    (η HC : Matrix (Qubits ℓ) (Qubits ℓ) ℂ) (ε : ℝ) : ℝ :=
  ⨆ U : {U : Matrix.unitaryGroup (Qubits n × Qubits ℓ) ℂ // IsApproxCatalytic U η ε},
    extractedWork ρ H η HC U.1

end CatalystQLB.Query.Supplement


