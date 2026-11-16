-- Prove2me | Definitions.Def_CatalystQLB_Query_Supplement_extractedWork
-- name    : CatalystQLB_Query_Supplement_extractedWork
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:01:25.011969+00:00
-- url     : https://prove2.me/theorems/a7e0a89a-5fbe-438c-88de-8710ba31f08b
-- title:
--   Work extracted by one circuit, $\mathrm{tr}[H^{\mathrm{tot}}(\rho\otimes\eta-U(\rho\otimes\eta)U^\dagger)]$
-- statement:
--   For a system state $\rho$, Hamiltonians $H$ and $H_C$, a catalyst state $\eta$ and a unitary $U$ on system and catalyst, the **work extracted by $U$** is the decrease of the total energy:
--   $$\mathrm{tr}\Big[H^{\mathrm{tot}}\big(\rho\otimes\eta-U(\rho\otimes\eta)U^\dagger\big)\Big].$$
--   It is the objective of Definition 141 and the quantity averaged in Definition 142.
--
--   **Formalization Note** The real part of the complex trace (real for Hermitian $H,H_C$ and density $\rho,\eta$).
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Definition 141, Eq. (175), and Definition 142, Eq. (176), p.96 (PDF 99)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_CatalystQLB_Query_Supplement_Htot

open scoped Matrix Kronecker

namespace CatalystQLB.Query.Supplement

open QAlgorithms

/-- The **work extracted by one circuit** `U` from `ρ` with catalyst state `η` and catalyst
Hamiltonian `H_C`: `tr[H^tot (ρ ⊗ η − U (ρ ⊗ η) U†)]` (Arora, Chakraborty, Cojocaru, Saminathan,
Singh, *Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of
2026-11-03), the integrand of Definition 142, Eq. (176), and the objective of Definition 141,
Eq. (175), p.96 (PDF 99)).

**Formalization Note** The real part of the complex trace (the trace is real for Hermitian
`H, H_C` and density `ρ, η`). IO first, catalyst second. -/
noncomputable def extractedWork {n ℓ : ℕ} (ρ H : Matrix (Qubits n) (Qubits n) ℂ)
    (η HC : Matrix (Qubits ℓ) (Qubits ℓ) ℂ) (U : Matrix.unitaryGroup (Qubits n × Qubits ℓ) ℂ) :
    ℝ :=
  (Matrix.trace (Htot H HC *
    (ρ ⊗ₖ η - (U : Matrix _ _ ℂ) * (ρ ⊗ₖ η) * (U : Matrix _ _ ℂ)ᴴ))).re

end CatalystQLB.Query.Supplement


