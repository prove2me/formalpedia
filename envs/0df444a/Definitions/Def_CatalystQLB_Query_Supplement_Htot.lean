-- Prove2me | Definitions.Def_CatalystQLB_Query_Supplement_Htot
-- name    : CatalystQLB_Query_Supplement_Htot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:00:52.024501+00:00
-- url     : https://prove2.me/theorems/7eb8f795-1677-407b-89ae-1f4d811484ef
-- title:
--   Total Hamiltonian $H^{\mathrm{tot}}=H\otimes I_C+I_{\mathrm{IO}}\otimes H_C$
-- statement:
--   For a system Hamiltonian $H\in\mathrm{Herm}(n)$ and a catalyst Hamiltonian $H_C\in\mathrm{Herm}(\ell)$, the **total Hamiltonian** on system and catalyst is
--   $$H^{\mathrm{tot}} := H\otimes I_C + I_{\mathrm{IO}}\otimes H_C .$$
--   With $H_C=0$ the catalyst carries no energy, as in every earlier definition of catalytic work extraction.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Appendix C.3, p.96 (PDF 99)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

open scoped Matrix Kronecker

namespace CatalystQLB.Query.Supplement

open QAlgorithms

/-- The **total Hamiltonian** `H^tot := H ⊗ I_C + I_IO ⊗ H_C` of system and catalyst (Arora,
Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of
Catalysts*, arXiv:2609.40323 (version of 2026-11-03), Appendix C.3, p.96 (PDF 99)).

**Formalization Note** IO first, catalyst second (`Qubits n × Qubits ℓ`); `⊗` is `⊗ₖ`. -/
noncomputable def Htot {n ℓ : ℕ} (H : Matrix (Qubits n) (Qubits n) ℂ)
    (HC : Matrix (Qubits ℓ) (Qubits ℓ) ℂ) :
    Matrix (Qubits n × Qubits ℓ) (Qubits n × Qubits ℓ) ℂ :=
  H ⊗ₖ (1 : Matrix (Qubits ℓ) (Qubits ℓ) ℂ) + (1 : Matrix (Qubits n) (Qubits n) ℂ) ⊗ₖ HC

end CatalystQLB.Query.Supplement


