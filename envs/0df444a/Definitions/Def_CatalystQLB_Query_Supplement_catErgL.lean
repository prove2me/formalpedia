-- Prove2me | Definitions.Def_CatalystQLB_Query_Supplement_catErgL
-- name    : CatalystQLB_Query_Supplement_catErgL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:59:25.940195+00:00
-- url     : https://prove2.me/theorems/d4dbd844-62d1-4265-b6a7-f762555e05a6
-- title:
--   Catalytic ergotropy with $\ell$ catalyst qubits, $\mathsf{cat}\text{-}\mathrm{erg}_{\rho,H}(\ell)$
-- statement:
--   For $\rho\in\mathrm{Den}(n)$, $H\in\mathrm{Herm}(n)$ and $\ell\in\mathbb N$, the **catalytic ergotropy with $\ell$ catalysts** is
--   $$\mathsf{cat}\text{-}\mathrm{erg}_{\rho,H}(\ell) := \max_{\substack{|\eta\rangle\in\mathcal H_{\mathrm{catalyst}}\\ U\in\mathsf{cat}\text{-}\mathcal U_{|\eta\rangle}(n,\ell)}}\mathrm{tr}\Big[(H\otimes I_{2^\ell})\big(\rho\otimes|\eta\rangle\langle\eta|-U(\rho\otimes|\eta\rangle\langle\eta|)U^\dagger\big)\Big],$$
--   the maximum over unit catalyst vectors $|\eta\rangle$ on $\ell$ qubits and exact catalytic unitaries for that catalyst. The catalyst carries no energy.
--
--   **Formalization Note** The real supremum over pairs $(|\eta\rangle,U)$ with $|\eta\rangle$ a unit vector; the set is nonempty (identity unitary) and bounded for density $\rho$ and Hermitian $H$, so the supremum is the paper's maximum. The printed $|\eta\rangle\langle\eta|^{\otimes\ell}$ is read as $|\eta\rangle\langle\eta|$: $|\eta\rangle$ already lives on the $\ell$ catalyst qubits, and the proof of Theorem 86 uses $\rho\otimes|\eta\rangle\langle\eta|$.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Definition 84, p.53 (PDF 56)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_CatalystQLB_Query_Supplement_IsUnitVec
import Definitions.Def_CatalystQLB_Query_Supplement_ketbra
import Definitions.Def_CatalystQLB_Query_Supplement_IsExactCatalytic

open scoped Matrix Kronecker

namespace CatalystQLB.Query.Supplement

open QAlgorithms

/-- **Catalytic ergotropy with `ℓ` catalysts** (Arora, Chakraborty, Cojocaru, Saminathan, Singh,
*Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of
2026-11-03), Definition 84, p.53 (PDF 56)):
`cat-erg_{ρ,H}(ℓ) := max_{|η⟩ ∈ H_catalyst, U ∈ cat-U_{|η⟩}(n, ℓ)}
  tr[(H ⊗ I_{2^ℓ}) (ρ ⊗ |η⟩⟨η| − U (ρ ⊗ |η⟩⟨η|) U†)]`.

**Formalization Note** The maximum ranges over pairs of a unit vector `|η⟩` on the `ℓ` catalyst
qubits and an exact catalytic unitary `U ∈ cat-U_{|η⟩}(n, ℓ)` (Definition 65); it is the real
supremum `⨆` over that set, which is nonempty (`U = I`, `|η⟩` a basis vector) and, for a density
`ρ` and Hermitian `H`, bounded by `2‖H‖`, so it is the paper's maximum. The printed
`|η⟩⟨η|^{⊗ℓ}` is read as `|η⟩⟨η|`: `|η⟩` already lives on the `ℓ` catalyst qubits, and the proof
of Theorem 86 uses `ρ ⊗ |η⟩⟨η|`. The catalyst carries no energy (`H ⊗ I`). The trace is the real
part of the complex trace (real for Hermitian `H` and density `ρ`). -/
noncomputable def catErgL (n ℓ : ℕ) (ρ H : Matrix (Qubits n) (Qubits n) ℂ) : ℝ :=
  ⨆ p : {p : (Qubits ℓ → ℂ) × Matrix.unitaryGroup (Qubits n × Qubits ℓ) ℂ //
      IsUnitVec p.1 ∧ IsExactCatalytic p.2 p.1},
    (Matrix.trace ((H ⊗ₖ (1 : Matrix (Qubits ℓ) (Qubits ℓ) ℂ)) *
      (ρ ⊗ₖ ketbra p.1.1 -
        (p.1.2 : Matrix _ _ ℂ) * (ρ ⊗ₖ ketbra p.1.1) * (p.1.2 : Matrix _ _ ℂ)ᴴ))).re

end CatalystQLB.Query.Supplement


