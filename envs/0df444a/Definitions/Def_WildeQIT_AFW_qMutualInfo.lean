-- Prove2me | Definitions.Def_WildeQIT_AFW_qMutualInfo
-- name    : WildeQIT_AFW_qMutualInfo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:33.131587+00:00
-- url     : https://prove2.me/theorems/1aa86775-dfc3-4f45-af79-a9c1ee0fa469
-- title:
--   Quantum mutual information $I(A;B)_\rho = H(A)_\rho + H(B)_\rho - H(AB)_\rho$
-- statement:
--   Let $\rho_{AB}$ be a bipartite state on $\mathcal H_A \otimes \mathcal H_B$, with marginals $\rho_A = \mathrm{Tr}_B\,\rho_{AB}$ and $\rho_B = \mathrm{Tr}_A\,\rho_{AB}$. Its **quantum mutual information** is
--
--   $$
--   I(A;B)_\rho \equiv H(A)_\rho + H(B)_\rho - H(AB)_\rho ,
--   $$
--
--   where $H(\omega) = -\mathrm{Tr}\{\omega\log_2\omega\}$ is the von Neumann entropy.
--
--   It measures the total correlation between $A$ and $B$; Theorem 11.10.4 bounds it above and below by the trace distance between $\rho_{AB}$ and $\rho_A\otimes\rho_B$.
--
--   **Formalization Note** The bipartite space is the index type `A × B`; $\rho_A$ is `WildeQIT.partialTraceRight ρ`, $\rho_B$ is `WildeQIT.partialTraceLeft ρ`, and $H$ is the published `QAlgorithms.vnEntropy` (base 2). The definition is total on matrices; the theorems assume density operators.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 11.6.1, (11.67), p. 334

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_WildeQIT_partialTrace

namespace WildeQIT.AFW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Definition 11.6.1, (11.67), p. 334:
"The quantum mutual information of a bipartite state ρ_AB ∈ D(H_A ⊗ H_B) is defined as follows:
I(A; B)_ρ ≡ H(A)_ρ + H(B)_ρ − H(AB)_ρ."

**Formalization Note.** The bipartite system is the index type `A × B` (Kronecker convention);
`ρ_A = Tr_B ρ` is `WildeQIT.partialTraceRight ρ`, `ρ_B = Tr_A ρ` is `WildeQIT.partialTraceLeft ρ`,
and `H` is the published von Neumann entropy `QAlgorithms.vnEntropy` (base-2 logarithm,
`H(ρ) = −Tr ρ log₂ ρ`). The definition is total on matrices; statements assume density
operators. -/
noncomputable def qMutualInfo {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Matrix (A × B) (A × B) ℂ) : ℝ :=
  QAlgorithms.vnEntropy (WildeQIT.partialTraceRight ρ) +
    QAlgorithms.vnEntropy (WildeQIT.partialTraceLeft ρ) - QAlgorithms.vnEntropy ρ

end WildeQIT.AFW


