-- Prove2me | Definitions.Def_DattaDiscord_mutualInfo
-- name    : DattaDiscord_mutualInfo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:20:55.098194+00:00
-- url     : https://prove2.me/theorems/8e0c8142-7043-4249-b394-776512f042a4
-- title:
--   Quantum mutual information $I(A:B)=H(A)+H(B)-H(A,B)$
-- statement:
--   For a bipartite operator $\rho_{AB}$ with marginals $\rho_A=\mathrm{Tr}_B\rho_{AB}$ and $\rho_B=\mathrm{Tr}_A\rho_{AB}$, the **quantum mutual information** is
--
--   $$
--   I(A:B)=H(\rho_A)+H(\rho_B)-H(\rho_{AB}),
--   $$
--
--   with $H$ the von Neumann entropy in bits. It measures the total (classical and quantum) correlations of the state.
--
--   **Formalization Note** $\rho_A$ is `QAlgorithms.traceRight ρ` and $\rho_B$ is `QAlgorithms.traceLeft ρ`; $H$ is `QAlgorithms.vnEntropy`.
-- source:
--   Datta, A Condition for the Nullity of Quantum Discord, arXiv:1003.5256v2, p.1 ("I(A : B) = H(A) + H(B) − H(A, B)")

import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Ensemble

open scoped ComplexConjugate

namespace DattaDiscord

/-- **Quantum mutual information** `I(A : B) = H(A) + H(B) − H(A, B)`, Datta, *A Condition for the Nullity of Quantum Discord*, arXiv:1003.5256v2, p.1, where
`H` is the von Neumann entropy in bits.

**Formalization Note** `H(A) = H(ρ_A)` with `ρ_A = QAlgorithms.traceRight ρ` (trace out `B`),
`H(B) = H(ρ_B)` with `ρ_B = QAlgorithms.traceLeft ρ` (trace out `A`), and `H(A, B) = H(ρ_AB)`;
`H` is the published `QAlgorithms.vnEntropy` (base 2). -/
noncomputable def mutualInfo {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (ρ : Matrix (A × B) (A × B) ℂ) : ℝ :=
  QAlgorithms.vnEntropy (QAlgorithms.traceRight ρ) + QAlgorithms.vnEntropy (QAlgorithms.traceLeft ρ)
    - QAlgorithms.vnEntropy ρ

end DattaDiscord


