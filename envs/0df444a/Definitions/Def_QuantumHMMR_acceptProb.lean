-- Prove2me | Definitions.Def_QuantumHMMR_acceptProb
-- name    : QuantumHMMR_acceptProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:37:03.7617+00:00
-- url     : https://prove2.me/theorems/e3f4fcad-3774-4c9b-8586-de1f1f9451fd
-- title:
--   Acceptance probability $\mathrm{Tr}[M_A |A^U_t\rangle\langle A^U_t|]$
-- statement:
--   For a $t$-query algorithm followed by a two-outcome measurement $(M_A, I - M_A)$, the probability of the first outcome when the oracle is $U$ is
--   $$
--   p_{A,M_A}(U) = \mathrm{Tr}\big[M_A \cdot |A^U_t\rangle\langle A^U_t|\big].
--   $$
--   Its averages over $U \sim \nu$ and $U \sim \mu_H$ are compared in the definition of an adaptive design.
--
--   **Formalization Note** Computed as the published `effectProb` $\mathrm{Re}\,\mathrm{Tr}(M\rho)$ of the published `pureDensity` $\rho = |\psi\rangle\langle\psi|$; for an effect the trace is real.
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Definition 3.1, Eq. (6), p.10

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QuantumHMMR_adaptiveState

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45

namespace QuantumHMMR

/-- The acceptance probability `Tr[M_A · |A^U_t⟩⟨A^U_t|]` of a `t`-query algorithm followed by the
two-outcome measurement `(M_A, I - M_A)` (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), Eq. (6), p.10), as a function of the oracle `U`.

**Formalization Note** Computed with the published `effectProb M ρ = Re Tr(M ρ)` and
`pureDensity ψ = |ψ⟩⟨ψ|`; for an effect `0 ⪯ M ⪯ I` the trace is real. -/
noncomputable def acceptProb {n t : ℕ} (alg : AdaptiveAlg n t)
    (M : Matrix (Qubits (n + alg.anc)) (Qubits (n + alg.anc)) ℂ) (U : QMat n) : ℝ :=
  effectProb M (pureDensity (adaptiveState alg U))

end QuantumHMMR


