-- Prove2me | Definitions.Def_MayersBC_outcomeDist
-- name    : MayersBC_outcomeDist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:56:13.244561+00:00
-- url     : https://prove2.me/theorems/2857e201-1a7d-4700-ba51-e3d7e7869437
-- title:
--   Outcome distribution of a measurement
-- statement:
--   A measurement on a system in state $\rho$ with POVM elements $\{M_j\}_{j \in J}$ returns outcome $j$ with probability
--
--   $$
--   \Pr(J = j) = \operatorname{Tr}(M_j \rho) .
--   $$
--
--   In the paper, $J_b$ is the outcome of Bob's measurement when Alice's bit is $b$, with $\Pr(J_b = j) = \operatorname{Tr}(M_j\rho_b)$; the Kolmogorov distance and the Bhattacharyya–Wootters overlap are applied to these two distributions.
--
--   **Formalization Note** The measurement is given by its POVM elements; the paper's operators $M_j^{(B)} = P_j U$ have POVM elements $U^\dagger P_j U$. The value is the real part of the trace.
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section d, pp.7–8

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
open QAlgorithms

namespace MayersBC

/-- Mayers, arXiv:quant-ph/9603015v3, section d, pp.7–8: the distribution `j ↦ Pr(J_b = j)` of
the classical outcome `J` of a measurement `{M_j}` on the photons in state `ρ_b`,
`Pr(J = j) = Tr(M_j ρ)`.

**Formalization Note.** The measurement is given by its POVM elements `M_j` (for the page's
operators `M_j^{(B)} = P_j U` the element is `M_j^{(B)†} M_j^{(B)} = U† P_j U`). The outcome set is
any type `J`; the value is the real part of the trace (`QAlgorithms.effectProb`). -/
noncomputable def outcomeDist {J ι : Type} [Fintype ι] (M : J → Matrix ι ι ℂ)
    (ρ : Matrix ι ι ℂ) : J → ℝ :=
  fun j => effectProb (M j) ρ

end MayersBC


