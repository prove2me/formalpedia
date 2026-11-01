-- Prove2me | Definitions.Def_DattaDiscord_condState
-- name    : DattaDiscord_condState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:21:48.998871+00:00
-- url     : https://prove2.me/theorems/5a6e752b-c983-4d02-b134-f22e5bd378e2
-- title:
--   Post-measurement state $\rho_{A|i}=\mathrm{Tr}_B(\Pi_i\rho_{AB})/p_i$
-- statement:
--   Let $\rho_{AB}$ be an operator on $\mathcal H_A\otimes\mathcal H_B$ and $\Pi$ a POVM element on $B$, with outcome probability $p$ (`outcomeProb`). The state of $A$ after the measurement of $B$ gives this outcome is, by Eq. (1),
--
--   $$
--   \rho_{A|\Pi}=\frac{\mathrm{Tr}_B\big((I_A\otimes\Pi)\,\rho_{AB}\big)}{p},
--   $$
--
--   where $\mathrm{Tr}_B$ is the partial trace over $B$.
--
--   **Formalization Note** $\mathrm{Tr}_B$ is the published `QAlgorithms.traceRight` (it traces out the second factor). When $p=0$, Lean's convention $0^{-1}=0$ makes $\rho_{A|\Pi}$ the zero matrix; every use multiplies it by $p$, so this value never contributes.
-- source:
--   Datta, A Condition for the Nullity of Quantum Discord, arXiv:1003.5256v2, Eq. (1), p.1

import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_DattaDiscord_outcomeProb

open scoped ComplexConjugate

namespace DattaDiscord

/-- **Post-measurement state of `A`**, Datta, *A Condition for the Nullity of Quantum Discord*, arXiv:1003.5256v2, Eq. (1), p.1: the state of `A` after the
measurement of `B` gives the outcome with POVM element `Π` is
`ρ_{A|Π} = Tr_B(Π ρ_AB) / p`, with `p = Tr_{A,B}(Π ρ_AB)` (`outcomeProb`).

**Formalization Note** `Tr_B` is the published `QAlgorithms.traceRight` (it traces out the second
factor `B`), and `Π` acts as `I_A ⊗ Π`. When `p = 0` Lean's `0⁻¹ = 0` makes the state the zero
matrix; every place it is used multiplies it by `p`, so the junk value never contributes. -/
noncomputable def condState {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (ρ : Matrix (A × B) (A × B) ℂ) (M : Matrix B B ℂ) : Matrix A A ℂ :=
  ((outcomeProb ρ M : ℂ)⁻¹) •
    QAlgorithms.traceRight (Matrix.kronecker (1 : Matrix A A ℂ) M * ρ)

end DattaDiscord


