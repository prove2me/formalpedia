-- Prove2me | Definitions.Def_FourierRankQLB_QueryCircuit_finalState
-- name    : FourierRankQLB_QueryCircuit_finalState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:54.084528+00:00
-- url     : https://prove2.me/theorems/268d2deb-a778-44a5-b701-ac2a4794012a
-- title:
--   The final state $|\psi_T\rangle$ of Eq. (15)
-- statement:
--   The final state of a $T$-query algorithm,
--   $$
--   |\psi_T\rangle=U_TO_TU_{T-1}\cdots U_1O_1U_0|\psi_0\rangle .
--   $$
--   With $O_j=O_{Q,j}$ it is the state whose dependence on $Q$ the Fourier-rank method tracks.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (15), p.16

import Mathlib
import Definitions.Def_FourierRankQLB_QueryCircuit_stateAt

namespace FourierRankQLB

/-- The final state `|ψ_T⟩ = U_T O_T U_{T-1} ⋯ U_1 O_1 U_0 |ψ₀⟩` of Eq. (15).

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (15), p. 16. -/
noncomputable def QueryCircuit.finalState {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (C : QueryCircuit H) (O : Fin C.T → (H ≃ₗᵢ[ℂ] H)) : H :=
  C.stateAt O C.T (Nat.lt_succ_self _)

end FourierRankQLB


