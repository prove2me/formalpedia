-- Prove2me | Definitions.Def_FourierRankQLB_QueryCircuit_stateAt
-- name    : FourierRankQLB_QueryCircuit_stateAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:25.004235+00:00
-- url     : https://prove2.me/theorems/49cad87a-8b0c-4c5d-9adf-92aa12d45378
-- title:
--   The state after $k$ queries
-- statement:
--   For oracles $O_1,\dots,O_T$, the state after $k$ queries,
--   $$
--   U_kO_kU_{k-1}\cdots U_1O_1U_0|\psi_0\rangle .
--   $$
--
--   **Formalization Note** The query slots are indexed from $0$ in Lean.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (15), p.16

import Mathlib
import Definitions.Def_FourierRankQLB_QueryCircuit

namespace FourierRankQLB

/-- The state `U_k O_k U_{k-1} ⋯ O_1 U_0 |ψ₀⟩` after `k` queries, for oracles `O`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (15), p. 16.

**Formalization Note.** The query slots `O_1, …, O_T` of the paper are indexed `0, …, T - 1` here. -/
noncomputable def QueryCircuit.stateAt {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (C : QueryCircuit H) (O : Fin C.T → (H ≃ₗᵢ[ℂ] H)) : (k : ℕ) → k < C.T + 1 → H
  | 0, _ => C.U 0 C.ψ₀
  | k + 1, hk => C.U ⟨k + 1, hk⟩ (O ⟨k, Nat.lt_of_succ_lt_succ hk⟩
      (QueryCircuit.stateAt C O k (Nat.lt_of_succ_lt hk)))

end FourierRankQLB


