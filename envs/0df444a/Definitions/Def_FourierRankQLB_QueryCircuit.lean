-- Prove2me | Definitions.Def_FourierRankQLB_QueryCircuit
-- name    : FourierRankQLB_QueryCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:38:11.049816+00:00
-- url     : https://prove2.me/theorems/cfe7c2d3-d890-48bc-8909-c3eb1a469a50
-- title:
--   The oracle-independent part of a $T$-query algorithm
-- statement:
--   The data of the form (15) that do not depend on the hidden matrix: the number of queries $T$, a unit initial state $|\psi_0\rangle$ and unitaries $U_0,\dots,U_T$ on a Hilbert space $H$.
--
--   Classical randomness, intermediate measurements and adaptivity are absorbed into this form by purification, and shorter branches by padding.
--
--   **Formalization Note** Being fields of a structure chosen before $Q$, these data cannot depend on $Q$. A query slot controlled by the stored history is one plain query between unitaries that swap the answer register with a workspace $|+\rangle$ state, so it needs no field.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (15), p.16

import Mathlib

namespace FourierRankQLB

/-- The oracle-independent data of a `T`-query algorithm (15): the number of queries, the unit
initial state `|ψ₀⟩` and the inter-query unitaries `U₀, …, U_T` on a Hilbert space `H`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (15), p. 16.

**Formalization Note.** These are fields of a structure chosen before the hidden matrix, so none of
them depends on `Q`. The paper reaches the form (15) by purifying classical randomness and
intermediate measurements and padding with identity queries; a query slot controlled by the stored
history is one plain query between unitaries that swap the answer register with a workspace `|+⟩`
state, so it needs no field. -/
structure QueryCircuit (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The number of queries. -/
  T : ℕ
  /-- The initial state. -/
  ψ₀ : H
  /-- The initial state is a unit vector. -/
  norm_ψ₀ : ‖ψ₀‖ = 1
  /-- The unitaries `U₀, …, U_T`. -/
  U : Fin (T + 1) → (H ≃ₗᵢ[ℂ] H)

end FourierRankQLB


