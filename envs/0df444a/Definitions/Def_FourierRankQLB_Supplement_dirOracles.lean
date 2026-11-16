-- Prove2me | Definitions.Def_FourierRankQLB_Supplement_dirOracles
-- name    : FourierRankQLB_Supplement_dirOracles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:12:42.921224+00:00
-- url     : https://prove2.me/theorems/a21549db-39d9-40d3-bb1d-2eeffd5dec5b
-- title:
--   Oracle sequence with slot directions $P$ or $P^{-1}$
-- statement:
--   Given a unitary oracle $P$ on a Hilbert space $H$ and a direction vector $\mathrm{inv} \in \{\mathrm{false},\mathrm{true}\}^T$, the oracle sequence of a $T$-query algorithm applies at slot $j$
--
--   $$
--   O_j = \begin{cases} P, & \mathrm{inv}_j = \mathrm{false},\\ P^{-1}, & \mathrm{inv}_j = \mathrm{true}.\end{cases}
--   $$
--
--   In the phase models of the paper one application of $P_Q$ or $P_Q^{-1}$ is one matrix phase query (p.15), and one application of $G_f$ or $G_f^{-1}$ is one gradient query (p.33). The direction vector is part of the algorithm and is fixed before the hidden input.
--
--   **Formalization Note** Query slots are indexed $0,\dots,T-1$, as in the base mission's `QueryCircuit`.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §2.4, p.15 and §6, p.33

import Mathlib

namespace FourierRankQLB

namespace Supplement

/-- The oracle sequence of a phase-model algorithm: slot `j` applies the oracle `P` when
`inv j = false` and its inverse `P⁻¹` when `inv j = true`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, p. 15 ("one application of `P_Q` or `P_Q⁻¹` is a matrix phase query") and p. 33 ("one application of `G_f` or `G_f⁻¹` counts as one gradient query").

**Formalization Note.** The direction vector `inv` belongs to the algorithm and is fixed before the
hidden input, like the rest of the circuit. Query slots are indexed `0, …, T - 1`. -/
def dirOracles {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (P : H ≃ₗᵢ[ℂ] H)
    {T : ℕ} (inv : Fin T → Bool) : Fin T → (H ≃ₗᵢ[ℂ] H) :=
  fun j => if inv j then P.symm else P

end Supplement

end FourierRankQLB


