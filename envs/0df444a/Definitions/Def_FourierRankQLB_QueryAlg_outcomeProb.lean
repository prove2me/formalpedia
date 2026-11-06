-- Prove2me | Definitions.Def_FourierRankQLB_QueryAlg_outcomeProb
-- name    : FourierRankQLB_QueryAlg_outcomeProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:42:12.641959+00:00
-- url     : https://prove2.me/theorems/f353f06b-7c96-41b6-9bde-7f32549f958e
-- title:
--   The outcome probability of a query algorithm
-- statement:
--   The probability that the algorithm, run against the oracles $O_1,\dots,O_T$, returns an element of a set $S$ of outcomes: $\langle\psi_T,E(S)\psi_T\rangle$.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (15), p.16 and §3.1, p.18

import Mathlib
import Definitions.Def_FourierRankQLB_QueryAlg
import Definitions.Def_FourierRankQLB_POVM_prob
import Definitions.Def_FourierRankQLB_QueryCircuit_finalState

namespace FourierRankQLB

/-- The probability that the algorithm, run against the oracles `O`, outputs an element of `S`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (15), p. 16 and §3.1, p. 18. -/
noncomputable def QueryAlg.outcomeProb {H X : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [MeasurableSpace X] (A : QueryAlg H X)
    (O : Fin A.T → (H ≃ₗᵢ[ℂ] H)) (S : Set X) : ℝ :=
  A.meas.prob (A.toQueryCircuit.finalState O) S

end FourierRankQLB


