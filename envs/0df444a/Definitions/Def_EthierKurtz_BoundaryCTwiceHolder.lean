-- Prove2me | Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
-- name    : EthierKurtz_BoundaryCTwiceHolder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:09:59.595984+00:00
-- url     : https://prove2.me/theorems/47e06ade-092e-4e0a-9dc8-f4dbfde57a4d
-- title:
--   C²,μ boundary regularity
-- statement:
--   A bounded-region boundary admitting uniform-radius orthogonal graph charts whose graphing functions have C²,μ regularity and horizontal tangent plane at each chart center.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 8, Section 1, boundary convention preceding Theorem 1.4, printed p. 368 (PDF p. 377).

import Definitions.Def_EthierKurtz_CTwiceHolder

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- The source's uniform-radius orthogonal graph charts. Zero derivative
at the chart origin identifies the last axis as normal. Its sign is irrelevant
to this boundary regularity predicate (and may be chosen outward). -/
def BoundaryCTwiceHolder {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) (μ : ℝ) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∀ x₀ ∈ frontier Ω,
    ∃ U : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin (n + 1)),
    ∃ D : Set (EuclideanSpace ℝ (Fin n)),
    ∃ u : EuclideanSpace ℝ (Fin n) → ℝ,
      IsOpen D ∧ (0 : EuclideanSpace ℝ (Fin n)) ∈ D ∧
      CTwiceHolder D μ u ∧ u 0 = 0 ∧ fderiv ℝ u 0 = 0 ∧
      IsConnected (frontier Ω ∩ Metric.ball x₀ ρ) ∧
      (fun x => U (x - x₀)) '' (frontier Ω ∩ Metric.ball x₀ ρ) =
        (fun z : EuclideanSpace ℝ (Fin n) =>
          (WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i)) :
            EuclideanSpace ℝ (Fin (n + 1)))) '' D

end EthierKurtz


