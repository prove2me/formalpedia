-- Prove2me | Definitions.Def_EthierKurtz_BoundaryCOnceHolder
-- name    : EthierKurtz_BoundaryCOnceHolder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:12:47.096198+00:00
-- url     : https://prove2.me/theorems/0ae82931-2dd9-4b3e-9bf8-169214f5bb66
-- title:
--   C¹,μ boundary-function regularity
-- statement:
--   A scalar boundary function whose pullback through a local orthogonal boundary graph chart has C¹,μ regularity.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 8, Section 1, boundary-function convention for Theorem 1.5, printed pp. 368–369 (PDF pp. 377–378).

import Definitions.Def_EthierKurtz_CTwiceHolder
import Definitions.Def_EthierKurtz_COnceHolder

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- C^{1,μ} boundary functions in the orthogonal graph coordinates of p. 368.
The sign of the last coordinate is immaterial for this regularity predicate.
The ambient function is used only on the frontier. -/
def BoundaryCOnceHolder {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) (μ : ℝ)
    (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) : Prop :=
  ∀ x₀ ∈ frontier Ω, ∃ ρ : ℝ, 0 < ρ ∧
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
            EuclideanSpace ℝ (Fin (n + 1)))) '' D ∧
      COnceHolder D μ (fun z => φ (x₀ + U.symm
        (WithLp.toLp 2 (Fin.lastCases (u z) (fun i => z i)))))

end EthierKurtz


