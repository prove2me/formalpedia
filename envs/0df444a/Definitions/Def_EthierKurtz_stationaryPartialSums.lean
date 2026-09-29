-- Prove2me | Definitions.Def_EthierKurtz_stationaryPartialSums
-- name    : EthierKurtz_stationaryPartialSums
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:59:37.3369+00:00
-- url     : https://prove2.me/theorems/0267e858-f4bc-474e-9b67-7b30f9575c1a
-- title:
--   Scaled stationary partial-sum process
-- statement:
--   The one-dimensional process whose value at nonnegative time t is the sum of Y_1 through Y_floor((n+1)t), divided by the square root of n+1.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 7, Section 3, equation (3.2), printed p. 351 (PDF p. 360).

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

/-- Equation (3.2), with positive scaling index n+1 and the real line
identified with one-dimensional Euclidean space. -/
noncomputable def stationaryPartialSums {Ω : Type*}
    (Y : ℤ → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) : EuclideanSpace ℝ (Fin 1) :=
  WithLp.toLp 2 (fun _ =>
    (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ *
      ∑ k ∈ Finset.range ⌊((n + 1 : ℕ) : ℝ) * (t : ℝ)⌋₊, Y ((k : ℤ) + 1) ω)

end EthierKurtz


