-- Prove2me | Definitions.Def_EthierKurtz_closedRegionRestriction
-- name    : EthierKurtz_closedRegionRestriction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:10:54.852269+00:00
-- url     : https://prove2.me/theorems/62749e25-a5e6-4e1d-8f5e-45e10406002e
-- title:
--   Ambient extension of a closed-region function
-- statement:
--   The ambient scalar function agreeing with a bounded continuous function on the closed region and set to zero outside it, used only for interior differentiation.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 8, Section 1, equations (1.15) and (1.17), printed p. 368 (PDF p. 377).

import Mathlib

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

open Classical in
/-- Ambient extension used only for differentiation at interior points. -/
noncomputable def closedRegionRestriction {d : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (f : (closure Ω) →ᵇ ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  if hx : x ∈ closure Ω then f ⟨x, hx⟩ else 0

end EthierKurtz


