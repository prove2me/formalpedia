-- Prove2me | Definitions.Def_EthierKurtz_intervalRealRestriction
-- name    : EthierKurtz_intervalRealRestriction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:06:16.158176+00:00
-- url     : https://prove2.me/theorems/9a4e3143-1f79-48ea-b5d4-a0bd90f0c0c8
-- title:
--   Real restriction of a continuous function on an extended interval
-- statement:
--   Restrict a continuous real-valued function on the compact extended interval to its real points, using zero only outside the interval where interior derivatives and endpoint limits do not inspect it.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 1, equations (1.1), (1.8), printed pp. 366–367 (PDF pp. 375–376).

import Mathlib

open Filter MeasureTheory
open scoped Topology ENNReal

namespace EthierKurtz

/-- Restrict a continuous function on the compact extended interval to real
points. The zero extension outside the interval is immaterial to interior
ordinary derivatives and to interior endpoint limits. -/
noncomputable def intervalRealRestriction {r₀ r₁ : EReal}
    (f : C(Set.Icc r₀ r₁, ℝ)) (x : ℝ) : ℝ :=
  if hx : (x : EReal) ∈ Set.Icc r₀ r₁ then f ⟨x, hx⟩ else 0

end EthierKurtz


