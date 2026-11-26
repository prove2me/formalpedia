-- Prove2me | Definitions.Def_Eden_AttractorDistance
-- name    : Eden_AttractorDistance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:11:58.004942+00:00
-- url     : https://prove2.me/theorems/d1f2f6d8-7544-57a1-b209-f536f9100b2b
-- title:
--   Attractor Distance
-- statement:
--   Definitions and structural lemmas for Attractor Distance, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/AttractorDistance.lean

import Definitions.Def_Eden_InvariantSets
import Mathlib.Topology.MetricSpace.HausdorffDistance
set_option autoImplicit true
noncomputable section
namespace Eden
def discScale (r : ℝ) : ℝ := if r ≤ Real.sqrt 2 then 1 else Real.sqrt 2 / r
def attractorProjection (p : PhaseSpace) : PhaseSpace :=
  !₂[discScale (Real.sqrt (radiusSq₁ p)) * p 0,
     discScale (Real.sqrt (radiusSq₁ p)) * p 1,
     discScale (Real.sqrt (radiusSq₂ p)) * p 2,
     discScale (Real.sqrt (radiusSq₂ p)) * p 3, 0]
end Eden


