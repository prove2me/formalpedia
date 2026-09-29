-- Prove2me | Definitions.Def_auto_GRU_M05_PRESCRIBED_IsDPolytope
-- name    : auto_GRU_M05_PRESCRIBED_IsDPolytope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T19:04:41.667974+00:00
-- url     : https://prove2.me/theorems/9e85e784-9237-4d53-aecf-486dc61ae148
-- title:
--   Full-dimensional nonempty real polytopes
-- statement:
--   A nonempty finite convex hull in real coordinate space whose affine span is the whole space.
-- source:
--   Branko Grünbaum, Convex Polytopes, second edition (2003), §3.1 printed p.31 (finite hulls and faces); §2.4 printed p.17 (faces).

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Set.Card

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

def auto_GRU_M05_PRESCRIBED_IsDPolytope {d : ℕ} (P : Set (Fin d → ℝ)) : Prop :=
  (∃ V : Set (Fin d → ℝ), V.Finite ∧ V.Nonempty ∧ P = convexHull ℝ V) ∧
    affineSpan ℝ P = ⊤

end Grunbaum2003


