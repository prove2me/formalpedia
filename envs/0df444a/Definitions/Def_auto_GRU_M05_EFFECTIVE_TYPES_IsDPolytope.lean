-- Prove2me | Definitions.Def_auto_GRU_M05_EFFECTIVE_TYPES_IsDPolytope
-- name    : auto_GRU_M05_EFFECTIVE_TYPES_IsDPolytope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T19:10:52.28834+00:00
-- url     : https://prove2.me/theorems/381dfb79-5636-4ac3-ba74-38b959ea9ff4
-- title:
--   Full-dimensional real polytopes
-- statement:
--   A nonempty finite convex hull in real coordinate space whose affine span is the whole space.
-- source:
--   Grünbaum, Convex Polytopes, 2nd ed., Springer (2003), §3.1, printed p.31

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Set.Card
import Mathlib.Order.Hom.Basic

set_option autoImplicit false
open scoped BigOperators


namespace Grunbaum2003

def IsDPolytope {d : ℕ} (P : Set (Fin d → ℝ)) : Prop :=
  (∃ V : Set (Fin d → ℝ), V.Finite ∧ V.Nonempty ∧ P = convexHull ℝ V) ∧
    affineSpan ℝ P = ⊤

end Grunbaum2003


