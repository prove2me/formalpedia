-- Prove2me | Definitions.Def_auto_GRU_M05_GALE_EQ_IsDPolytope
-- name    : auto_GRU_M05_GALE_EQ_IsDPolytope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T19:03:31.93574+00:00
-- url     : https://prove2.me/theorems/f58f3b97-f2f2-4be1-8c3f-eaef1fcb5d4d
-- title:
--   Full-dimensional real polytopes
-- statement:
--   A nonempty finite convex hull in real coordinate space whose affine span is the whole space.
-- source:
--   Grünbaum, Convex Polytopes (2003), §3.1, printed p.31

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Set.Card
import Mathlib.Order.Hom.Basic
import Mathlib.Analysis.Convex.Intrinsic
set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

def IsDPolytope {d : ℕ} (P : Set (Fin d → ℝ)) : Prop :=
  (∃ V : Set (Fin d → ℝ), V.Finite ∧ V.Nonempty ∧ P = convexHull ℝ V) ∧
    affineSpan ℝ P = ⊤

end Grunbaum2003


