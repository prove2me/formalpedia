-- Prove2me | Definitions.Def_auto_GRU_M05_GALE_EQ_PolytopeFace
-- name    : auto_GRU_M05_GALE_EQ_PolytopeFace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T19:03:47.892066+00:00
-- url     : https://prove2.me/theorems/642e52ba-642b-448a-9012-280329951b0c
-- title:
--   The full face poset
-- statement:
--   All exposed faces of a polytope, ordered by inclusion, including the empty face and the polytope itself.
-- source:
--   Grünbaum, Convex Polytopes (2003), §2.4, printed p.17; §5.4, printed p.89

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

abbrev PolytopeFace {d : ℕ} (P : Set (Fin d → ℝ)) :=
  {F : Set (Fin d → ℝ) // IsExposed ℝ P F}

end Grunbaum2003


