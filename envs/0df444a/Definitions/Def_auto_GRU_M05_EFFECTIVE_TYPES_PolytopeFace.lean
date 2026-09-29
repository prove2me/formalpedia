-- Prove2me | Definitions.Def_auto_GRU_M05_EFFECTIVE_TYPES_PolytopeFace
-- name    : auto_GRU_M05_EFFECTIVE_TYPES_PolytopeFace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T19:11:14.1633+00:00
-- url     : https://prove2.me/theorems/fef1dc85-660a-4ed0-9d12-617a2c2d101f
-- title:
--   The full face poset
-- statement:
--   All exposed faces ordered by inclusion, including the empty face and the whole polytope.
-- source:
--   Grünbaum, Convex Polytopes, 2nd ed., Springer (2003), §2.4, printed p.17; §12.3, printed p.231

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Set.Card
import Mathlib.Order.Hom.Basic

set_option autoImplicit false
open scoped BigOperators


namespace Grunbaum2003

abbrev PolytopeFace {d : ℕ} (P : Set (Fin d → ℝ)) :=
  {F : Set (Fin d → ℝ) // IsExposed ℝ P F}

end Grunbaum2003


