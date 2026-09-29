-- Prove2me | Definitions.Def_auto_GRU_M05_EFFECTIVE_TYPES_faceCount
-- name    : auto_GRU_M05_EFFECTIVE_TYPES_faceCount
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T19:11:04.084388+00:00
-- url     : https://prove2.me/theorems/e5fc410e-6c7d-4ad8-9a3c-790b7d4874dc
-- title:
--   Number of nonempty faces of a given dimension
-- statement:
--   The number of nonempty exposed faces of affine dimension k, counting the whole polytope when it has dimension k.
-- source:
--   Grünbaum, Convex Polytopes, 2nd ed., Springer (2003), §2.4, printed p.17; §3.1, printed p.31

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Set.Card
import Mathlib.Order.Hom.Basic

set_option autoImplicit false
open scoped BigOperators


namespace Grunbaum2003

noncomputable def faceCount {d : ℕ} (P : Set (Fin d → ℝ)) (k : ℕ) : ℕ :=
  {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
    Module.finrank ℝ (affineSpan ℝ F).direction = k}.ncard

end Grunbaum2003


