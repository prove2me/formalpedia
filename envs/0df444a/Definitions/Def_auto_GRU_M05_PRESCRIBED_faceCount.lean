-- Prove2me | Definitions.Def_auto_GRU_M05_PRESCRIBED_faceCount
-- name    : auto_GRU_M05_PRESCRIBED_faceCount
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T19:04:57.113945+00:00
-- url     : https://prove2.me/theorems/4742061f-60f0-4b4e-9554-068732a861b7
-- title:
--   Number of nonempty faces of a specified dimension
-- statement:
--   The number of distinct nonempty exposed faces with affine dimension k. For a polytope this family is finite.
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

noncomputable def auto_GRU_M05_PRESCRIBED_faceCount {d : ℕ} (P : Set (Fin d → ℝ)) (k : ℕ) : ℕ :=
  {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
    Module.finrank ℝ (affineSpan ℝ F).direction = k}.ncard

end Grunbaum2003


