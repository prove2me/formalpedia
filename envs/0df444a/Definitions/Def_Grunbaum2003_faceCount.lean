-- Prove2me | Definitions.Def_Grunbaum2003_faceCount
-- name    : Grunbaum2003_faceCount
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:34:32.270145+00:00
-- url     : https://prove2.me/theorems/10c24d7b-794a-4e5f-b27f-9e733d031aaf
-- title:
--   Number of nonempty faces of a given dimension
-- statement:
--   The finite cardinality of nonempty exposed faces of affine dimension k.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §§2.4, 3.1, 8.1, printed pp. 17, 31, 130 / PDF pp. 35, 51, 162; nonempty face-count convention; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Set.Card

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

noncomputable def faceCount {d : ℕ} (P : Set (Fin d → ℝ)) (k : ℕ) : ℕ :=
  {F : Set (Fin d → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
    Module.finrank ℝ (affineSpan ℝ F).direction = k}.ncard

end Grunbaum2003


