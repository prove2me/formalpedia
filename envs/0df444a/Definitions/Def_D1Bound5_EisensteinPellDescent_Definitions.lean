-- Prove2me | Definitions.Def_D1Bound5_EisensteinPellDescent_Definitions
-- name    : D1Bound5_EisensteinPellDescent_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T03:33:53.345015+00:00
-- url     : https://prove2.me/theorems/02f3fc0e-0419-4752-9839-8cd8410697ad
-- title:
--   Eisenstein Pell Descent
-- statement:
--   Definitions for eisenstein pell descent in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `eisensteinCoordinateNorm`.
-- source:
--   D1Bound5/EisensteinPellDescent.lean, lines 7-7, SHA-256 cd2aa636e64bfd71d3cf36b1229109297e3ce100e0b6bdea085db37182ddca75. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5
open QuadInt

 def eisensteinCoordinateNorm (x y : ℤ) : ℤ := x^2+x*y+y^2











end D1Bound5
end


