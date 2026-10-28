-- Prove2me | Definitions.Def_D1Bound5_AdjugateCoverage_Definitions
-- name    : D1Bound5_AdjugateCoverage_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:13:20.392917+00:00
-- url     : https://prove2.me/theorems/5818fa35-08f9-451d-845d-cbe62bf13e6c
-- title:
--   Adjugate Coverage
-- statement:
--   Definitions for adjugate coverage in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `symmetricFour`, `symmetricFourAdj`.
-- source:
--   D1Bound5/AdjugateCoverage.lean, lines 9-10, SHA-256 f2847afb95c8defcb8c59c5324b1cbe3904cb7236a7d79d7d2486bba6b9076b4; D1Bound5/AdjugateCoverage.lean, lines 12-16, SHA-256 f2847afb95c8defcb8c59c5324b1cbe3904cb7236a7d79d7d2486bba6b9076b4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5

 def symmetricFour (x y z u v w : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,x,y,z; x,0,u,v; y,u,0,w; z,v,w,0]

 def symmetricFourAdj (x y z u v w : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![2*u*v*w, w^2*x-w*z*u-w*y*v, v^2*y-v*z*u-v*x*w, u^2*z-u*y*v-u*x*w;
     w^2*x-w*z*u-w*y*v, 2*y*z*w, z^2*u-z*y*v-z*x*w, y^2*v-y*x*w-y*z*u;
     v^2*y-v*z*u-v*x*w, z^2*u-z*y*v-z*x*w, 2*x*z*v, x^2*w-x*y*v-x*z*u;
     u^2*z-u*y*v-u*x*w, y^2*v-y*x*w-y*z*u, x^2*w-x*y*v-x*z*u, 2*x*y*u]







end D1Bound5
end


