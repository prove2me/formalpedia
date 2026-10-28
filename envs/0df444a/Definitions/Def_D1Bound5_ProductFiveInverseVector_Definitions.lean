-- Prove2me | Definitions.Def_D1Bound5_ProductFiveInverseVector_Definitions
-- name    : D1Bound5_ProductFiveInverseVector_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:54:01.542257+00:00
-- url     : https://prove2.me/theorems/73a5a4fb-d2c9-4eec-bb34-ad6d4ee58867
-- title:
--   Product Five Inverse Vector
-- statement:
--   Definitions for product five inverse vector in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `fiveY`, `fiveZ`.
-- source:
--   D1Bound5/ProductFiveInverseVector.lean, lines 8-8, SHA-256 425de7cb6ba343c242be88e9088726741289138c3dff82b0611bd3b9f173bbee; D1Bound5/ProductFiveInverseVector.lean, lines 9-9, SHA-256 425de7cb6ba343c242be88e9088726741289138c3dff82b0611bd3b9f173bbee. Project: https://github.com/tomislav-math/d1-bound5-lean

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

 noncomputable def fiveY : Fin 4 → ℂ := fun _ => (1/3 : ℂ)
 noncomputable def fiveZ : Fin 4 → ℂ := fun _ => (1/2 : ℂ)








end D1Bound5
end


