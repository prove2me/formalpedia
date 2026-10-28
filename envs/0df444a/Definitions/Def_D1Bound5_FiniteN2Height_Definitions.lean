-- Prove2me | Definitions.Def_D1Bound5_FiniteN2Height_Definitions
-- name    : D1Bound5_FiniteN2Height_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:31:37.175992+00:00
-- url     : https://prove2.me/theorems/63657c3f-1e74-43cb-b066-81d4cf7c82c6
-- title:
--   Finite N2Height
-- statement:
--   Definitions for finite n2height in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `finiteN2Coeff0`, `finiteN2Coeff1`, `finiteN2Coeff2`.
-- source:
--   D1Bound5/FiniteN2Height.lean, lines 8-11, SHA-256 2243c6283cc2715ea06a1ac894af3fc0ea0e8e3a907fae2e4dc3a502c1037c77; D1Bound5/FiniteN2Height.lean, lines 13-16, SHA-256 2243c6283cc2715ea06a1ac894af3fc0ea0e8e3a907fae2e4dc3a502c1037c77; D1Bound5/FiniteN2Height.lean, lines 18-21, SHA-256 2243c6283cc2715ea06a1ac894af3fc0ea0e8e3a907fae2e4dc3a502c1037c77. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5

def finiteN2Coeff0 : Fin 3 → Fin 2 → Fin 3 → ℤ :=
  ![![![0,20,-4], ![4,-20,0]],
    ![![15,10,-1], ![-4,-20,0]],
    ![![0,-20,-4], ![-1,10,15]]]

def finiteN2Coeff1 : Fin 3 → Fin 2 → Fin 4 → ℤ :=
  ![![![0,0,60,-28], ![28,-60,0,0]],
    ![![0,80,-40,8], ![12,-60,0,0]],
    ![![0,0,-60,12], ![8,-40,80,0]]]

def finiteN2Coeff2 : Fin 3 → Fin 2 → Fin 5 → ℤ :=
  ![![![0,0,0,40,-24], ![24,-40,0,0,0]],
    ![![0,0,80,-80,24], ![16,-40,0,0,0]],
    ![![0,0,0,-40,16], ![24,-80,80,0,0]]]











end D1Bound5
end


