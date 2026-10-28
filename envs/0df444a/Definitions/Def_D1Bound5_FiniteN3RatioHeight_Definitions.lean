-- Prove2me | Definitions.Def_D1Bound5_FiniteN3RatioHeight_Definitions
-- name    : D1Bound5_FiniteN3RatioHeight_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:09:22.870831+00:00
-- url     : https://prove2.me/theorems/32b43fe8-2e52-458f-a8a2-53cf4961394a
-- title:
--   Finite N3Ratio Height
-- statement:
--   Definitions for finite n3ratio height in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `finiteN3RatioRootCoeff`, `finiteN3RatioWeights`, `fiveRegionN3Height`.
-- source:
--   D1Bound5/FiniteN3RatioHeight.lean, lines 8-12, SHA-256 3b19adaab7a046dd5d462fa93e9c3522cc668117966f660bde17388fd5b6b587; D1Bound5/FiniteN3RatioHeight.lean, lines 22-26, SHA-256 3b19adaab7a046dd5d462fa93e9c3522cc668117966f660bde17388fd5b6b587; D1Bound5/FiniteN3RatioHeight.lean, lines 28-28, SHA-256 3b19adaab7a046dd5d462fa93e9c3522cc668117966f660bde17388fd5b6b587. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousTwo_Definitions
import Definitions.Def_D1Bound5_FiniteN3Height_Definitions

section
noncomputable section

namespace D1Bound5

def finiteN3RatioRootCoeff {R : Type*} [CommRing R] (x y : R) (i : Fin 3) (j : Fin 2) : Fin 4 → R :=
  ![finiteHomogeneousTwo 4 (finiteN3Coeff0 i j) x y,
    finiteHomogeneousTwo 5 (finiteN3Coeff1 i j) x y,
    finiteHomogeneousTwo 6 (finiteN3Coeff2 i j) x y,
    finiteHomogeneousTwo 7 (finiteN3Coeff3 i j) x y]



def finiteN3RatioWeights (r : ℝ) (i : Fin 3) : Fin 4 → ℝ :=
  ![finiteHomogeneousRatioWeight 4 (finiteN3Coeff0 i 0) r+finiteHomogeneousRatioWeight 4 (finiteN3Coeff0 i 1) r,
    finiteHomogeneousRatioWeight 5 (finiteN3Coeff1 i 0) r+finiteHomogeneousRatioWeight 5 (finiteN3Coeff1 i 1) r,
    finiteHomogeneousRatioWeight 6 (finiteN3Coeff2 i 0) r+finiteHomogeneousRatioWeight 6 (finiteN3Coeff2 i 1) r,
    finiteHomogeneousRatioWeight 7 (finiteN3Coeff3 i 0) r+finiteHomogeneousRatioWeight 7 (finiteN3Coeff3 i 1) r]

def fiveRegionN3Height : Fin 5 → ℝ := ![282,697,1306,1652,3553]









end D1Bound5
end


