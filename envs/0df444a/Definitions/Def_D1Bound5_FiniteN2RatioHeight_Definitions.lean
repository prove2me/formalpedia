-- Prove2me | Definitions.Def_D1Bound5_FiniteN2RatioHeight_Definitions
-- name    : D1Bound5_FiniteN2RatioHeight_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:09:26.73535+00:00
-- url     : https://prove2.me/theorems/0e009eb8-35e9-4b87-a683-241af0d3a0b0
-- title:
--   Finite N2Ratio Height
-- statement:
--   Definitions for finite n2ratio height in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `finiteN2RatioRootCoeff`, `finiteN2RatioWeights`, `fiveRegionN2Height`.
-- source:
--   D1Bound5/FiniteN2RatioHeight.lean, lines 8-11, SHA-256 acd86dd6afa56a2834a76abb67f2f38aa493cf97b505b550e022ae5087305669; D1Bound5/FiniteN2RatioHeight.lean, lines 21-24, SHA-256 acd86dd6afa56a2834a76abb67f2f38aa493cf97b505b550e022ae5087305669; D1Bound5/FiniteN2RatioHeight.lean, lines 26-26, SHA-256 acd86dd6afa56a2834a76abb67f2f38aa493cf97b505b550e022ae5087305669. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteN2Height_Definitions

section
noncomputable section

namespace D1Bound5

def finiteN2RatioRootCoeff {R : Type*} [CommRing R] (x y : R) (i : Fin 3) (j : Fin 2) : Fin 3 → R :=
  ![finiteHomogeneousTwo 2 (finiteN2Coeff0 i j) x y,
    finiteHomogeneousTwo 3 (finiteN2Coeff1 i j) x y,
    finiteHomogeneousTwo 4 (finiteN2Coeff2 i j) x y]



def finiteN2RatioWeights (r : ℝ) (i : Fin 3) : Fin 3 → ℝ :=
  ![finiteHomogeneousRatioWeight 2 (finiteN2Coeff0 i 0) r+finiteHomogeneousRatioWeight 2 (finiteN2Coeff0 i 1) r,
    finiteHomogeneousRatioWeight 3 (finiteN2Coeff1 i 0) r+finiteHomogeneousRatioWeight 3 (finiteN2Coeff1 i 1) r,
    finiteHomogeneousRatioWeight 4 (finiteN2Coeff2 i 0) r+finiteHomogeneousRatioWeight 4 (finiteN2Coeff2 i 1) r]

def fiveRegionN2Height : Fin 5 → ℝ := ![36,69,109,130,220]









end D1Bound5
end


