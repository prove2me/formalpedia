-- Prove2me | Definitions.Def_D1Bound5_FiniteA4RatioHeight_Definitions
-- name    : D1Bound5_FiniteA4RatioHeight_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:09:49.034463+00:00
-- url     : https://prove2.me/theorems/db29a38c-d0b7-4446-92b8-831315eeb87e
-- title:
--   Finite A4Ratio Height
-- statement:
--   Definitions for finite a4ratio height in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `finiteA4RatioWeights`, `fiveRegionA4Height`.
-- source:
--   D1Bound5/FiniteA4RatioHeight.lean, lines 8-13, SHA-256 a98d9593d896e1b8a0048726d24791b93b2bacc8fb14d4196e608cc3b8ddd02c; D1Bound5/FiniteA4RatioHeight.lean, lines 15-15, SHA-256 a98d9593d896e1b8a0048726d24791b93b2bacc8fb14d4196e608cc3b8ddd02c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteA4Coefficients_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions

section
noncomputable section

namespace D1Bound5

def finiteA4RatioWeights (r : ℝ) (i : Fin 3) : Fin 5 → ℝ :=
  ![finiteHomogeneousRatioWeight 5 (finiteA4Coeff0 i 0) r+finiteHomogeneousRatioWeight 5 (finiteA4Coeff0 i 1) r,
    finiteHomogeneousRatioWeight 6 (finiteA4Coeff1 i 0) r+finiteHomogeneousRatioWeight 6 (finiteA4Coeff1 i 1) r,
    finiteHomogeneousRatioWeight 7 (finiteA4Coeff2 i 0) r+finiteHomogeneousRatioWeight 7 (finiteA4Coeff2 i 1) r,
    finiteHomogeneousRatioWeight 8 (finiteA4Coeff3 i 0) r+finiteHomogeneousRatioWeight 8 (finiteA4Coeff3 i 1) r,
    finiteHomogeneousRatioWeight 9 (finiteA4Coeff4 i 0) r+finiteHomogeneousRatioWeight 9 (finiteA4Coeff4 i 1) r]

def fiveRegionA4Height : Fin 5 → ℝ := ![4605,14771,34919,48019,134712]









end D1Bound5
end


