-- Prove2me | Definitions.Def_D1Bound5_FiniteA3RatioHeight_Definitions
-- name    : D1Bound5_FiniteA3RatioHeight_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:09:46.98854+00:00
-- url     : https://prove2.me/theorems/9326c687-e341-4f1f-ab1e-d7bcb763b6d0
-- title:
--   Finite A3Ratio Height
-- statement:
--   Definitions for finite a3ratio height in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `finiteA3RatioWeights`, `fiveRegionA3Height`.
-- source:
--   D1Bound5/FiniteA3RatioHeight.lean, lines 8-12, SHA-256 747d84efb3a599bfd5fb9dfc2190b17d3fd8f676687d8e8b401785ccf8d1c7d7; D1Bound5/FiniteA3RatioHeight.lean, lines 14-14, SHA-256 747d84efb3a599bfd5fb9dfc2190b17d3fd8f676687d8e8b401785ccf8d1c7d7. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteA3Coefficients_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions

section
noncomputable section

namespace D1Bound5

def finiteA3RatioWeights (r : ℝ) (i : Fin 3) : Fin 4 → ℝ :=
  ![finiteHomogeneousRatioWeight 3 (finiteA3Coeff0 i 0) r+finiteHomogeneousRatioWeight 3 (finiteA3Coeff0 i 1) r,
    finiteHomogeneousRatioWeight 4 (finiteA3Coeff1 i 0) r+finiteHomogeneousRatioWeight 4 (finiteA3Coeff1 i 1) r,
    finiteHomogeneousRatioWeight 5 (finiteA3Coeff2 i 0) r+finiteHomogeneousRatioWeight 5 (finiteA3Coeff2 i 1) r,
    finiteHomogeneousRatioWeight 6 (finiteA3Coeff3 i 0) r+finiteHomogeneousRatioWeight 6 (finiteA3Coeff3 i 1) r]

def fiveRegionA3Height : Fin 5 → ℝ := ![145,326,663,863,1944]









end D1Bound5
end


