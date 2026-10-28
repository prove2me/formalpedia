-- Prove2me | Definitions.Def_D1Bound5_FiniteA5RatioHeight_Definitions
-- name    : D1Bound5_FiniteA5RatioHeight_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:09:30.063734+00:00
-- url     : https://prove2.me/theorems/3a96b12f-916b-47e8-945b-9200182117c8
-- title:
--   Finite A5Ratio Height
-- statement:
--   Definitions for finite a5ratio height in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `finiteA5RatioWeights`, `fiveRegionA5Height`.
-- source:
--   D1Bound5/FiniteA5RatioHeight.lean, lines 8-14, SHA-256 caf61348fb66d8b422dc583b23aa54e12391df9c8ee1e7521aa8bfee1537daef; D1Bound5/FiniteA5RatioHeight.lean, lines 16-16, SHA-256 caf61348fb66d8b422dc583b23aa54e12391df9c8ee1e7521aa8bfee1537daef. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FiniteA5Coefficients_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousRatio_Definitions

section
noncomputable section

namespace D1Bound5

def finiteA5RatioWeights (r : ℝ) (i : Fin 3) : Fin 6 → ℝ :=
  ![finiteHomogeneousRatioWeight 7 (finiteA5Coeff0 i 0) r+finiteHomogeneousRatioWeight 7 (finiteA5Coeff0 i 1) r,
    finiteHomogeneousRatioWeight 8 (finiteA5Coeff1 i 0) r+finiteHomogeneousRatioWeight 8 (finiteA5Coeff1 i 1) r,
    finiteHomogeneousRatioWeight 9 (finiteA5Coeff2 i 0) r+finiteHomogeneousRatioWeight 9 (finiteA5Coeff2 i 1) r,
    finiteHomogeneousRatioWeight 10 (finiteA5Coeff3 i 0) r+finiteHomogeneousRatioWeight 10 (finiteA5Coeff3 i 1) r,
    finiteHomogeneousRatioWeight 11 (finiteA5Coeff4 i 0) r+finiteHomogeneousRatioWeight 11 (finiteA5Coeff4 i 1) r,
    finiteHomogeneousRatioWeight 12 (finiteA5Coeff5 i 0) r+finiteHomogeneousRatioWeight 12 (finiteA5Coeff5 i 1) r]

def fiveRegionA5Height : Fin 5 → ℝ := ![38390,171856,482131,701908,2400382]









end D1Bound5
end


