-- Prove2me | Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions
-- name    : D1Bound5_HalfBinomialCoefficients_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:32:39.967981+00:00
-- url     : https://prove2.me/theorems/66d1dffd-2a0d-48c2-9a03-20572cb8c3f7
-- title:
--   Half Binomial Coefficients
-- statement:
--   The real Taylor coefficient of `sqrt (1+z)` at degree `n`. The named objects in this bundle include `halfBinomialCoeff`.
-- source:
--   D1Bound5/HalfBinomialCoefficients.lean, lines 9-11, SHA-256 97b0412384b100b3ac306cb8297135156f099ce2af7ece88037027b2b15bd23b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

section
open Finset

namespace D1Bound5

/-- The real Taylor coefficient of `sqrt (1+z)` at degree `n`. -/
noncomputable def halfBinomialCoeff (n : ℕ) : ℝ :=
  Ring.choose (1 / 2 : ℝ) n















end D1Bound5
end


