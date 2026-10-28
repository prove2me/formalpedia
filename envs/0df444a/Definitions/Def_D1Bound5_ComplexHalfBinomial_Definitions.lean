-- Prove2me | Definitions.Def_D1Bound5_ComplexHalfBinomial_Definitions
-- name    : D1Bound5_ComplexHalfBinomial_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:33:00.168595+00:00
-- url     : https://prove2.me/theorems/09c6627a-badd-4db1-a447-42f881e3df45
-- title:
--   Complex Half Binomial
-- statement:
--   The degree-n coefficient in the product of the two formal half-binomial series with complex variables x and y. The named objects in this bundle include `halfBinomialWeightedCoeff`.
-- source:
--   D1Bound5/ComplexHalfBinomial.lean, lines 9-14, SHA-256 e7e6f8b11a6f554af427f9bfa36df35a8240f67bed0729f2ba7396a3dc39d624. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions

section
open Finset

namespace D1Bound5

/-- The degree-n coefficient in the product of the two formal half-binomial
series with complex variables x and y. -/
noncomputable def halfBinomialWeightedCoeff (x y : ℂ) (n : ℕ) : ℂ :=
  ∑ ij ∈ Finset.antidiagonal n,
    ((halfBinomialCoeff ij.1 * halfBinomialCoeff ij.2 : ℝ) : ℂ) *
      x ^ ij.1 * y ^ ij.2







end D1Bound5
end


