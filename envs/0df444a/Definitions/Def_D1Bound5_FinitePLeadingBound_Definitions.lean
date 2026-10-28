-- Prove2me | Definitions.Def_D1Bound5_FinitePLeadingBound_Definitions
-- name    : D1Bound5_FinitePLeadingBound_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:24:27.464209+00:00
-- url     : https://prove2.me/theorems/eb076d0a-ea51-4553-8b28-9213b2c2e87f
-- title:
--   Finite PLeading Bound
-- statement:
--   Coefficient, denominator anchor, numerator anchor, numerator exponent, and denominator exponent; a common denominator256 is outside the sum. The named objects in this bundle include `FinitePLeadingTerm`, `finitePLeadingTerms`, `finitePLeadingTermValue`.
-- source:
--   D1Bound5/FinitePLeadingBound.lean, lines 10-12, SHA-256 237162555cf7aab44715f5fa900788556d3bb32195d23d9b5b35cca9462a87fc; D1Bound5/FinitePLeadingBound.lean, lines 14-26, SHA-256 237162555cf7aab44715f5fa900788556d3bb32195d23d9b5b35cca9462a87fc; D1Bound5/FinitePLeadingBound.lean, lines 28-30, SHA-256 237162555cf7aab44715f5fa900788556d3bb32195d23d9b5b35cca9462a87fc. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open Finset

namespace D1Bound5

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

/-- Coefficient, denominator anchor, numerator anchor, numerator exponent,
and denominator exponent; a common denominator256 is outside the sum. -/
abbrev FinitePLeadingTerm := ℤ × Fin 3 × Fin 3 × ℕ × ℕ

def finitePLeadingTerms : Fin 4 → Fin 12 → FinitePLeadingTerm :=
  ![![(10,0,0,0,2),(-10,1,1,0,2),(5,1,0,1,3),(-5,0,1,1,3),
      (0,0,0,0,1),(0,0,0,0,1),(0,0,0,0,1),(0,0,0,0,1),
      (0,0,0,0,1),(0,0,0,0,1),(0,0,0,0,1),(0,0,0,0,1)],
    ![(10,0,0,0,2),(-10,1,1,0,2),(5,1,0,1,3),(-5,0,1,1,3),
      (10,1,1,0,2),(-10,2,2,0,2),(5,2,1,1,3),(-5,1,2,1,3),
      (-10,0,0,0,2),(10,2,2,0,2),(-5,2,0,1,3),(5,0,2,1,3)],
    ![(-150,0,0,0,1),(80,0,1,1,2),(-15,0,1,2,3),(-35,1,0,1,2),
      (120,1,1,0,1),(0,0,0,0,1),(0,0,0,0,1),(0,0,0,0,1),
      (0,0,0,0,1),(0,0,0,0,1),(0,0,0,0,1),(0,0,0,0,1)],
    ![(-150,0,0,0,1),(80,0,2,1,2),(-15,0,2,2,3),(-35,2,0,1,2),
      (150,1,1,0,1),(-80,1,2,1,2),(15,1,2,2,3),(35,2,1,1,2),
      (0,0,0,0,1),(0,0,0,0,1),(0,0,0,0,1),(0,0,0,0,1)]]

noncomputable def finitePLeadingTermValue (x : Fin 3 → ℂ)
    (t : FinitePLeadingTerm) : ℂ :=
  (t.1 : ℂ)*(x t.2.2.1)^t.2.2.2.1/(x t.2.1)^t.2.2.2.2









end D1Bound5
end


