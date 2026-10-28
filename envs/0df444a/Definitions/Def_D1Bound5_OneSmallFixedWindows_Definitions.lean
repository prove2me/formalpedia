-- Prove2me | Definitions.Def_D1Bound5_OneSmallFixedWindows_Definitions
-- name    : D1Bound5_OneSmallFixedWindows_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:19:58.28181+00:00
-- url     : https://prove2.me/theorems/fbd0ff8e-e99b-4bd5-8b2a-48e9980e9043
-- title:
--   One Small Fixed Windows
-- statement:
--   Definitions for one small fixed windows in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `fixedWindowN2`, `fixedWindowP`, `fixedWindowA3`, `fixedWindowN3`, `fixedWindowN3bs`, `fixedWindowA4`, `fixedWindowA5`.
-- source:
--   D1Bound5/OneSmallFixedWindows.lean, lines 6-7, SHA-256 a89b44c2f3bb4ff79203e5d94458daa63b872e293c34f760393d0338cb4694eb; D1Bound5/OneSmallFixedWindows.lean, lines 8-10, SHA-256 a89b44c2f3bb4ff79203e5d94458daa63b872e293c34f760393d0338cb4694eb; D1Bound5/OneSmallFixedWindows.lean, lines 11-12, SHA-256 a89b44c2f3bb4ff79203e5d94458daa63b872e293c34f760393d0338cb4694eb; D1Bound5/OneSmallFixedWindows.lean, lines 13-14, SHA-256 a89b44c2f3bb4ff79203e5d94458daa63b872e293c34f760393d0338cb4694eb; D1Bound5/OneSmallFixedWindows.lean, lines 15-17, SHA-256 a89b44c2f3bb4ff79203e5d94458daa63b872e293c34f760393d0338cb4694eb; D1Bound5/OneSmallFixedWindows.lean, lines 18-19, SHA-256 a89b44c2f3bb4ff79203e5d94458daa63b872e293c34f760393d0338cb4694eb; D1Bound5/OneSmallFixedWindows.lean, lines 20-21, SHA-256 a89b44c2f3bb4ff79203e5d94458daa63b872e293c34f760393d0338cb4694eb. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001

section
namespace D1Bound5

noncomputable def fixedWindowN2 (r : OneSmallCutoffRow) (B C : ℝ) : ℝ × ℝ :=
  (4*(r.M2 : ℝ)^2*B^8*C^5/(1-1/4000 : ℝ), C^7/(4*(r.R2 : ℝ)^2*B^4*(1+1/4000 : ℝ)))
noncomputable def fixedWindowP (r : OneSmallCutoffRow) (B S C : ℝ) : ℝ × ℝ :=
  (4*2400^2*(max (B*S^3) (B^3*S^2))^2*C^5/(1-1/4000 : ℝ),
    C^9/(4*(r.Rp : ℝ)^2*S^4*(1+1/4000 : ℝ)))
noncomputable def fixedWindowA3 (r : OneSmallCutoffRow) (B C : ℝ) : ℝ × ℝ :=
  (4*(r.M3 : ℝ)^2*B^12*C^7/(1-1/4000 : ℝ), C^9/(4*(r.R3 : ℝ)^2*B^6*(1+1/4000 : ℝ)))
noncomputable def fixedWindowN3 (r : OneSmallCutoffRow) (B C : ℝ) : ℝ × ℝ :=
  (4*(r.Mn : ℝ)^2*B^14*C^7/(1-1/4000 : ℝ), C^11/(4*(r.Rn : ℝ)^2*B^6*(1+1/4000 : ℝ)))
noncomputable def fixedWindowN3bs (r : OneSmallCutoffRow) (B S C : ℝ) : ℝ × ℝ :=
  (4*(r.Mbs : ℝ)^2*S^14*C^7/(1-1/4000 : ℝ),
    B^8*C^11/(4*(r.Rbs : ℝ)^2*S^6*(1+1/4000 : ℝ)))
noncomputable def fixedWindowA4 (r : OneSmallCutoffRow) (B C : ℝ) : ℝ × ℝ :=
  (4*(r.M4 : ℝ)^2*B^18*C^9/(1-1/4000 : ℝ), C^13/(4*(r.R4 : ℝ)^2*B^8*(1+1/4000 : ℝ)))
noncomputable def fixedWindowA5 (r : OneSmallCutoffRow) (B C : ℝ) : ℝ × ℝ :=
  (4*(r.M5 : ℝ)^2*B^24*C^11/(1-1/4000 : ℝ), C^17/(4*(r.R5 : ℝ)^2*B^10*(1+1/4000 : ℝ)))





end D1Bound5
end


