-- Prove2me | Definitions.Def_D1Bound5_CoherentFourParameters_Definitions
-- name    : D1Bound5_CoherentFourParameters_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:11:03.721625+00:00
-- url     : https://prove2.me/theorems/0b77630e-49fd-4768-bd05-86ccc4976d29
-- title:
--   Coherent Four Parameters
-- statement:
--   Definitions for coherent four parameters in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `coherentFourLeadingLower`, `coherentFourLeadingUpper`, `coherentFourTailConstant`, `coherentFourLowerConstant`, `coherentFourUpperConstant`.
-- source:
--   D1Bound5/CoherentFourParameters.lean, lines 9-10, SHA-256 2e9b9910fdc9ab9d971f73968ff3041629e55002234f11342512ba505d011e8a; D1Bound5/CoherentFourParameters.lean, lines 12-13, SHA-256 2e9b9910fdc9ab9d971f73968ff3041629e55002234f11342512ba505d011e8a; D1Bound5/CoherentFourParameters.lean, lines 15-15, SHA-256 2e9b9910fdc9ab9d971f73968ff3041629e55002234f11342512ba505d011e8a; D1Bound5/CoherentFourParameters.lean, lines 17-17, SHA-256 2e9b9910fdc9ab9d971f73968ff3041629e55002234f11342512ba505d011e8a; D1Bound5/CoherentFourParameters.lean, lines 19-19, SHA-256 2e9b9910fdc9ab9d971f73968ff3041629e55002234f11342512ba505d011e8a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
open Finset

noncomputable section

namespace D1Bound5

def coherentFourLeadingLower : ℝ :=
  (1-1/1000)^2*(5-6/1000-5/(1000:ℝ)^2)/128

def coherentFourLeadingUpper : ℝ :=
  (1+1/1000)^2*(5+6/1000+5/(1000:ℝ)^2)/128

def coherentFourTailConstant : ℝ := (7/64 : ℝ)*((1000/999 : ℝ)^4-1)

def coherentFourLowerConstant : ℝ := coherentFourLeadingLower-coherentFourTailConstant

def coherentFourUpperConstant : ℝ := coherentFourLeadingUpper+coherentFourTailConstant









end D1Bound5
end


