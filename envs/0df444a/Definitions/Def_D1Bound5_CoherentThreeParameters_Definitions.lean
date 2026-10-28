-- Prove2me | Definitions.Def_D1Bound5_CoherentThreeParameters_Definitions
-- name    : D1Bound5_CoherentThreeParameters_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:25:07.980851+00:00
-- url     : https://prove2.me/theorems/4a012986-df44-4ea4-b481-e0f3167e72da
-- title:
--   Coherent Three Parameters
-- statement:
--   Definitions for coherent three parameters in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `coherentThreeTailConstant`, `coherentThreeLowerConstant`, `coherentThreeUpperConstant`.
-- source:
--   D1Bound5/CoherentThreeParameters.lean, lines 10-11, SHA-256 ca0fac013bc4ef76939f023e46143eabcee36be640a6d47b13f0373264757949; D1Bound5/CoherentThreeParameters.lean, lines 13-14, SHA-256 ca0fac013bc4ef76939f023e46143eabcee36be640a6d47b13f0373264757949; D1Bound5/CoherentThreeParameters.lean, lines 16-17, SHA-256 ca0fac013bc4ef76939f023e46143eabcee36be640a6d47b13f0373264757949. Project: https://github.com/tomislav-math/d1-bound5-lean

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

def coherentThreeTailConstant (H : ℝ) : ℝ :=
  (5/32 : ℝ) * ((H/(H-1))^3-1)

def coherentThreeLowerConstant (H : ℝ) : ℝ :=
  (45/1024 : ℝ) - coherentThreeTailConstant H

def coherentThreeUpperConstant (H : ℝ) : ℝ :=
  (85/1024 : ℝ) + coherentThreeTailConstant H











end D1Bound5
end


