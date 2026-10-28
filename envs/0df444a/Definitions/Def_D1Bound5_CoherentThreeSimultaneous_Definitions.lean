-- Prove2me | Definitions.Def_D1Bound5_CoherentThreeSimultaneous_Definitions
-- name    : D1Bound5_CoherentThreeSimultaneous_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:54:14.160976+00:00
-- url     : https://prove2.me/theorems/b9a6fb5a-60e8-4959-9a2f-dc623ed335d5
-- title:
--   Coherent Three Simultaneous
-- statement:
--   Definitions for coherent three simultaneous in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `coherentElementary2`, `coherentElementary3`, `coherentElementary4`.
-- source:
--   D1Bound5/CoherentThreeSimultaneous.lean, lines 9-11, SHA-256 ee201a480813e6432c988412c0b0b54c06b4815f872ad14ff04a828a0dbc941f; D1Bound5/CoherentThreeSimultaneous.lean, lines 13-15, SHA-256 ee201a480813e6432c988412c0b0b54c06b4815f872ad14ff04a828a0dbc941f; D1Bound5/CoherentThreeSimultaneous.lean, lines 17-18, SHA-256 ee201a480813e6432c988412c0b0b54c06b4815f872ad14ff04a828a0dbc941f. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
open Finset Polynomial

namespace D1Bound5

def coherentElementary2 {F : Type*} [CommRing F] (a : Fin 4 → F) : F :=
  a 0 * a 1 + a 0 * a 2 + a 0 * a 3 +
    a 1 * a 2 + a 1 * a 3 + a 2 * a 3

def coherentElementary3 {F : Type*} [CommRing F] (a : Fin 4 → F) : F :=
  a 0 * a 1 * a 2 + a 0 * a 1 * a 3 +
    a 0 * a 2 * a 3 + a 1 * a 2 * a 3

def coherentElementary4 {F : Type*} [CommRing F] (a : Fin 4 → F) : F :=
  a 0 * a 1 * a 2 * a 3











end D1Bound5
end


