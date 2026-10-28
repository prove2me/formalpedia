-- Prove2me | Definitions.Def_D1Bound5_CoherentThreeNonvanishing_Definitions
-- name    : D1Bound5_CoherentThreeNonvanishing_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:24:28.948863+00:00
-- url     : https://prove2.me/theorems/7086665e-ffe7-4ddc-aa89-40b30b3d5893
-- title:
--   Coherent Three Nonvanishing
-- statement:
--   Definitions for coherent three nonvanishing in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `coherentTriple012`, `coherentTriple013`.
-- source:
--   D1Bound5/CoherentThreeNonvanishing.lean, lines 165-166, SHA-256 20f76d470fd8a77be69b6cbe7c960d5062bc8bb2410754eb1f27bcf0090be809; D1Bound5/CoherentThreeNonvanishing.lean, lines 168-169, SHA-256 20f76d470fd8a77be69b6cbe7c960d5062bc8bb2410754eb1f27bcf0090be809. Project: https://github.com/tomislav-math/d1-bound5-lean

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
open Finset

namespace D1Bound5









def coherentTriple012 {F : Type*} (a : Fin 4 → F) : Fin 3 → F :=
  fun i => a (![0,1,2] i)

def coherentTriple013 {F : Type*} (a : Fin 4 → F) : Fin 3 → F :=
  fun i => a (![0,1,3] i)



end D1Bound5
end


