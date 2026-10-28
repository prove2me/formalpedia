-- Prove2me | Definitions.Def_D1Bound5_CoherentFormBounds_Definitions
-- name    : D1Bound5_CoherentFormBounds_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:11:12.330992+00:00
-- url     : https://prove2.me/theorems/a27c47e3-b2ed-4bcd-912f-612a8afc7168
-- title:
--   Coherent Form Bounds
-- statement:
--   The complete homogeneous remainder for the actual reciprocal terminal parameters. The finite-subtype indexing matches the proved Lagrange interpolation theorem exactly. The named objects in this bundle include `coherentRemainder`.
-- source:
--   D1Bound5/CoherentFormBounds.lean, lines 8-14, SHA-256 c03d23c1aa78f01b328715b302c1ec28dd87b243d972f665963735dee00e4981. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_ComplexHalfBinomial_Definitions

section
open Finset

namespace D1Bound5

/-- The complete homogeneous remainder for the actual reciprocal
terminal parameters.  The finite-subtype indexing matches the proved
Lagrange interpolation theorem exactly. -/
noncomputable def coherentRemainder {m : ℕ} (a : Fin m → ℂ) (p q : ℂ) : ℂ :=
  ∑' j : ℕ, halfBinomialWeightedCoeff p⁻¹ q⁻¹ (m + j) *
    MvPolynomial.aeval (fun i : (Finset.univ : Finset (Fin m)) => (a i)⁻¹)
      (MvPolynomial.hsymm (Finset.univ : Finset (Fin m)) ℂ j)







end D1Bound5
end


