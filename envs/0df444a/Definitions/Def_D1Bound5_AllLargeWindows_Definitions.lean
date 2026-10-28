-- Prove2me | Definitions.Def_D1Bound5_AllLargeWindows_Definitions
-- name    : D1Bound5_AllLargeWindows_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:23:31.732097+00:00
-- url     : https://prove2.me/theorems/df973467-0bf0-41e8-8145-2f99a850772b
-- title:
--   All Large Windows
-- statement:
--   The actual closed endpoints used in the all-large branch. Every family receives its analytic exclusion in the final tuple assembly. The named objects in this bundle include `allLargeWindowQ`, `allLargeWindowN2`, `allLargeWindowP`, `allLargeWindowA3`, `allLargeWindowM`, `allLargeWindowN3`, `allLargeWindowA4`, `allLargeWindowA5`.
-- source:
--   D1Bound5/AllLargeWindows.lean, lines 5-8, SHA-256 8a55028f795f579ca9d48bce231b9a089c1b85f46e7e028019c12a2849cb716c; D1Bound5/AllLargeWindows.lean, lines 10-11, SHA-256 8a55028f795f579ca9d48bce231b9a089c1b85f46e7e028019c12a2849cb716c; D1Bound5/AllLargeWindows.lean, lines 13-15, SHA-256 8a55028f795f579ca9d48bce231b9a089c1b85f46e7e028019c12a2849cb716c; D1Bound5/AllLargeWindows.lean, lines 17-18, SHA-256 8a55028f795f579ca9d48bce231b9a089c1b85f46e7e028019c12a2849cb716c; D1Bound5/AllLargeWindows.lean, lines 20-22, SHA-256 8a55028f795f579ca9d48bce231b9a089c1b85f46e7e028019c12a2849cb716c; D1Bound5/AllLargeWindows.lean, lines 24-26, SHA-256 8a55028f795f579ca9d48bce231b9a089c1b85f46e7e028019c12a2849cb716c; D1Bound5/AllLargeWindows.lean, lines 28-30, SHA-256 8a55028f795f579ca9d48bce231b9a089c1b85f46e7e028019c12a2849cb716c; D1Bound5/AllLargeWindows.lean, lines 32-34, SHA-256 8a55028f795f579ca9d48bce231b9a089c1b85f46e7e028019c12a2849cb716c. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Data.Int.GCD
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order

section
namespace D1Bound5

/-- The actual closed endpoints used in the all-large branch. Every
family receives its analytic exclusion in the final tuple assembly. -/
noncomputable def allLargeWindowQ (A T C : ℝ) : ℝ × ℝ :=
  (4*55^2*T^6*C^3/(1-1/4000 : ℝ), A^4*C^7/(9*T^2*(1+1/4000 : ℝ)))

noncomputable def allLargeWindowN2 (A B C : ℝ) : ℝ × ℝ :=
  (4*243^2*B^8*C^5/(1-1/4000 : ℝ), 4*A^6*C^7/(25*B^4*(1+1/4000 : ℝ)))

noncomputable def allLargeWindowP (A B S C : ℝ) : ℝ × ℝ :=
  (4*2400^2*(max (B*S^3) (B^3*S^2))^2*C^5/(1-1/4000 : ℝ),
    A^6*C^9/(36*S^4*(1+1/4000 : ℝ)))

noncomputable def allLargeWindowA3 (A B C : ℝ) : ℝ × ℝ :=
  (4*2265^2*B^12*C^7/(1-1/4000 : ℝ), 64*A^8*C^9/(1225*B^6*(1+1/4000 : ℝ)))

noncomputable def allLargeWindowM (A B S C : ℝ) : ℝ × ℝ :=
  (4*((8/9 : ℝ)*608^2)^2*B^6*S^16*C^5/(1-1/4000 : ℝ),
    A^6*C^11/(4*(3920/81 : ℝ)^2*B^4*S^10*(1+1/4000 : ℝ)))

noncomputable def allLargeWindowN3 (A B C : ℝ) : ℝ × ℝ :=
  (4*4143^2*B^14*C^7/(1-1/4000 : ℝ),
    256*A^8*C^11/(1225*B^6*(1+1/4000 : ℝ)))

noncomputable def allLargeWindowA4 (A B C : ℝ) : ℝ × ℝ :=
  (4*165763^2*B^18*C^9/(1-1/4000 : ℝ),
    16*A^10*C^13/(3969*B^8*(1+1/4000 : ℝ)))

noncomputable def allLargeWindowA5 (A B C : ℝ) : ℝ × ℝ :=
  (4*3113013^2*B^24*C^11/(1-1/4000 : ℝ),
    1024*A^12*C^17/(245025*B^10*(1+1/4000 : ℝ)))





end D1Bound5
end


