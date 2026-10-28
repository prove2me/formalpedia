-- Prove2me | Definitions.Def_D1Bound5_FinitePAdaptiveTailBound_Definitions
-- name    : D1Bound5_FinitePAdaptiveTailBound_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T01:31:57.37402+00:00
-- url     : https://prove2.me/theorems/4170db48-d3cc-4cf3-8012-2498f41fd5e0
-- title:
--   Finite PAdaptive Tail Bound
-- statement:
--   Definitions for finite padaptive tail bound in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `finitePAdaptiveTailCoeffWeight`.
-- source:
--   D1Bound5/FinitePAdaptiveTailBound.lean, lines 6-8, SHA-256 e82a8b4b2fb104b1a8e9ee85e59a9053010935a948dafdd2ad97b98bd358afae. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePAdaptiveTailData_Definitions
import Definitions.Def_D1Bound5_FinitePHeight_Definitions

section
namespace D1Bound5

noncomputable def finitePAdaptiveTailCoeffWeight (i : Fin 4) (l j : Fin 3) (x : ℝ) : ℝ :=
  ∑ t : Fin 3, |((finitePRootTerms i l j t).1 : ℝ)| *
    x^(finitePAdaptiveTailExponent i l j t)







end D1Bound5
end


