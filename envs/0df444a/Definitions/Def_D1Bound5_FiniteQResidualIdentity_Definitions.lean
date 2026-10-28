-- Prove2me | Definitions.Def_D1Bound5_FiniteQResidualIdentity_Definitions
-- name    : D1Bound5_FiniteQResidualIdentity_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:33:00.322989+00:00
-- url     : https://prove2.me/theorems/63342441-754c-41d8-bb80-f11d00a40261
-- title:
--   Finite QResidual Identity
-- statement:
--   The remainder of the actual principal half power after n terms. The named objects in this bundle include `finiteQHalfRemainder`, `finiteQResidual`.
-- source:
--   D1Bound5/FiniteQResidualIdentity.lean, lines 30-32, SHA-256 74ab040376af9b42e7ee62656f2fd8f3a92a0111248e8b31465d43a74a137c58; D1Bound5/FiniteQResidualIdentity.lean, lines 73-77, SHA-256 74ab040376af9b42e7ee62656f2fd8f3a92a0111248e8b31465d43a74a137c58. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteQMatrix_Definitions
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions

section
open Finset

namespace D1Bound5



/-- The remainder of the actual principal half power after n terms. -/
noncomputable def finiteQHalfRemainder (n : ℕ) (z : ℂ) : ℂ :=
  (1+z)^(1/2 : ℂ) - ∑ m ∈ Finset.range n, (halfBinomialCoeff m : ℂ)*z^m



/-- The residual of the actual finite pair row on its two principal
half-power branches. -/
noncomputable def finiteQResidual (u v c : ℂ) : ℂ :=
  finiteQConstant u v c + u*finiteQLeft u v c*((1+1/(u*c))^(1/2 : ℂ)) +
    v*finiteQRight u v c*((1+1/(v*c))^(1/2 : ℂ))



end D1Bound5
end


