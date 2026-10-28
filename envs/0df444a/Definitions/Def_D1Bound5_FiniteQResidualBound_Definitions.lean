-- Prove2me | Definitions.Def_D1Bound5_FiniteQResidualBound_Definitions
-- name    : D1Bound5_FiniteQResidualBound_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T00:42:24.093934+00:00
-- url     : https://prove2.me/theorems/4bcf766f-5a86-420d-afb8-a4fc9aea1902
-- title:
--   Finite QResidual Bound
-- statement:
--   Definitions for finite qresidual bound in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `finiteQTailSide`.
-- source:
--   D1Bound5/FiniteQResidualBound.lean, lines 15-17, SHA-256 a3e6f379d6e8b22749f6d6447d2c163488ae6d9c3b3948f32b3749f0bb7a7bac. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteQResidualIdentity_Definitions

section
namespace D1Bound5



noncomputable def finiteQTailSide (u v c : ℂ) : ℂ :=
  u*(u^2-5*u*v)*finiteQHalfRemainder 4 (1/(u*c)) +
    u*(4*u^3-8*u^2*v)*c*finiteQHalfRemainder 5 (1/(u*c))





end D1Bound5
end


