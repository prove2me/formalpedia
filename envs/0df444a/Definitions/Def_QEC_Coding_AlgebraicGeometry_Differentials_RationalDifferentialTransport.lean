-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RationalDifferentialTransport
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_RationalDifferentialTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:41:13.884255+00:00
-- url     : https://prove2.me/theorems/71358447-a771-440e-92a8-a4a5a2747f48
-- title:
--   Rational Differential Transport
-- statement:
--   Definitions and structural lemmas for Rational Differential Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/RationalDifferentialTransport.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ParameterDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
noncomputable section
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [Algebra.IsSeparable (RatFunc k) K] [FiniteDimensional (RatFunc k) K]
variable [Finite k]
end
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential


