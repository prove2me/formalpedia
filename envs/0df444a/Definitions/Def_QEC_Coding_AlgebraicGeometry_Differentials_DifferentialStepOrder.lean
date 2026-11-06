-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialStepOrder
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_DifferentialStepOrder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:41:09.387445+00:00
-- url     : https://prove2.me/theorems/f5b54286-c6b3-41e0-8edf-ffe9f4072d01
-- title:
--   Differential Step Order
-- statement:
--   Definitions and structural lemmas for Differential Step Order, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/DifferentialStepOrder.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ParameterDifferentialOrder
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
noncomputable section
variable {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [Algebra (RatFunc k) L]
    [IsScalarTower k (RatFunc k) K] [IsScalarTower k (RatFunc k) L]
    [IsScalarTower (RatFunc k) K L]
    [Algebra.IsSeparable (RatFunc k) K] [Algebra.IsSeparable (RatFunc k) L]
    [FiniteDimensional (RatFunc k) K] [FiniteDimensional (RatFunc k) L]
end
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential


