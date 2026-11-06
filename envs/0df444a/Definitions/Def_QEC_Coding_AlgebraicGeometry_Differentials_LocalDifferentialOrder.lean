-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalDifferentialOrder
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_LocalDifferentialOrder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:23:32.405205+00:00
-- url     : https://prove2.me/theorems/8c7a1b6e-20a6-4f4e-ad19-ba95c87133ec
-- title:
--   Local Differential Order
-- statement:
--   Definitions and structural lemmas for Local Differential Order, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/LocalDifferentialOrder.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalUniformizerDerivative
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
namespace Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
end Differential
end QEC.Coding.AlgebraicGeometry


