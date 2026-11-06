-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalUniformizerDerivative
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_LocalUniformizerDerivative
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:22:39.677357+00:00
-- url     : https://prove2.me/theorems/774f4f99-2823-4037-8777-7ae01815e181
-- title:
--   Local Uniformizer Derivative
-- statement:
--   Definitions and structural lemmas for Local Uniformizer Derivative, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/LocalUniformizerDerivative.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalLogarithmicDifferential
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
namespace FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
end FunctionFieldDifferential
namespace Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
end Differential
end QEC.Coding.AlgebraicGeometry


