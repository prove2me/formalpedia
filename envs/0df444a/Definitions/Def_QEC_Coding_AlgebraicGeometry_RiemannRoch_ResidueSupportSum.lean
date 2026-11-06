-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_ResidueSupportSum
-- name    : QEC_Coding_AlgebraicGeometry_RiemannRoch_ResidueSupportSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:38:54.311993+00:00
-- url     : https://prove2.me/theorems/f83645f6-36bc-4bed-86fa-970640be6051
-- title:
--   Residue Support Sum
-- statement:
--   Definitions and structural lemmas for Residue Support Sum, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/ResidueSupportSum.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_ResidueProduct
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
namespace Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
end Differential
end QEC.Coding.AlgebraicGeometry


