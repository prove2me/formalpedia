-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_ConstantFieldTransport
-- name    : QEC_Coding_AlgebraicGeometry_Codes_ConstantFieldTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:15:34.73481+00:00
-- url     : https://prove2.me/theorems/4eec28bf-e5f0-4345-8ffa-df8d6b081257
-- title:
--   Constant Field Transport
-- statement:
--   Definitions and structural lemmas for Constant Field Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/ConstantFieldTransport.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_CodeDuality
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_ResiduePairing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationInterpolation
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
variable (k F : Type*) [Field k] [Fintype k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
variable [κ : Algebra k F]
variable [@IsFullConstantField k F _ _ (@AffinePlace.constantAlgebra k F _ _ π)]
variable {ι : Type*} [Fintype ι]
end
end QEC.Coding.AlgebraicGeometry


