-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_NegativeDegreeVanishing
-- name    : QEC_Coding_AlgebraicGeometry_RiemannRoch_NegativeDegreeVanishing
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:20:36.779198+00:00
-- url     : https://prove2.me/theorems/c1dd06df-c804-4578-a758-273218e37673
-- title:
--   Negative Degree Vanishing
-- statement:
--   Definitions and structural lemmas for Negative Degree Vanishing, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/NegativeDegreeVanishing.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Space
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
variable [Algebra k F]
end QEC.Coding.AlgebraicGeometry


