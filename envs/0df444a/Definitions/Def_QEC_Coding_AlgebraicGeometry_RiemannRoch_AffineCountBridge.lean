-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_AffineCountBridge
-- name    : QEC_Coding_AlgebraicGeometry_RiemannRoch_AffineCountBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:11:43.004822+00:00
-- url     : https://prove2.me/theorems/75ee6b2b-a350-48d6-afc9-4d9d88672511
-- title:
--   Affine Count Bridge
-- statement:
--   Definitions and structural lemmas for Affine Count Bridge, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/AffineCountBridge.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero nonZeroDivisors
namespace AffinePlace
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
noncomputable local instance _p2m_local_instance_45ffe40864_30 : Algebra k F := constantAlgebra k F
abbrev affineRing : Type _ := _root_.FunctionField.ringOfIntegers k F
abbrev affineFractionalIdeal : Type _ :=
  FractionalIdeal (affineRing k F)⁰ F
noncomputable def chartFractionalLattice (D : Divisor (carrier k F)) :
    affineFractionalIdeal k F :=
  (-D).prod (fun P exponent => (P.asIdeal : affineFractionalIdeal k F) ^ exponent)
end AffinePlace
end QEC.Coding.AlgebraicGeometry


