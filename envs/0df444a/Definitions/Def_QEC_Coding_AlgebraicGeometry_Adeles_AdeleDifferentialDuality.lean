-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialDuality
-- name    : QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialDuality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:48:08.026679+00:00
-- url     : https://prove2.me/theorems/f2660c14-caa8-42f8-bcd9-8df2279d28ad
-- title:
--   Adele Differential Duality
-- statement:
--   Definitions and structural lemmas for Adele Differential Duality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Adeles/AdeleDifferentialDuality.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialWeil
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finiteDimensional_riemannRochSubmodule

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
noncomputable local instance globalAdeleDifferentialDualityAlgebra :
    Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π
attribute [local instance] globalAdeleDifferentialDualityAlgebra
local instance globalAdeleDifferentialDualityScalarTower :
    IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
attribute [local instance] globalAdeleDifferentialDualityScalarTower
namespace GlobalPlace
variable [IsFullConstantField k F]
local instance globalAdeleDifferentialDualityRiemannRochFiniteDimensional
    (D : Divisor (GlobalPlace k F)) :
    FiniteDimensional k (riemannRochSubmodule D) :=
  finiteDimensional_riemannRochSubmodule
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D
attribute [local instance] globalAdeleDifferentialDualityRiemannRochFiniteDimensional
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry


