-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_EffectiveIncrement
-- name    : QEC_Coding_AlgebraicGeometry_RiemannRoch_EffectiveIncrement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:53:16.919195+00:00
-- url     : https://prove2.me/theorems/46a2b52e-e0a7-4c3f-8651-87c0fc19d0fa
-- title:
--   Effective Increment
-- statement:
--   Definitions and structural lemmas for Effective Increment, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/EffectiveIncrement.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrementDimension
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finiteDimensional_riemannRochSubmodule

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
noncomputable local instance riemannRochEffectiveIncrementAlgebra : Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π
attribute [local instance] riemannRochEffectiveIncrementAlgebra
local instance riemannRochEffectiveIncrementScalarTower :
    IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
attribute [local instance] riemannRochEffectiveIncrementScalarTower
namespace GlobalPlace
local instance finiteDimensionalRiemannRochSubmodule
    (G : Divisor (GlobalPlace k F)) :
    FiniteDimensional k (riemannRochSubmodule G) :=
  finiteDimensional_riemannRochSubmodule
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G
attribute [local instance] finiteDimensionalRiemannRochSubmodule
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry


