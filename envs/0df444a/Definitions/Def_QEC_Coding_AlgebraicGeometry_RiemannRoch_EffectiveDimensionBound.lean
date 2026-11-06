-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_EffectiveDimensionBound
-- name    : QEC_Coding_AlgebraicGeometry_RiemannRoch_EffectiveDimensionBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:54:33.026209+00:00
-- url     : https://prove2.me/theorems/437e405b-c43c-4288-a3e9-56638ac6f1d4
-- title:
--   Effective Dimension Bound
-- statement:
--   Definitions and structural lemmas for Effective Dimension Bound, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/EffectiveDimensionBound.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Constants
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_EffectiveIncrement
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
noncomputable local instance riemannRochEffectiveDimensionBoundAlgebra :
    Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π
local instance riemannRochEffectiveDimensionBoundScalarTower :
    IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
namespace GlobalPlace
local instance riemannRochEffectiveDimensionBoundFiniteDimensional
    (G : Divisor (GlobalPlace k F)) :
    FiniteDimensional k (riemannRochSubmodule G) :=
  finiteDimensional_riemannRochSubmodule
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry


