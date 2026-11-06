-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Theorem
-- name    : QEC_Coding_AlgebraicGeometry_RiemannRoch_Theorem
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:52:05.795836+00:00
-- url     : https://prove2.me/theorems/e3e50f74-72e5-4f95-bdfa-3ecf09f100cb
-- title:
--   Theorem
-- statement:
--   Definitions and structural lemmas for Theorem, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Theorem.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialDuality
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
noncomputable local instance riemannRochTheoremAlgebra : Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π
local instance riemannRochTheoremScalarTower :
    IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
local instance riemannRochTheoremFiniteDimensional
    (G : Divisor (GlobalPlace k F)) :
    FiniteDimensional k (GlobalPlace.riemannRochSubmodule G) :=
  GlobalPlace.finiteDimensional_riemannRochSubmodule
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G
variable [IsFullConstantField k F]
namespace GlobalPlace
end GlobalPlace
namespace CanonicalDivisor
end CanonicalDivisor
namespace GlobalPlace
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry


