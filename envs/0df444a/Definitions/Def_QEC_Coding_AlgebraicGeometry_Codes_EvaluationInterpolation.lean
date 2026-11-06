-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationInterpolation
-- name    : QEC_Coding_AlgebraicGeometry_Codes_EvaluationInterpolation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:53:39.966137+00:00
-- url     : https://prove2.me/theorems/e9f91271-a069-4d42-a416-87260cfab9e3
-- title:
--   Evaluation Interpolation
-- statement:
--   Definitions and structural lemmas for Evaluation Interpolation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/EvaluationInterpolation.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationKernel
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Theorem
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finiteDimensional_riemannRochSubmodule

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
variable (k F : Type*) [Field k] [Fintype k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
local instance interpolationConstantAlgebra : Algebra k F := AffinePlace.constantAlgebra k F
local instance interpolationConstantTower : IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
local instance interpolationFiniteDimensional (G : Divisor (GlobalPlace k F)) :
    FiniteDimensional k (GlobalPlace.riemannRochSubmodule G) :=
  GlobalPlace.finiteDimensional_riemannRochSubmodule
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G
variable [IsFullConstantField k F] {ι : Type*} [Fintype ι]
end
end QEC.Coding.AlgebraicGeometry


