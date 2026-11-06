-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarFamily
-- name    : QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarFamily
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:56:06.003667+00:00
-- url     : https://prove2.me/theorems/5f0ec565-bc40-41a1-8212-f90a56971572
-- title:
--   Polar Family
-- statement:
--   Definitions and structural lemmas for Polar Family, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/PolarFamily.lean

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_EffectiveDimensionBound
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finiteDimensional_riemannRochSubmodule

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open Polynomial Submodule
open scoped BigOperators Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
noncomputable local instance riemannRochPolarFamilyAlgebra : Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π
attribute [local instance] riemannRochPolarFamilyAlgebra
local instance riemannRochPolarFamilyPolynomialScalarTower :
    IsScalarTower k (Polynomial k) F :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
attribute [local instance] riemannRochPolarFamilyPolynomialScalarTower
local instance riemannRochPolarFamilyRationalScalarTower :
    IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
attribute [local instance] riemannRochPolarFamilyRationalScalarTower
namespace GlobalPlace
local instance riemannRochPolarFamilyFiniteDimensional
    (G : Divisor (GlobalPlace k F)) :
    FiniteDimensional k (riemannRochSubmodule G) :=
  finiteDimensional_riemannRochSubmodule
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G
attribute [local instance] riemannRochPolarFamilyFiniteDimensional
noncomputable def polarDivisor (x : F) : Divisor (GlobalPlace k F) := by
  classical
  exact if hx : x = 0 then 0
    else (-principalDivisor (k := k) (F := F) (Units.mk0 x hx)) ⊔ 0
noncomputable def basisPoleBound {ι : Type*} [Fintype ι]
    (b : ι → F) : Divisor (GlobalPlace k F) :=
  (Finset.univ : Finset ι).sum fun i =>
    polarDivisor (k := k) (F := F) (b i)
noncomputable def chartVariable : F :=
  algebraMap (RatFunc k) F RatFunc.X
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry


