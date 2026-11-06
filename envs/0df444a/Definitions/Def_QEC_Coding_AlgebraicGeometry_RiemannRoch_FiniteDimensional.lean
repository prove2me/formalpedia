-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_FiniteDimensional
-- name    : QEC_Coding_AlgebraicGeometry_RiemannRoch_FiniteDimensional
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T14:06:17.483712+00:00
-- url     : https://prove2.me/theorems/067bb295-9d96-4527-a255-9c1e76f4a75f
-- title:
--   Finite Dimensional
-- statement:
--   Definitions and structural lemmas for Finite Dimensional, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/FiniteDimensional.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_ChartContainment
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_TwoChartFiniteDimensionalBridge
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc nonZeroDivisors
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
theorem directConstantAlgebra_map_eq_rationalRestriction
    : letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
    algebraMap k F = (algebraMap (RatFunc k) F).comp (algebraMap k (RatFunc k)) := by
  letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
  ext c
  change algebraMap (Polynomial k) F (Polynomial.C c) =
    algebraMap (RatFunc k) F
      (algebraMap (Polynomial k) (RatFunc k) (Polynomial.C c))
  exact IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) F (Polynomial.C c)
@[reducible] noncomputable def directConstantScalarTower :
    letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
    IsScalarTower k (RatFunc k) F := by
  letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
  exact IsScalarTower.of_algebraMap_eq fun c => by
    simpa only [RingHom.comp_apply] using
      DFunLike.congr_fun
        (directConstantAlgebra_map_eq_rationalRestriction (π := π) (ρ := ρ)
          (τ := τ) (φ := φ) (s := s) k F) c
noncomputable def GlobalPlace.directChartModule
    (G : Divisor (@GlobalPlace k F _ _ _ (@AffinePlace.constantAlgebra k F _ _ π))) :
    Submodule (Polynomial k) F :=
  (AffinePlace.chartFractionalLattice k F
    (GlobalPlace.directChartDivisor (π := π) k F G)).coeToSubmodule.restrictScalars (Polynomial k)
end QEC.Coding.AlgebraicGeometry


