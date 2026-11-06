-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_Differential
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:16:36.241782+00:00
-- url     : https://prove2.me/theorems/c2e9bd19-baa0-4b0f-a719-d7bcf00e7807
-- title:
--   Differential
-- statement:
--   Definitions and structural lemmas for Differential, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/Differential.lean

import Mathlib.RingTheory.Kaehler.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SeparableDerivationExtension
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
variable (k F : Type*) [Field k] [Field F] [Algebra k F]
abbrev Differential : Type _ := KaehlerDifferential k F
noncomputable def differential : F →ₗ[k] Differential k F :=
  (KaehlerDifferential.D k F).toLinearMap
@[simp]
theorem differential_zero : differential k F 0 = 0 :=
  (differential k F).map_zero
@[simp]
theorem differential_add (f g : F) :
    differential k F (f + g) = differential k F f + differential k F g :=
  (differential k F).map_add f g
@[simp]
theorem differential_algebraMap (a : k) :
    differential k F (algebraMap k F a) = 0 := by
  exact (KaehlerDifferential.D k F).map_algebraMap a
noncomputable def Differential.lift {M : Type*} [AddCommGroup M] [Module k M]
    [Module F M] [IsScalarTower k F M] (D : Derivation k F M) :
    Differential k F →ₗ[F] M :=
  D.liftKaehlerDifferential
theorem Differential.lift_differential {M : Type*} [AddCommGroup M] [Module k M]
    [Module F M] [IsScalarTower k F M] (D : Derivation k F M) (f : F) :
    Differential.lift k F D (differential k F f) = D f :=
  D.liftKaehlerDifferential_comp_D f
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
namespace FunctionFieldDifferential
open scoped RatFunc
variable {k F : Type*} [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]
noncomputable def functionFieldDerivation : Derivation k F F :=
  SeparableDerivationExtension.separableDerivationExtension (k := k) (F := F)
    (RatFuncDerivation.rationalDerivation (k := k) (M := F) 1)
theorem functionFieldDerivation_apply_X :
    functionFieldDerivation (k := k) (F := F)
      (algebraMap (RatFunc k) F RatFunc.X) = 1 := by
  rw [functionFieldDerivation,
    SeparableDerivationExtension.separableDerivationExtension_apply_algebraMap]
  exact RatFuncDerivation.rationalDerivation_apply_X (k := k) (1 : F)
noncomputable def functionFieldDifferentialGenerator : Differential k F :=
  differential k F (algebraMap (RatFunc k) F RatFunc.X)
noncomputable def functionFieldDifferentialCoordinate : Differential k F →ₗ[F] F :=
  Differential.lift k F (functionFieldDerivation (k := k) (F := F))
noncomputable def functionFieldDifferentialGeneratorMap : F →ₗ[F] Differential k F :=
  (LinearMap.id : F →ₗ[F] F).smulRight
    (functionFieldDifferentialGenerator (k := k) (F := F))
theorem functionFieldDifferentialCoordinate_generator :
    functionFieldDifferentialCoordinate (k := k) (F := F)
      (functionFieldDifferentialGenerator (k := k) (F := F)) = 1 := by
  unfold functionFieldDifferentialCoordinate functionFieldDifferentialGenerator
  rw [Differential.lift_differential]
  exact functionFieldDerivation_apply_X (k := k) (F := F)
theorem separableDerivationValueEquiv_apply_X
    (D : Derivation k F (Differential k F)) :
    SeparableDerivationExtension.separableDerivationValueEquiv (k := k) (F := F)
      (M := Differential k F) D = D (algebraMap (RatFunc k) F RatFunc.X) :=
  rfl
theorem functionFieldDifferentialCoordinate_comp_generatorMap :
    (functionFieldDifferentialCoordinate (k := k) (F := F)).comp
      (functionFieldDifferentialGeneratorMap (k := k) (F := F)) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  change functionFieldDifferentialCoordinate (k := k) (F := F)
      (a • functionFieldDifferentialGenerator (k := k) (F := F)) = a
  simpa only [map_smul, functionFieldDifferentialCoordinate_generator, smul_eq_mul, mul_one]
theorem functionFieldDifferentialGeneratorMap_comp_coordinate :
    (functionFieldDifferentialGeneratorMap (k := k) (F := F)).comp
      (functionFieldDifferentialCoordinate (k := k) (F := F)) = LinearMap.id := by
  apply Derivation.liftKaehlerDifferential_unique
  apply (SeparableDerivationExtension.separableDerivationValueEquiv (k := k) (F := F)
    (M := Differential k F)).injective
  rw [separableDerivationValueEquiv_apply_X, separableDerivationValueEquiv_apply_X]
  change functionFieldDifferentialGeneratorMap (k := k) (F := F)
      (functionFieldDifferentialCoordinate (k := k) (F := F)
        (functionFieldDifferentialGenerator (k := k) (F := F))) =
      functionFieldDifferentialGenerator (k := k) (F := F)
  rw [functionFieldDifferentialCoordinate_generator]
  simp only [functionFieldDifferentialGeneratorMap, LinearMap.smulRight_apply,
    LinearMap.id_apply, one_smul]
noncomputable def functionFieldDifferentialEquiv : Differential k F ≃ₗ[F] F :=
  LinearEquiv.ofLinear
    (functionFieldDifferentialCoordinate (k := k) (F := F))
    (functionFieldDifferentialGeneratorMap (k := k) (F := F))
    (functionFieldDifferentialCoordinate_comp_generatorMap (k := k) (F := F))
    (functionFieldDifferentialGeneratorMap_comp_coordinate (k := k) (F := F))
end FunctionFieldDifferential
end QEC.Coding.AlgebraicGeometry


