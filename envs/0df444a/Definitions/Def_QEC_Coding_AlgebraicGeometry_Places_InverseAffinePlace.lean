-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
-- name    : QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:41:40.969956+00:00
-- url     : https://prove2.me/theorems/496ab4a0-8b39-4221-aff8-af5d9d00163f
-- title:
--   Inverse Affine Place
-- statement:
--   Definitions and structural lemmas for Inverse Affine Place, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseAffinePlace.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseChart
import Mathlib.FieldTheory.Separable
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
namespace InverseAffinePlace
open scoped IntermediateField Polynomial RatFunc
section RationalTransport
variable (k : Type*) [Field k]
theorem inverseVariable_transcendental :
    Transcendental k ((RatFunc.X : RatFunc k)⁻¹) := by
  intro h
  exact RatFunc.transcendental_X (IsAlgebraic.inv_iff.mp h)
theorem adjoin_inverseVariable_eq_top :
    k⟮((RatFunc.X : RatFunc k)⁻¹)⟯ = ⊤ := by
  apply top_unique
  rw [← RatFunc.adjoin_X]
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  rw [Set.mem_singleton_iff.mp hx]
  change (RatFunc.X : RatFunc k) ∈ IntermediateField.adjoin k {(RatFunc.X : RatFunc k)⁻¹}
  simpa only [inv_inv] using
    (IntermediateField.adjoin k {((RatFunc.X : RatFunc k)⁻¹)}).inv_mem
      (IntermediateField.subset_adjoin k {((RatFunc.X : RatFunc k)⁻¹)}
        (Set.mem_singleton _))
noncomputable def rationalInvolution : RatFunc k ≃ₐ[k] RatFunc k :=
  (RatFunc.algEquivOfTranscendental ((RatFunc.X : RatFunc k)⁻¹)
    (inverseVariable_transcendental k)).trans
    ((IntermediateField.equivOfEq (adjoin_inverseVariable_eq_top k)).trans
      IntermediateField.topEquiv)
variable (F : Type*) [Field F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
noncomputable def transportedRationalMap : RatFunc k →+* F :=
  (algebraMap k⟮X⟯ F).comp (rationalInvolution k).toRingEquiv.toRingHom
@[reducible] noncomputable def transportedRationalAlgebra : Algebra k⟮X⟯ F :=
  (transportedRationalMap k F).toAlgebra
noncomputable def transportedPolynomialMap : k[X] →+* F :=
  (transportedRationalMap (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)).comp (algebraMap k[X] k⟮X⟯)
@[reducible] noncomputable def transportedPolynomialAlgebra : Algebra k[X] F :=
  (transportedPolynomialMap (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)).toAlgebra
theorem transportedScalarTower :
    let : Algebra k⟮X⟯ F := transportedRationalAlgebra (k := k) (F := F)
      (oldRationalAlgebra := oldRationalAlgebra)
    let : Algebra k[X] F := transportedPolynomialAlgebra (k := k) (F := F)
      (oldRationalAlgebra := oldRationalAlgebra)
    IsScalarTower k[X] k⟮X⟯ F := by
  let : Algebra k⟮X⟯ F := transportedRationalAlgebra (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
  let : Algebra k[X] F := transportedPolynomialAlgebra (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
  let : FaithfulSMul k[X] F :=
    (faithfulSMul_iff_algebraMap_injective k[X] F).mpr <| by
      change Function.Injective (transportedPolynomialMap (k := k) (F := F)
        (oldRationalAlgebra := oldRationalAlgebra))
      exact (transportedRationalMap (k := k) (F := F)
        (oldRationalAlgebra := oldRationalAlgebra)).injective.comp
          (IsFractionRing.injective k[X] k⟮X⟯)
  let liftRationalAlgebra : Algebra k⟮X⟯ F := by
    let : Algebra k[X] F := transportedPolynomialAlgebra (k := k) (F := F)
      (oldRationalAlgebra := oldRationalAlgebra)
    exact RatFunc.liftAlgebra k F
  have hAlgebra : transportedRationalAlgebra (k := k) (F := F)
      (oldRationalAlgebra := oldRationalAlgebra) = liftRationalAlgebra := by
    apply Algebra.algebra_ext
    intro x
    let : Algebra k[X] F := transportedPolynomialAlgebra (k := k) (F := F)
      (oldRationalAlgebra := oldRationalAlgebra)
    let : Algebra k⟮X⟯ F := liftRationalAlgebra
    let : IsScalarTower k[X] k⟮X⟯ F := RatFunc.isScalarTower_liftAlgebra k F
    have hMaps : transportedRationalMap (k := k) (F := F)
        (oldRationalAlgebra := oldRationalAlgebra) = algebraMap k⟮X⟯ F := by
      apply IsFractionRing.ringHom_ext (A := k[X])
      intro p
      change transportedRationalMap (k := k) (F := F)
          (oldRationalAlgebra := oldRationalAlgebra) (algebraMap k[X] k⟮X⟯ p) =
        algebraMap k⟮X⟯ F (algebraMap k[X] k⟮X⟯ p)
      exact IsScalarTower.algebraMap_apply k[X] k⟮X⟯ F p
    exact RingHom.congr_fun hMaps x
  rw [hAlgebra]
  exact RatFunc.isScalarTower_liftAlgebra k F
variable [oldFunctionField : _root_.FunctionField k F]
theorem transportedFunctionField :
    @FunctionField k F _ _ (transportedRationalAlgebra k F) := by
  exact @Module.Finite.of_equiv_equiv (RatFunc k) F (RatFunc k) F
    _ _ _ _ oldRationalAlgebra (transportedRationalAlgebra (k := k) (F := F)
      (oldRationalAlgebra := oldRationalAlgebra))
    (rationalInvolution k).symm.toRingEquiv (RingEquiv.refl F) (by
      ext x
      change algebraMap k⟮X⟯ F
        (rationalInvolution k ((rationalInvolution k).symm x)) = algebraMap k⟮X⟯ F x
      simp) oldFunctionField
omit oldFunctionField
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]
theorem transportedIsSeparable :
    @Algebra.IsSeparable k⟮X⟯ F _ _ (transportedRationalAlgebra (k := k) (F := F)
      (oldRationalAlgebra := oldRationalAlgebra)) := by
  exact @Algebra.IsSeparable.of_equiv_equiv (RatFunc k) F (RatFunc k) F
    _ _ _ _ oldRationalAlgebra (transportedRationalAlgebra (k := k) (F := F)
      (oldRationalAlgebra := oldRationalAlgebra))
    (rationalInvolution k).symm.toRingEquiv (RingEquiv.refl F) (by
      ext x
      change algebraMap k⟮X⟯ F
        (rationalInvolution k ((rationalInvolution k).symm x)) = algebraMap k⟮X⟯ F x
      simp) oldSeparable
end RationalTransport
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]
@[reducible] noncomputable def constantAlgebra : Algebra k F :=
  ((algebraMap k⟮X⟯ F).comp (algebraMap k k⟮X⟯)).toAlgebra
@[reducible] noncomputable def constantScalarTower :
    letI : Algebra k F := constantAlgebra k F
    IsScalarTower k k⟮X⟯ F := by
  letI : Algebra k F := constantAlgebra k F
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl
noncomputable abbrev carrier : Type _ :=
  letI : Algebra k⟮X⟯ F := transportedRationalAlgebra (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
  letI : Algebra k[X] F := transportedPolynomialAlgebra (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
  letI : IsScalarTower k[X] k⟮X⟯ F := transportedScalarTower (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
  letI : _root_.FunctionField k F := transportedFunctionField (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField)
  letI : Algebra.IsSeparable k⟮X⟯ F := transportedIsSeparable (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable)
  AffinePlace.carrier k F
end InverseAffinePlace
end QEC.Coding.AlgebraicGeometry


