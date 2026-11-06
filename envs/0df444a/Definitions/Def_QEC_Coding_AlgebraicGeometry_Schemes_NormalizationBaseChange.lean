-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_NormalizationBaseChange
-- name    : QEC_Coding_AlgebraicGeometry_Schemes_NormalizationBaseChange
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:11:58.076416+00:00
-- url     : https://prove2.me/theorems/3d282eb6-9420-496a-8c0e-685fe64b6196
-- title:
--   Normalization Base Change
-- statement:
--   Definitions and structural lemmas for Normalization Base Change, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/NormalizationBaseChange.lean

import Mathlib.AlgebraicGeometry.Pullbacks
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]
lemma algHomRingHom_apply (f : A →ₐ[R] B) (x : A) : f.toRingHom x = f x := rfl
open scoped TensorProduct
section TensorApplications
variable {R₀ S₀ A₀ D₀ : Type} [CommRing R₀] [CommRing S₀] [CommRing A₀] [CommRing D₀]
  [Algebra R₀ S₀] [Algebra R₀ A₀]
def normalizationBaseRingHom (e : S₀ ⊗[R₀] A₀ →+* D₀) : A₀ →+* D₀ where
  toFun x := e ((1 : S₀) ⊗ₜ[R₀] x)
  map_one' := by
    simpa only [RingHom.comp_apply, algHomRingHom_apply, Algebra.TensorProduct.includeRight_apply] using (e.comp (Algebra.TensorProduct.includeRight : A₀ →ₐ[R₀] S₀ ⊗[R₀] A₀).toRingHom).map_one
  map_mul' x y := by
    simpa only [RingHom.comp_apply, algHomRingHom_apply, Algebra.TensorProduct.includeRight_apply] using (e.comp (Algebra.TensorProduct.includeRight : A₀ →ₐ[R₀] S₀ ⊗[R₀] A₀).toRingHom).map_mul x y
  map_zero' := by
    simpa only [RingHom.comp_apply, algHomRingHom_apply, Algebra.TensorProduct.includeRight_apply] using (e.comp (Algebra.TensorProduct.includeRight : A₀ →ₐ[R₀] S₀ ⊗[R₀] A₀).toRingHom).map_zero
  map_add' x y := by
    simpa only [RingHom.comp_apply, algHomRingHom_apply, Algebra.TensorProduct.includeRight_apply] using (e.comp (Algebra.TensorProduct.includeRight : A₀ →ₐ[R₀] S₀ ⊗[R₀] A₀).toRingHom).map_add x y
def normalizationConstantRingHom (e : S₀ ⊗[R₀] A₀ →+* D₀) : S₀ →+* D₀ where
  toFun x := e (x ⊗ₜ[R₀] (1 : A₀))
  map_one' := by
    simpa only [RingHom.comp_apply, algHomRingHom_apply, Algebra.TensorProduct.includeLeft_apply] using (e.comp (Algebra.TensorProduct.includeLeft : S₀ →ₐ[R₀] S₀ ⊗[R₀] A₀).toRingHom).map_one
  map_mul' x y := by
    simpa only [RingHom.comp_apply, algHomRingHom_apply, Algebra.TensorProduct.includeLeft_apply] using (e.comp (Algebra.TensorProduct.includeLeft : S₀ →ₐ[R₀] S₀ ⊗[R₀] A₀).toRingHom).map_mul x y
  map_zero' := by
    simpa only [RingHom.comp_apply, algHomRingHom_apply, Algebra.TensorProduct.includeLeft_apply] using (e.comp (Algebra.TensorProduct.includeLeft : S₀ →ₐ[R₀] S₀ ⊗[R₀] A₀).toRingHom).map_zero
  map_add' x y := by
    simpa only [RingHom.comp_apply, algHomRingHom_apply, Algebra.TensorProduct.includeLeft_apply] using (e.comp (Algebra.TensorProduct.includeLeft : S₀ →ₐ[R₀] S₀ ⊗[R₀] A₀).toRingHom).map_add x y
end TensorApplications
end QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
namespace QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
variable {R S A B : Type} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra S B]
def normalizationTensorSpecIso (e : S ⊗[R] A ≃ₐ[S] B) :
    Spec (.of B) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
  (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op) ≪≫
    (pullbackSpecIso R S A).symm
end
end QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
namespace QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
open scoped TensorProduct
noncomputable section
variable {R S A B : Type} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra S B]
end
end QEC.Coding.AlgebraicGeometry.NormalizationBaseChange


