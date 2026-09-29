-- Prove2me | solution 1 for AlgebraicGeometry.IsAffineOpen.ringEquiv_tensor_map_eq_presheaf_map_of_specMap_comp_fromSpec_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/ef211277-ef6e-5c9a-a9f8-ec707f1ef2d4

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IsAffineOpen_ringEquiv_tensor_map_eq_presheaf_map_of_specMap_comp_fromSpec_eq

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.TwoAffineOpenCover TensorProduct IsLocalRing"

universe u

namespace SigmaTransport

theorem ringHom_tmul_ext {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Semiring C] (f g : A ⊗[R] B →+* C)
    (h₁ : ∀ a : A, f (a ⊗ₜ 1) = g (a ⊗ₜ 1)) (h₂ : ∀ b : B, f (1 ⊗ₜ b) = g (1 ⊗ₜ b)) (z : A ⊗[R] B) :
    f z = g z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b =>
    have : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [this, map_mul, map_mul, h₁, h₂]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem ringHom_eq_of_specMap_comp_eq {X Y : Scheme.{u}} {OU : Y.Opens} (hOU : IsAffineOpen OU) {W' : X.Opens} (hW' : IsAffineOpen W')
    (ψ ψ' : Γ(Y, OU) →+* Γ(X, W'))
    (h : hW'.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ) ≫ hOU.fromSpec =
      hW'.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ') ≫ hOU.fromSpec) : ψ = ψ' := by
  rw [Iso.cancel_iso_hom_left, cancel_mono] at h
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

end SigmaTransport

open SigmaTransport in
theorem solution
    {T' : Type u} [CommRing T'] [IsLocalRing T']
    {Y Y' Ak : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T')) (qY' : Y' ⟶ Spec (CommRingCat.of T'))
    (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T')))
    (OU : Y.Opens) (hOU : IsAffineOpen OU) (OU' : Y'.Opens) (hOU' : IsAffineOpen OU')
    (W W' : Ak.Opens) (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hWW : W' ≤ W)
    (m : (W : Scheme.{u}) ⟶ Y)
    (h : letI := algebraOfHom qY OU; letI := algebraOfHom qY' OU'
      Γ(Y, OU) →ₐ[T'] Γ(Y', OU'))
    (σ : letI := algebraOfHom qY OU
      (ResidueField T') ⊗[T'] Γ(Y, OU) ≃+* Γ(Ak, W))
    (σ' : letI := algebraOfHom qY' OU'
      (ResidueField T') ⊗[T'] Γ(Y', OU') ≃+* Γ(Ak, W'))
    (hσ₁ : letI := algebraOfHom qY OU
      hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Y, OU) →ₐ[T'] (ResidueField T') ⊗[T'] Γ(Y, OU)).toRingHom) ≫
          hOU.fromSpec = m)
    (hσ₂ : letI := algebraOfHom qY OU
      letI := algebraOfHom fk W
      ∀ x : ResidueField T', σ (x ⊗ₜ[T'] (1 : Γ(Y, OU))) = algebraMap (ResidueField T') Γ(Ak, W) x)
    (hσ'₂ : letI := algebraOfHom qY' OU'
      letI := algebraOfHom fk W'
      ∀ x : ResidueField T', σ' (x ⊗ₜ[T'] (1 : Γ(Y', OU'))) = algebraMap (ResidueField T') Γ(Ak, W') x)
    (hcomp : letI := algebraOfHom qY OU
      letI := algebraOfHom qY' OU'
      hW'.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom σ'.toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Y', OU') →ₐ[T'] (ResidueField T') ⊗[T'] Γ(Y', OU')).toRingHom) ≫
          Spec.map (CommRingCat.ofHom h.toRingHom) ≫ hOU.fromSpec = Ak.homOfLE hWW ≫ m) :
    letI := algebraOfHom qY OU
    letI := algebraOfHom qY' OU'
    ∀ z : (ResidueField T') ⊗[T'] Γ(Y, OU),
      σ' (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h z) =
        (Ak.presheaf.map (homOfLE hWW).op).hom (σ z) := by
  classical
  letI iOU := algebraOfHom qY OU
  letI iOU' := algebraOfHom qY' OU'
  letI iW := algebraOfHom fk W
  letI iW' := algebraOfHom fk W'
  intro z

  let ψ₁ : Γ(Y, OU) →+* Γ(Ak, W') :=
    (Ak.presheaf.map (homOfLE hWW).op).hom.comp (σ.toRingHom.comp
      (Algebra.TensorProduct.includeRight : Γ(Y, OU) →ₐ[T'] (ResidueField T') ⊗[T'] Γ(Y, OU)).toRingHom)
  let ψ₂ : Γ(Y, OU) →+* Γ(Ak, W') :=
    σ'.toRingHom.comp ((Algebra.TensorProduct.includeRight :
      Γ(Y', OU') →ₐ[T'] (ResidueField T') ⊗[T'] Γ(Y', OU')).toRingHom.comp h.toRingHom)
  have hψ : ψ₁ = ψ₂ := by
    apply ringHom_eq_of_specMap_comp_eq hOU hW'

    have h2 : hW'.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ₂) ≫ hOU.fromSpec = Ak.homOfLE hWW ≫ m := by
      rw [← hcomp]
      simp only [ψ₂, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

    have h1 : hW'.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ₁) ≫ hOU.fromSpec = Ak.homOfLE hWW ≫ m := by
      have key : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : Γ(Y, OU) →ₐ[T'] (ResidueField T') ⊗[T'] Γ(Y, OU)).toRingHom) ≫
          hOU.fromSpec = hW.isoSpec.inv ≫ m := by
        rw [← hσ₁, Iso.inv_hom_id_assoc]
      have nat : Spec.map (Ak.presheaf.map (homOfLE hWW).op) ≫ hW.isoSpec.inv = hW'.isoSpec.inv ≫ Ak.homOfLE hWW := by
        rw [← cancel_mono W.ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.map_fromSpec hW hW',
          Scheme.homOfLE_ι, IsAffineOpen.isoSpec_inv_ι]
      simp only [ψ₁, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom]
      rw [key, ← Category.assoc (Spec.map _), nat, ← Category.assoc, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [h1, h2]

  refine ringHom_tmul_ext
    (σ'.toRingHom.comp (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h).toRingHom)
    ((Ak.presheaf.map (homOfLE hWW).op).hom.comp σ.toRingHom) ?_ ?_ z
  · intro x
    show σ' (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h (x ⊗ₜ 1)) =
      (Ak.presheaf.map (homOfLE hWW).op).hom (σ (x ⊗ₜ 1))
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply, hσ'₂, hσ₂, algebraMap_algebraOfHom, algebraMap_algebraOfHom]
    show _ = (fk.appLE ⊤ W le_top ≫ Ak.presheaf.map (homOfLE hWW).op).hom _
    rw [Scheme.Hom.appLE_map]
  · intro y
    show σ' (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T')) h (1 ⊗ₜ y)) =
      (Ak.presheaf.map (homOfLE hWW).op).hom (σ (1 ⊗ₜ y))
    rw [Algebra.TensorProduct.map_tmul, map_one]
    exact (RingHom.congr_fun hψ y).symm

end S_AlgebraicGeometry_IsAffineOpen_ringEquiv_tensor_map_eq_presheaf_map_of_specMap_comp_fromSpec_eq
end P2MW
export P2MW.S_AlgebraicGeometry_IsAffineOpen_ringEquiv_tensor_map_eq_presheaf_map_of_specMap_comp_fromSpec_eq (solution)
