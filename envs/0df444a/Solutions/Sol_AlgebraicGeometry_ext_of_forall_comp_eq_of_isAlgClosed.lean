-- Prove2me | solution 1 for AlgebraicGeometry.ext_of_forall_comp_eq_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/551d8180-f703-5dc5-a95a-02245206b9fa

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ext_of_forall_comp_eq_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {κ : Type u} [Field κ] [IsAlgClosed κ] {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of κ)) (fY : Y ⟶ Spec (CommRingCat.of κ))
    [LocallyOfFiniteType fX] [IsReduced X] [IsSeparated fY]
    {f g : X ⟶ Y} (hf : f ≫ fY = fX) (hg : g ≫ fY = fX)
    (h : ∀ x : Spec (CommRingCat.of κ) ⟶ X, x ≫ fX = 𝟙 _ → x ≫ f = x ≫ g) :
    f = g := by
  classical

  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace fX
  refine ext_of_fromSpecResidueField_eq f g fY (closedPoints X) ?_ ?_ (hf.trans hg.symm)
  · rw [Dense, ← Set.eq_univ_iff_forall]
    exact closure_closedPoints
  · intro x hx

    have hxcl : IsClosed ({x} : Set X) := hx
    haveI : LocallyOfFiniteType (X.fromSpecResidueField x) := isClosed_singleton_iff_locallyOfFiniteType.1 hxcl
    haveI : LocallyOfFiniteType (X.fromSpecResidueField x ≫ fX) := inferInstance

    set φ : CommRingCat.of κ ⟶ CommRingCat.of (X.residueField x) := Spec.preimage (X.fromSpecResidueField x ≫ fX) with hφdef
    have hφ : Spec.map φ = X.fromSpecResidueField x ≫ fX := Spec.map_preimage _
    have hft : RingHom.FiniteType φ.hom := by
      have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
      exact HasRingHomProperty.Spec_iff.mp this
    letI : Algebra κ (X.residueField x) := φ.hom.toAlgebra
    haveI : Algebra.FiniteType κ (X.residueField x) := hft
    haveI : Module.Finite κ (X.residueField x) := finite_of_finite_type_of_isJacobsonRing κ (X.residueField x)
    haveI : Algebra.IsIntegral κ (X.residueField x) := inferInstance
    have hbij : Function.Bijective (algebraMap κ (X.residueField x)) := IsAlgClosed.algebraMap_bijective_of_isIntegral

    let e : κ ≃+* X.residueField x := RingEquiv.ofBijective (algebraMap κ (X.residueField x)) hbij
    let ψ : CommRingCat.of (X.residueField x) ⟶ CommRingCat.of κ := CommRingCat.ofHom e.symm.toRingHom
    have hψφ : φ ≫ ψ = 𝟙 _ := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      change e.symm (algebraMap κ (X.residueField x) a) = a
      exact e.symm_apply_apply a
    haveI : IsIso ψ := by
      refine ⟨⟨φ, ?_, hψφ⟩⟩
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro b
      change algebraMap κ (X.residueField x) (e.symm b) = b
      exact e.apply_symm_apply b
    let x₀ : Spec (CommRingCat.of κ) ⟶ X := Spec.map ψ ≫ X.fromSpecResidueField x
    have hx₀ : x₀ ≫ fX = 𝟙 _ := by
      change (Spec.map ψ ≫ X.fromSpecResidueField x) ≫ fX = 𝟙 _
      rw [Category.assoc, ← hφ, ← Spec.map_comp, hψφ, Spec.map_id]
    have hx₀' := h x₀ hx₀
    change (Spec.map ψ ≫ X.fromSpecResidueField x) ≫ f = (Spec.map ψ ≫ X.fromSpecResidueField x) ≫ g at hx₀'
    rw [Category.assoc, Category.assoc] at hx₀'
    exact (cancel_epi (Spec.map ψ)).1 hx₀'

end S_AlgebraicGeometry_ext_of_forall_comp_eq_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicGeometry_ext_of_forall_comp_eq_of_isAlgClosed (solution)
