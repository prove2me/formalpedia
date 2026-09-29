-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.IsFibreReading.eq_zero_of_isFibreReading_zero_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/46d911d7-e478-5c08-92a2-6fba31c3a9b5

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isAffineOpen_preimage_and_isPushout_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_IsFibreReading_eq_zero_of_isFibreReading_zero_of_flat

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

open scoped TensorProduct

universe u

theorem solution
    {B₁ : Type u} [CommRing B₁] [IsLocalRing B₁]
    (V : Type u) [AddCommGroup V] [Module (ResidueField B₁) V] [Module.Finite (ResidueField B₁) V]
    [Module B₁ V] [IsScalarTower B₁ (ResidueField B₁) V] (ι : V →ₗ[B₁] B₁) (hι : Function.Injective ι)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁)) [Flat f]
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of (ResidueField B₁))) (i : Xk ⟶ X)
    (hi : IsPullback i fk f (Spec.map (CommRingCat.ofHom (residue B₁))))
    (U : X.Opens) (hU : IsAffineOpen U) (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U) (hW' : i ⁻¹ᵁ U ≤ W)
    (δ : Γ(X, U)) (hδ : IsFibreReading V ι f fk i U W hW δ 0) :
    δ = 0 := by
  classical
  obtain rfl : W = i ⁻¹ᵁ U := le_antisymm hW hW'
  obtain ⟨n, v, s, hsum, hread⟩ := hδ

  letI iA : Algebra B₁ Γ(X, U) := f.sectionsAlgebra U
  letI iAk : Algebra (ResidueField B₁) Γ(Xk, i ⁻¹ᵁ U) := fk.sectionsAlgebra (i ⁻¹ᵁ U)
  letI iT : Algebra Γ(X, U) Γ(Xk, i ⁻¹ᵁ U) := (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  letI iB : Algebra B₁ Γ(Xk, i ⁻¹ᵁ U) :=
    ((algebraMap (ResidueField B₁) Γ(Xk, i ⁻¹ᵁ U)).comp (algebraMap B₁ (ResidueField B₁))).toAlgebra
  haveI : IsScalarTower B₁ (ResidueField B₁) Γ(Xk, i ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have htop : (Spec.map (CommRingCat.ofHom (residue B₁))).appLE ⊤ ⊤ le_top =
      (Spec.map (CommRingCat.ofHom (residue B₁))).appTop := Scheme.Hom.appLE_eq_app _
  have hsq : ∀ b : B₁, algebraMap Γ(X, U) Γ(Xk, i ⁻¹ᵁ U) (algebraMap B₁ Γ(X, U) b) =
      algebraMap B₁ Γ(Xk, i ⁻¹ᵁ U) b := by
    intro b
    change (((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv ≫ f.appLE ⊤ U le_top) ≫ i.appLE U (i ⁻¹ᵁ U) le_rfl).hom b =
      ((CommRingCat.ofHom (residue B₁) ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B₁))).inv) ≫
        fk.appLE ⊤ (i ⁻¹ᵁ U) le_top).hom b
    congr 2
    rw [Category.assoc, Scheme.Hom.appLE_comp_appLE, Scheme.ΓSpecIso_inv_naturality, Category.assoc, ← htop,
      Scheme.Hom.appLE_comp_appLE]
    congr 1
    have key : ∀ {g₁ g₂ : Xk ⟶ Spec (CommRingCat.of B₁)} (h : g₁ = g₂)
        (p₁ : i ⁻¹ᵁ U ≤ g₁ ⁻¹ᵁ ⊤) (p₂ : i ⁻¹ᵁ U ≤ g₂ ⁻¹ᵁ ⊤), g₁.appLE ⊤ (i ⁻¹ᵁ U) p₁ = g₂.appLE ⊤ (i ⁻¹ᵁ U) p₂ := by
      rintro g₁ _ rfl p₁ p₂; rfl
    exact key hi.w _ _
  haveI : IsScalarTower B₁ Γ(X, U) Γ(Xk, i ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq (fun b => (hsq b).symm)
  have hi' : IsPullback i fk f (Spec.map (CommRingCat.ofHom (algebraMap B₁ (ResidueField B₁)))) := by
    rw [ResidueField.algebraMap_eq]; exact hi

  haveI hP : Algebra.IsPushout B₁ (ResidueField B₁) Γ(X, U) Γ(Xk, i ⁻¹ᵁ U) :=
    (Scheme.Hom.isAffineOpen_preimage_and_isPushout_of_isPullback f fk i hi' U hU).2

  have hsum' : (∑ j, algebraMap B₁ (X.presheaf.obj (Opposite.op U)) (ι (v j)) * s j) = δ := hsum
  have hread' : ∀ ξ : Module.Dual (ResidueField B₁) V,
      (∑ j, algebraMap (ResidueField B₁) (Xk.presheaf.obj (Opposite.op (i ⁻¹ᵁ U))) (ξ (v j)) * (i.app U).hom (s j)) = 0 := by
    intro ξ
    have h := hread ξ
    rw [LinearMap.zero_apply] at h
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h.symm
    rw [OModulePresheaf.res_refl_apply]
    rfl

  have h1 : ∀ ξ : Module.Dual (ResidueField B₁) V,
      (∑ j, ξ (v j) ⊗ₜ[B₁] s j : ResidueField B₁ ⊗[B₁] (X.presheaf.obj (Opposite.op U))) = 0 := by
    intro ξ
    apply (Algebra.IsPushout.equiv B₁ (ResidueField B₁) (X.presheaf.obj (Opposite.op U)) (Xk.presheaf.obj (Opposite.op (i ⁻¹ᵁ U)))).injective
    rw [map_zero, map_sum, ← hread' ξ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.IsPushout.equiv_tmul, Scheme.Hom.app_eq_appLE]
    rfl

  have h2 : ∀ (e : V) (ξ : Module.Dual (ResidueField B₁) V),
      (∑ j, algebraMap B₁ (X.presheaf.obj (Opposite.op U)) (ι (ξ (v j) • e)) * s j) = 0 := by
    intro e ξ
    let Λ : ResidueField B₁ ⊗[B₁] (X.presheaf.obj (Opposite.op U)) →ₗ[B₁] (X.presheaf.obj (Opposite.op U)) :=
      TensorProduct.lift (LinearMap.mk₂ B₁ (fun (c : ResidueField B₁) (a : (X.presheaf.obj (Opposite.op U))) => algebraMap B₁ (X.presheaf.obj (Opposite.op U)) (ι (c • e)) * a)
        (fun c c' a => by simp only [add_smul, map_add, add_mul])
        (fun b c a => by
          rw [smul_assoc, map_smul, smul_eq_mul, map_mul, Algebra.smul_def, mul_assoc])
        (fun c a a' => by simp only [mul_add])
        (fun b c a => by rw [Algebra.smul_def, Algebra.smul_def, mul_left_comm]))
    have hΛ : ∀ c a, Λ (c ⊗ₜ a) = algebraMap B₁ (X.presheaf.obj (Opposite.op U)) (ι (c • e)) * a := fun c a => TensorProduct.lift.tmul _ _
    have h := congrArg Λ (h1 ξ)
    rw [map_sum, map_zero] at h
    simpa only [hΛ] using h

  let bV := Module.finBasis (ResidueField B₁) V
  have h3 : ∀ j, ι (v j) = ∑ l, ι (bV.dualBasis l (v j) • bV l) := fun j => by
    rw [← map_sum]
    congr 1
    simp only [bV.dualBasis_apply]
    exact (bV.sum_repr (v j)).symm
  calc δ = ∑ j, algebraMap B₁ (X.presheaf.obj (Opposite.op U)) (ι (v j)) * s j := hsum'.symm
    _ = ∑ j, ∑ l, algebraMap B₁ (X.presheaf.obj (Opposite.op U)) (ι (bV.dualBasis l (v j) • bV l)) * s j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [h3, map_sum, Finset.sum_mul]
    _ = ∑ l, ∑ j, algebraMap B₁ (X.presheaf.obj (Opposite.op U)) (ι (bV.dualBasis l (v j) • bV l)) * s j := Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero fun l _ => h2 (bV l) (bV.dualBasis l)

#print axioms solution

end S_AlgebraicGeometry_SmallExtension_IsFibreReading_eq_zero_of_isFibreReading_zero_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_IsFibreReading_eq_zero_of_isFibreReading_zero_of_flat (solution)
