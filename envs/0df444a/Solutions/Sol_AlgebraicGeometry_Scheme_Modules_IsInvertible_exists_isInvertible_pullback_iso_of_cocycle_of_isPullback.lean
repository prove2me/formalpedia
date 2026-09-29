-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isInvertible_pullback_iso_of_cocycle_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/c5e77717-f305-52aa-b4bc-82692540e2bf

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective
import Theorems.Thm_CommRingCat_isPushout_tensorProduct_tensorProduct
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_descentData_obj_eq_of_cocycle_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isInvertible_pullback_iso_of_cocycle_of_isPullback
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app Algebra.DescentCofaces.i₁_apply Algebra.DescentCofaces.i₂_apply Algebra.DescentCofaces.c₁₂_tmul Algebra.DescentCofaces.c₂₃_tmul Algebra.DescentCofaces.c₁₃_tmul"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace LDESCAux

theorem flat_specMap {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S'] [Module.Flat S S'] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap S S'))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  show (algebraMap S S').Flat
  have h : (algebraMap S S').toAlgebra = ‹Algebra S S'› := Algebra.algebra_ext _ _ fun _ => rfl
  unfold RingHom.Flat
  rw [h]; infer_instance

def objIso {C : Type*} [Category C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat} {ι : Type*} {S : C} {X : ι → C}
    {f : ∀ i, X i ⟶ S} {D₁ D₂ : F.DescentData f} (e : D₁ ≅ D₂) (i : ι) : D₁.obj i ≅ D₂.obj i where
  hom := e.hom.hom i
  inv := e.inv.hom i
  hom_inv_id := by rw [← Pseudofunctor.DescentData.comp_hom, e.hom_inv_id, Pseudofunctor.DescentData.id_hom]
  inv_hom_id := by rw [← Pseudofunctor.DescentData.comp_hom, e.inv_hom_id, Pseudofunctor.DescentData.id_hom]

theorem main
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of S'))
    (L' : X'.Modules) (hL' : Scheme.Modules.IsInvertible L')
    (X'' : Scheme.{u}) (f'' : X'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S')))
    (a₁ a₂ : X'' ⟶ X')
    (ha₁ : IsPullback a₁ f'' f' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (X''' : Scheme.{u}) (f''' : X''' ⟶ Spec (CommRingCat.of (S' ⊗[S] (S' ⊗[S] S'))))
    (b₁₂ b₁₃ b₂₃ : X''' ⟶ X'')
    (hb₁₂ : IsPullback b₁₂ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')).toRingHom)))
    (hb₁₃ : IsPullback b₁₃ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S')).toRingHom)))
    (hb₂₃ : IsPullback b₂₃ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' ⊗[S] S' →ₐ[S] S' ⊗[S] (S' ⊗[S] S')).toRingHom)))
    (h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁) (h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁) (h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂)
    (ψ : (Scheme.Modules.pullback a₁).obj L' ≅ (Scheme.Modules.pullback a₂).obj L')
    (hψ : ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L') ≪≫
          ((Scheme.Modules.pullbackCongr h₂).app L') ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₂).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₃).app L').symm
        = ((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₃ a₂).app L'))
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of S)) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (hca : a₁ ≫ c = a₂ ≫ c) :
    ∃ (L : X.Modules), Scheme.Modules.IsInvertible L ∧ Nonempty ((Scheme.Modules.pullback c).obj L ≅ L') := by

  let ι : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S) := Spec.map (CommRingCat.ofHom (algebraMap S S'))
  let v : Spec (CommRingCat.of (S' ⊗[S] S')) ⟶ Spec (CommRingCat.of S') := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom)
  let w : Spec (CommRingCat.of (S' ⊗[S] S')) ⟶ Spec (CommRingCat.of S') := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)
  let m : Spec (CommRingCat.of (S' ⊗[S] (S' ⊗[S] S'))) ⟶ Spec (CommRingCat.of (S' ⊗[S] S')) :=
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')).toRingHom)
  let n : Spec (CommRingCat.of (S' ⊗[S] (S' ⊗[S] S'))) ⟶ Spec (CommRingCat.of (S' ⊗[S] S')) :=
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' ⊗[S] S' →ₐ[S] S' ⊗[S] (S' ⊗[S] S')).toRingHom)

  haveI : Flat ι := flat_specMap
  haveI : Surjective ι := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩
  haveI : IsAffineHom ι := inferInstance
  haveI : Flat c := MorphismProperty.of_isPullback hc.flip inferInstance
  haveI : Surjective c := MorphismProperty.of_isPullback hc.flip inferInstance
  haveI : IsAffineHom c := MorphismProperty.of_isPullback hc.flip inferInstance

  have hSpec : IsPullback v w ι ι :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct S S' S')
  have hbig : IsPullback (f'' ≫ w) a₁ ι (f' ≫ ι) := ha₁.flip.paste_horiz hSpec.flip
  have hbig' : IsPullback (a₂ ≫ f') a₁ ι (c ≫ f) := by rw [ha₂.w, hc.w]; exact hbig
  have hP : IsPullback a₁ a₂ c c := (IsPullback.of_right hbig' hca.symm hc.flip).flip

  have hSpec3 : IsPullback m n w v :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct_tensorProduct S S' S' S')
  have hbig3 : IsPullback (f''' ≫ n) b₁₂ v (f'' ≫ w) := hb₁₂.flip.paste_horiz hSpec3.flip
  have hbig3' : IsPullback (b₂₃ ≫ f'') b₁₂ v (a₂ ≫ f') := by rw [hb₂₃.w, ha₂.w]; exact hbig3
  have hT : IsPullback b₁₂ b₂₃ a₂ a₁ := (IsPullback.of_right hbig3' h₂.symm ha₁.flip).flip

  obtain ⟨D, hD⟩ := AlgebraicGeometry.Scheme.Modules.exists_descentData_obj_eq_of_cocycle_of_isPullback c a₁ a₂ hP b₁₂ b₁₃ b₂₃ h₁ h₂ h₃ hT L' ψ hψ
  obtain ⟨L, hL, ⟨e⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective c D
      (fun i => by rw [hD i]; exact hL')
  exact ⟨L, hL, ⟨objIso e () ≪≫ eqToIso (hD ())⟩⟩

end LDESCAux

theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of S'))
    (L' : X'.Modules) (hL' : Scheme.Modules.IsInvertible L')
    (X'' : Scheme.{u}) (f'' : X'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S')))
    (a₁ a₂ : X'' ⟶ X')
    (ha₁ : IsPullback a₁ f'' f' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (X''' : Scheme.{u}) (f''' : X''' ⟶ Spec (CommRingCat.of (S' ⊗[S] (S' ⊗[S] S'))))
    (b₁₂ b₁₃ b₂₃ : X''' ⟶ X'')
    (hb₁₂ : IsPullback b₁₂ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')).toRingHom)))
    (hb₁₃ : IsPullback b₁₃ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S')).toRingHom)))
    (hb₂₃ : IsPullback b₂₃ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' ⊗[S] S' →ₐ[S] S' ⊗[S] (S' ⊗[S] S')).toRingHom)))
    (h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁) (h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁) (h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂)
    (ψ : (Scheme.Modules.pullback a₁).obj L' ≅ (Scheme.Modules.pullback a₂).obj L')
    (hψ : ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L') ≪≫
          ((Scheme.Modules.pullbackCongr h₂).app L') ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₂).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₃).app L').symm
        = ((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₃ a₂).app L'))
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of S)) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (hca : a₁ ≫ c = a₂ ≫ c) :
    ∃ (L : X.Modules), Scheme.Modules.IsInvertible L ∧ Nonempty ((Scheme.Modules.pullback c).obj L ≅ L') :=
  LDESCAux.main S' X' f' L' hL' X'' f'' a₁ a₂ ha₁ ha₂ X''' f''' b₁₂ b₁₃ b₂₃ hb₁₂ hb₁₃ hb₂₃ h₁ h₂ h₃ ψ hψ X f c hc hca

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isInvertible_pullback_iso_of_cocycle_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isInvertible_pullback_iso_of_cocycle_of_isPullback (solution)
