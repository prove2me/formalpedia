-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/4bdc09ea-15ae-5ea5-8c9b-cbfd31762b11

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Modules.Hom.app_smul Scheme.Modules.pullback Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme.Hom.image_top_eq_opensRange Spec Spec.map Scheme Scheme.Modules.Hom.id_app Scheme.Modules.restrictFunctorIsoPullback Scheme.Hom.appLE_appIso_inv_assoc Scheme.Hom.opensRange_of_isIso Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Modules.map_smul Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Modules.geomFibreH0Finrank"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul Modules.pullback Hom.id_app Hom Hom.appLE_comp_appLE Γ Modules.Hom.comp_app Modules.Hom Hom.image_top_eq_opensRange Modules.Hom.id_app Modules.restrictFunctorIsoPullback Hom.appLE_appIso_inv_assoc Hom.opensRange_of_isIso Hom.comp_app Modules.pullbackCongr Modules Opens Modules.map_smul restrict Modules.pullbackComp ΓSpecIso Modules.geomFibreH0Finrank"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext Hom.app_smul pullback presheaf Hom.comp_app Hom Hom.id_app restrictFunctorIsoPullback pullbackCongr restrict map_smul pullbackComp geomFibreH0Finrank"
namespace H0CartesianAux
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {Y : Scheme.{u}}

lemma map_map {O₁ O₂ O₃ : Y.Opens} (f : O₂ ⟶ O₁) (g : O₃ ⟶ O₂) (c : Γ(Y, O₁)) :
    Y.presheaf.map g.op (Y.presheaf.map f.op c) = Y.presheaf.map (g ≫ f).op c := by
  rw [op_comp, Functor.map_comp]; rfl

lemma map_irrel {O₁ O₂ : Y.Opens} (f g : O₂ ⟶ O₁) (c : Γ(Y, O₁)) :
    Y.presheaf.map f.op c = Y.presheaf.map g.op c := by
  rw [Subsingleton.elim f g]

lemma mmap_mmap (N : Y.Modules) {O₁ O₂ O₃ : Y.Opens} (f : O₂ ⟶ O₁) (g : O₃ ⟶ O₂) (c : Γ(N, O₁)) :
    N.presheaf.map g.op (N.presheaf.map f.op c) = N.presheaf.map (g ≫ f).op c := by
  rw [op_comp, Functor.map_comp]; rfl

lemma mmap_irrel (N : Y.Modules) {O₁ O₂ : Y.Opens} (f g : O₂ ⟶ O₁) (c : Γ(N, O₁)) :
    N.presheaf.map f.op c = N.presheaf.map g.op c := by
  rw [Subsingleton.elim f g]

lemma image_top_of_isIso {P₂ P₁ : Scheme.{u}} (θ : P₂ ⟶ P₁) [IsIso θ] : θ ''ᵁ ⊤ = ⊤ := by
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]

noncomputable def iUp {P₂ P₁ : Scheme.{u}} (θ : P₂ ⟶ P₁) [IsIso θ] : (⊤ : P₁.Opens) ⟶ θ ''ᵁ ⊤ :=
  homOfLE (image_top_of_isIso θ).symm.le
noncomputable def iDown {P₂ P₁ : Scheme.{u}} (θ : P₂ ⟶ P₁) [IsIso θ] : θ ''ᵁ ⊤ ⟶ (⊤ : P₁.Opens) :=
  homOfLE le_top

noncomputable def restrictTopEquiv {P₂ P₁ : Scheme.{u}} (θ : P₂ ⟶ P₁) [IsIso θ] (N : P₁.Modules) :
    Γ(N.restrict θ, ⊤) ≃+ Γ(N, ⊤) :=
  { toFun := fun x => N.presheaf.map (iUp θ).op (show Γ(N, θ ''ᵁ ⊤) from x)
    invFun := fun y => (show Γ(N, θ ''ᵁ ⊤) from N.presheaf.map (iDown θ).op y)
    left_inv := fun x => by
      change (N.presheaf.map (iUp θ).op ≫ N.presheaf.map (iDown θ).op) x = x
      rw [← Functor.map_comp, ← op_comp, Subsingleton.elim (iDown θ ≫ iUp θ) (𝟙 _), op_id,
        CategoryTheory.Functor.map_id]; rfl
    right_inv := fun y => by
      change (N.presheaf.map (iDown θ).op ≫ N.presheaf.map (iUp θ).op) y = y
      rw [← Functor.map_comp, ← op_comp, Subsingleton.elim (iUp θ ≫ iDown θ) (𝟙 _), op_id,
        CategoryTheory.Functor.map_id]; rfl
    map_add' := fun x y => (N.presheaf.map (iUp θ).op).hom.map_add x y }

lemma restrictTopEquiv_smul {P₂ P₁ : Scheme.{u}} (θ : P₂ ⟶ P₁) [IsIso θ] (N : P₁.Modules)
    (r : Γ(P₁, ⊤)) (x : Γ(N.restrict θ, ⊤)) :
    restrictTopEquiv θ N ((θ.appLE ⊤ ⊤ (by simp)) r • x) = r • restrictTopEquiv θ N x := by

  change N.presheaf.map (iUp θ).op (((θ.appIso ⊤).inv (θ.appLE ⊤ ⊤ (by simp) r)) • (show Γ(N, θ ''ᵁ ⊤) from x)) =
    r • N.presheaf.map (iUp θ).op (show Γ(N, θ ''ᵁ ⊤) from x)
  rw [Scheme.Modules.map_smul]
  congr 1
  change (θ.appLE ⊤ ⊤ (by simp) ≫ (θ.appIso ⊤).inv ≫ P₁.presheaf.map (iUp θ).op) r = r
  rw [Scheme.Hom.appLE_appIso_inv_assoc, ← Functor.map_comp, ← op_comp, Subsingleton.elim (_ ≫ _) (𝟙 _), op_id,
    CategoryTheory.Functor.map_id]
  rfl

end AlgebraicGeometry.Scheme.Modules.H0CartesianAux

open AlgebraicGeometry.Scheme.Modules.H0CartesianAux in
theorem solution
    {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    {X A' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (f' : A' ⟶ Spec (CommRingCat.of S'))
    (c : A' ⟶ X) (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom φ)))
    (M : X.Modules) (M' : A'.Modules) (e : (Scheme.Modules.pullback c).obj M ≅ M')
    (K : Type u) [Field K] (sK : S' →+* K) :
    Scheme.Modules.geomFibreH0Finrank f' M' K sK = Scheme.Modules.geomFibreH0Finrank f M K (sK.comp φ) := by
  classical

  set t₁ := Spec.map (CommRingCat.ofHom (sK.comp φ)) with ht₁
  set t₂ := Spec.map (CommRingCat.ofHom sK) with ht₂
  have ht : t₂ ≫ Spec.map (CommRingCat.ofHom φ) = t₁ := by rw [ht₁, ht₂, ← Spec.map_comp]; rfl
  let fst₁ := Limits.pullback.fst f t₁
  let snd₁ := Limits.pullback.snd f t₁
  let fst₂ := Limits.pullback.fst f' t₂
  let snd₂ := Limits.pullback.snd f' t₂
  let θ : Limits.pullback f' t₂ ⟶ Limits.pullback f t₁ :=
    Limits.pullback.lift (fst₂ ≫ c) snd₂ (by rw [Category.assoc, hc.w, ← Category.assoc, Limits.pullback.condition, Category.assoc, ht])
  let θ' : Limits.pullback f t₁ ⟶ Limits.pullback f' t₂ :=
    Limits.pullback.lift (hc.lift fst₁ (snd₁ ≫ t₂) (by rw [Limits.pullback.condition, Category.assoc, ht])) snd₁ (by rw [hc.lift_snd])
  have hθθ' : θ ≫ θ' = 𝟙 _ := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst, Category.id_comp]
      apply hc.hom_ext
      · rw [Category.assoc, hc.lift_fst, Limits.pullback.lift_fst]
      · rw [Category.assoc, hc.lift_snd, Limits.pullback.lift_snd_assoc, Limits.pullback.condition]
    · rw [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd, Category.id_comp]
  have hθ'θ : θ' ≫ θ = 𝟙 _ := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst, ← Category.assoc, Limits.pullback.lift_fst, hc.lift_fst, Category.id_comp]
    · rw [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd, Category.id_comp]
  haveI : IsIso θ := ⟨θ', hθθ', hθ'θ⟩
  have hθfst : fst₂ ≫ c = θ ≫ fst₁ := (Limits.pullback.lift_fst _ _ _).symm
  have hθsnd : θ ≫ snd₁ = snd₂ := Limits.pullback.lift_snd _ _ _

  let N₁ : (Limits.pullback f t₁).Modules := (Scheme.Modules.pullback fst₁).obj M
  let N₂ : (Limits.pullback f' t₂).Modules := (Scheme.Modules.pullback fst₂).obj M'
  let ξ : N₂ ≅ N₁.restrict θ :=
    (Scheme.Modules.pullback fst₂).mapIso e.symm ≪≫
      (Scheme.Modules.pullbackComp fst₂ c).app M ≪≫
      (Scheme.Modules.pullbackCongr hθfst).app M ≪≫
      ((Scheme.Modules.pullbackComp θ fst₁).app M).symm ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback θ).app N₁).symm

  let ξT : Γ(N₂, ⊤) ≃+ Γ(N₁.restrict θ, ⊤) :=
    { toFun := fun x => ξ.hom.app ⊤ x
      invFun := fun y => ξ.inv.app ⊤ y
      left_inv := fun x => by
        change (ξ.hom.app ⊤ ≫ ξ.inv.app ⊤) x = x
        rw [← Scheme.Modules.Hom.comp_app, ξ.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
      right_inv := fun y => by
        change (ξ.inv.app ⊤ ≫ ξ.hom.app ⊤) y = y
        rw [← Scheme.Modules.Hom.comp_app, ξ.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl
      map_add' := fun x y => map_add _ x y }
  let Ψ : Γ(N₂, ⊤) ≃+ Γ(N₁, ⊤) := ξT.trans (restrictTopEquiv θ N₁)

  have hΨ : ∀ (r : Γ(Limits.pullback f t₁, ⊤)) (x : Γ(N₂, ⊤)), Ψ ((θ.appLE ⊤ ⊤ (by simp)) r • x) = r • Ψ x := by
    intro r x
    change restrictTopEquiv θ N₁ (ξ.hom.app ⊤ ((θ.appLE ⊤ ⊤ (by simp)) r • x)) = r • restrictTopEquiv θ N₁ (ξ.hom.app ⊤ x)
    rw [Scheme.Modules.Hom.app_smul, restrictTopEquiv_smul]

  unfold Scheme.Modules.geomFibreH0Finrank
  letI alg₁ : Algebra K Γ(Limits.pullback f t₁, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ snd₁.appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI alg₂ : Algebra K Γ(Limits.pullback f' t₂, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ snd₂.appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI mod₁ : Module K Γ(N₁, ⊤) := Module.compHom _ (algebraMap K Γ(Limits.pullback f t₁, ⊤))
  letI mod₂ : Module K Γ(N₂, ⊤) := Module.compHom _ (algebraMap K Γ(Limits.pullback f' t₂, ⊤))
  have halg : ∀ a : K, (θ.appLE ⊤ ⊤ (by simp)) (algebraMap K Γ(Limits.pullback f t₁, ⊤) a) = algebraMap K Γ(Limits.pullback f' t₂, ⊤) a := by
    intro a
    change ((Scheme.ΓSpecIso (.of K)).inv ≫ snd₁.appLE ⊤ ⊤ le_top ≫ θ.appLE ⊤ ⊤ (by simp)) a =
      ((Scheme.ΓSpecIso (.of K)).inv ≫ snd₂.appLE ⊤ ⊤ le_top) a
    congr 2
    rw [Scheme.Hom.appLE_comp_appLE]

    have : ∀ (g₁ g₂ : Limits.pullback f' t₂ ⟶ Spec (CommRingCat.of K)) (h : g₁ = g₂) (e₁ : (⊤ : (Limits.pullback f' t₂).Opens) ≤ g₁ ⁻¹ᵁ ⊤)
        (e₂ : (⊤ : (Limits.pullback f' t₂).Opens) ≤ g₂ ⁻¹ᵁ ⊤), g₁.appLE ⊤ ⊤ e₁ = g₂.appLE ⊤ ⊤ e₂ := by
      intro g₁ g₂ h e₁ e₂; subst h; rfl
    rw [this _ _ hθsnd]
  let ΨK : Γ(N₂, ⊤) ≃ₗ[K] Γ(N₁, ⊤) :=
    { Ψ with
      map_smul' := fun a x => by
        change Ψ (algebraMap K Γ(Limits.pullback f' t₂, ⊤) a • x) = algebraMap K Γ(Limits.pullback f t₁, ⊤) a • Ψ x
        rw [← halg, hΨ] }
  exact ΨK.finrank_eq

end S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback (solution)
