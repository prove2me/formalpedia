-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_isInvertible_pullback_iso_of_milnorSquare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/e6831368-51d7-525a-92d0-26c5effca944

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_of_forall_exists_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare.AlgebraicGeometry TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Scheme.Modules.toPresheaf Scheme.Modules.Hom.app_smul Scheme.Modules.pullback Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Hom.germ_stalkMap_apply Scheme.Modules.Hom IsClosedImmersion.isClosedEmbedding RingedSpace.isUnit_res_basicOpen Scheme Scheme.Modules.Hom.id_app IsClosedImmersion exists_isAffineOpen_mem_and_subset Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Hom.preimage_iSup exists_preimage_eq Scheme.Hom.comp_preimage Scheme.Modules.map_smul RingedSpace Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.IsFrameOn Scheme.Modules.IsFrameOn.bijective_self Scheme.Modules.IsFrameOn.exists_isUnit_smul_eq Scheme.Modules.IsFrameOn.unit_smul"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.hom_ext Modules.toPresheaf mem_basicOpen Modules.Hom.app_smul forget Modules.pullback Hom.id_app Hom mk Γ Modules.Hom.comp_app Hom.germ_stalkMap_apply empty Modules.Hom Modules.Hom.id_app Hom.comp_app basicOpen Modules.pullbackCongr Modules Hom.preimage_iSup Opens Hom.comp_preimage Modules.map_smul basicOpen_le Modules.pullbackComp evaluation Modules.IsInvertible Modules.IsFrameOn Modules.IsFrameOn.bijective_self Modules.IsFrameOn.exists_isUnit_smul_eq Modules.IsFrameOn.unit_smul"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext toPresheaf pushforwardCongr Hom.app_smul pushforward pushforwardComp pullback presheaf Hom.comp_app Hom pushforward_map_app Hom.id_app pushforward_obj_presheaf_map pullbackCongr isSheaf pullbackPushforwardAdjunction map_smul pullbackComp IsInvertible IsFrameOn pullbackLocalSection pullbackLocalSection_add pullbackLocalSection_smul map_homOfLE_pullbackLocalSection pullbackLocalSection_app homEquiv_symm_app_pullbackLocalSection isIso_of_isFrameOn_of_iSup_eq_top isInvertible_of_forall_exists_isFrameOn exists_isFrameOn_of_pullback_iso_unit unit_app_comp_pullbackComp_inv IsFrameOn.bijective_self IsFrameOn.exists_isUnit_smul_eq IsFrameOn.unit_smul"
namespace MilnorPatch
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

section General

variable {X : Scheme.{u}}

lemma map_app {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : V ⟶ U) (s : Γ(M, U)) :
    N.presheaf.map i.op (φ.app U s) = φ.app V (M.presheaf.map i.op s) := by
  have h := (φ.mapPresheaf).naturality i.op
  exact (congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(M, U) → Γ(N, V))) h) s).symm

lemma map_map {M : X.Modules} {U V V' : X.Opens} (i : V ⟶ U) (j : V' ⟶ V) (s : Γ(M, U)) :
    M.presheaf.map j.op (M.presheaf.map i.op s) = M.presheaf.map (j ≫ i).op s := by
  rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp]
  rfl

lemma map_congr {M : X.Modules} {U V : X.Opens} (i j : V ⟶ U) (s : Γ(M, U)) :
    M.presheaf.map i.op s = M.presheaf.map j.op s := by
  rw [Subsingleton.elim i j]

lemma map_id' {M : X.Modules} {U : X.Opens} (i : U ⟶ U) (s : Γ(M, U)) : M.presheaf.map i.op s = s := by
  rw [Subsingleton.elim i (𝟙 U), op_id, M.presheaf.map_id]
  rfl

lemma iso_hom_inv_app_apply {M N : X.Modules} (e : M ≅ N) (U : X.Opens) (x : Γ(M, U)) :
    e.inv.app U (e.hom.app U x) = x := by
  rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]
  rfl

lemma iso_inv_hom_app_apply {M N : X.Modules} (e : M ≅ N) (U : X.Opens) (x : Γ(N, U)) :
    e.hom.app U (e.inv.app U x) = x := by
  rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]
  rfl

lemma comp_app_apply {M N K : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ K) (U : X.Opens) (x : Γ(M, U)) :
    (φ ≫ ψ).app U x = ψ.app U (φ.app U x) := by
  rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]

lemma subsingleton_bot (M : X.Modules) {U : X.Opens} (hU : U = ⊥) (s t : Γ(M, U)) : s = t := by
  subst hU
  let F : TopCat.Sheaf Ab X.carrier := ⟨M.presheaf, M.isSheaf⟩
  exact F.eq_of_locally_eq' (fun i : PEmpty.{u + 1} => (⊥ : X.Opens)) ⊥ (fun i => i.elim) bot_le s t
    (fun i => i.elim)

def secFunctor (U : X.Opens) : X.Modules ⥤ Type u :=
  (Scheme.Modules.toPresheaf X ⋙ (CategoryTheory.evaluation (Opens X)ᵒᵖ Ab.{u}).obj (op U)) ⋙
    CategoryTheory.forget Ab.{u}

scoped instance (U : X.Opens) : PreservesLimitsOfShape WalkingCospan (secFunctor (X := X) U) := by
  have i1 : PreservesLimitsOfShape WalkingCospan (Scheme.Modules.toPresheaf X) := inferInstance
  have i2 : PreservesLimitsOfShape WalkingCospan ((CategoryTheory.evaluation (Opens X)ᵒᵖ Ab.{u}).obj (op U)) :=
    inferInstance
  have i3 : PreservesLimitsOfShape WalkingCospan (CategoryTheory.forget Ab.{u}) := inferInstance
  have i12 : PreservesLimitsOfShape WalkingCospan
      (Scheme.Modules.toPresheaf X ⋙ (CategoryTheory.evaluation (Opens X)ᵒᵖ Ab.{u}).obj (op U)) :=
    @comp_preservesLimitsOfShape _ _ _ _ _ _ _ _ _ _ i1 i2
  exact @comp_preservesLimitsOfShape _ _ _ _ _ _ _ _ _ _ i12 i3

lemma secFunctor_map {M N : X.Modules} (f : M ⟶ N) (U : X.Opens) (s : Γ(M, U)) :
    (secFunctor U).map f s = f.app U s := rfl

section FibreProduct

variable {A B C : X.Modules} (a : A ⟶ C) (b : B ⟶ C) (U : X.Opens)

def secIsLimit : IsLimit (PullbackCone.mk ((secFunctor U).map (pullback.fst a b))
    ((secFunctor U).map (pullback.snd a b))
    (by rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition])) :=
  isLimitOfHasPullbackOfPreservesLimit (secFunctor U) a b

variable {U}

def mkSec (s : Γ(A, U)) (t : Γ(B, U)) (h : a.app U s = b.app U t) : Γ(Limits.pullback a b, U) :=
  (PullbackCone.IsLimit.lift (secIsLimit a b U) (TypeCat.ofHom fun _ : PUnit.{u + 1} => s)
    (TypeCat.ofHom fun _ => t) (by ext; exact h)) PUnit.unit

lemma fst_mkSec (s : Γ(A, U)) (t : Γ(B, U)) (h : a.app U s = b.app U t) :
    (pullback.fst a b).app U (mkSec a b s t h) = s :=
  congrArg (fun k => (ConcreteCategory.hom k) PUnit.unit)
    (PullbackCone.IsLimit.lift_fst (secIsLimit a b U) (TypeCat.ofHom fun _ : PUnit.{u + 1} => s)
      (TypeCat.ofHom fun _ => t) (by ext; exact h))

lemma snd_mkSec (s : Γ(A, U)) (t : Γ(B, U)) (h : a.app U s = b.app U t) :
    (pullback.snd a b).app U (mkSec a b s t h) = t :=
  congrArg (fun k => (ConcreteCategory.hom k) PUnit.unit)
    (PullbackCone.IsLimit.lift_snd (secIsLimit a b U) (TypeCat.ofHom fun _ : PUnit.{u + 1} => s)
      (TypeCat.ofHom fun _ => t) (by ext; exact h))

lemma sec_ext {x y : Γ(Limits.pullback a b, U)} (h₁ : (pullback.fst a b).app U x = (pullback.fst a b).app U y)
    (h₂ : (pullback.snd a b).app U x = (pullback.snd a b).app U y) : x = y :=
  congrArg (fun k => (ConcreteCategory.hom k) PUnit.unit)
    (PullbackCone.IsLimit.hom_ext (secIsLimit a b U) (k := TypeCat.ofHom fun _ : PUnit.{u + 1} => x)
      (l := TypeCat.ofHom fun _ => y) (by ext; exact h₁) (by ext; exact h₂))

lemma sec_condition (x : Γ(Limits.pullback a b, U)) :
    a.app U ((pullback.fst a b).app U x) = b.app U ((pullback.snd a b).app U x) := by
  rw [← comp_app_apply, ← comp_app_apply, pullback.condition]

end FibreProduct

end General

section Glue

variable {W V₁ V₂ Z : Scheme.{u}} {i₁ : V₁ ⟶ W} {i₂ : V₂ ⟶ W} {j₁ : Z ⟶ V₁} {j₂ : Z ⟶ V₂}
  (hsq : j₁ ≫ i₁ = j₂ ≫ i₂) (L₁ : V₁.Modules) (L₂ : V₂.Modules)
  (φ : (Modules.pullback j₁).obj L₁ ≅ (Modules.pullback j₂).obj L₂)

include hsq in
lemma preimage_eq (U : W.Opens) : j₂ ⁻¹ᵁ (i₂ ⁻¹ᵁ U) = j₁ ⁻¹ᵁ (i₁ ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hsq]

def tr (M : Z.Modules) (U : W.Opens) (x : Γ(M, j₁ ⁻¹ᵁ (i₁ ⁻¹ᵁ U))) : Γ(M, j₂ ⁻¹ᵁ (i₂ ⁻¹ᵁ U)) :=
  M.presheaf.map (eqToHom (preimage_eq hsq U)).op x

lemma tr_def (M : Z.Modules) (U : W.Opens) (x : Γ(M, j₁ ⁻¹ᵁ (i₁ ⁻¹ᵁ U))) :
    tr hsq M U x = M.presheaf.map (eqToHom (preimage_eq hsq U)).op x := rfl

def K (i₂ : V₂ ⟶ W) (j₂ : Z ⟶ V₂) (L₂ : V₂.Modules) : W.Modules :=
  (pushforward (j₂ ≫ i₂)).obj ((Modules.pullback j₂).obj L₂)

def aMap : (pushforward i₁).obj L₁ ⟶ K i₂ j₂ L₂ :=
  (pushforward i₁).map ((pullbackPushforwardAdjunction j₁).unit.app L₁) ≫
    (pushforwardComp j₁ i₁).hom.app _ ≫ (pushforward (j₁ ≫ i₁)).map φ.hom ≫ (pushforwardCongr hsq).hom.app _

def bMap : (pushforward i₂).obj L₂ ⟶ K i₂ j₂ L₂ :=
  (pushforward i₂).map ((pullbackPushforwardAdjunction j₂).unit.app L₂) ≫ (pushforwardComp j₂ i₂).hom.app _

lemma aMap_app (U : W.Opens) (s : Γ(L₁, i₁ ⁻¹ᵁ U)) :
    (aMap hsq L₁ L₂ φ).app U s = tr hsq _ U (φ.hom.app _ (pullbackLocalSection j₁ s)) := by
  simp only [aMap, Scheme.Modules.Hom.comp_app, pushforward_map_app, CategoryTheory.comp_apply]
  rfl

lemma bMap_app (U : W.Opens) (s : Γ(L₂, i₂ ⁻¹ᵁ U)) :
    (bMap L₂ : (pushforward i₂).obj L₂ ⟶ K i₂ j₂ L₂).app U s = pullbackLocalSection j₂ s := by
  simp only [bMap, Scheme.Modules.Hom.comp_app, pushforward_map_app, CategoryTheory.comp_apply]
  rfl

def glued : W.Modules := Limits.pullback (aMap hsq L₁ L₂ φ) (bMap (j₂ := j₂) L₂)

def pr₁ : glued hsq L₁ L₂ φ ⟶ (pushforward i₁).obj L₁ := pullback.fst _ _

def pr₂ : glued hsq L₁ L₂ φ ⟶ (pushforward i₂).obj L₂ := pullback.snd _ _

variable {hsq L₁ L₂ φ}

def c₁ {U : W.Opens} (s : Γ(glued hsq L₁ L₂ φ, U)) : Γ(L₁, i₁ ⁻¹ᵁ U) := (pr₁ hsq L₁ L₂ φ).app U s

def c₂ {U : W.Opens} (s : Γ(glued hsq L₁ L₂ φ, U)) : Γ(L₂, i₂ ⁻¹ᵁ U) := (pr₂ hsq L₁ L₂ φ).app U s

lemma c₁_def {U : W.Opens} (s : Γ(glued hsq L₁ L₂ φ, U)) : c₁ s = (pr₁ hsq L₁ L₂ φ).app U s := rfl
lemma c₂_def {U : W.Opens} (s : Γ(glued hsq L₁ L₂ φ, U)) : c₂ s = (pr₂ hsq L₁ L₂ φ).app U s := rfl

lemma cond {U : W.Opens} (s : Γ(glued hsq L₁ L₂ φ, U)) :
    tr hsq _ U (φ.hom.app _ (pullbackLocalSection j₁ (c₁ s))) = pullbackLocalSection j₂ (c₂ s) := by
  have h := sec_condition (aMap hsq L₁ L₂ φ) (bMap (j₂ := j₂) L₂) s
  rw [aMap_app, bMap_app] at h
  exact h

private def _root_.AlgebraicGeometry.Scheme.Modules.MilnorPatch.mk {U : W.Opens} (s₁ : Γ(L₁, i₁ ⁻¹ᵁ U)) (s₂ : Γ(L₂, i₂ ⁻¹ᵁ U))
    (h : tr hsq _ U (φ.hom.app _ (pullbackLocalSection j₁ s₁)) = pullbackLocalSection j₂ s₂) :
    Γ(glued hsq L₁ L₂ φ, U) :=
  mkSec (aMap hsq L₁ L₂ φ) (bMap (j₂ := j₂) L₂) s₁ s₂ (by rw [aMap_app, bMap_app]; exact h)

p2m_export "AlgebraicGeometry.Scheme.Modules.MilnorPatch" "mk"
@[scoped simp] lemma c₁_mk {U : W.Opens} (s₁ : Γ(L₁, i₁ ⁻¹ᵁ U)) (s₂ : Γ(L₂, i₂ ⁻¹ᵁ U))
    (h : tr hsq _ U (φ.hom.app _ (pullbackLocalSection j₁ s₁)) = pullbackLocalSection j₂ s₂) :
    c₁ (mk s₁ s₂ h) = s₁ :=
  fst_mkSec _ _ _ _ _

@[scoped simp] lemma c₂_mk {U : W.Opens} (s₁ : Γ(L₁, i₁ ⁻¹ᵁ U)) (s₂ : Γ(L₂, i₂ ⁻¹ᵁ U))
    (h : tr hsq _ U (φ.hom.app _ (pullbackLocalSection j₁ s₁)) = pullbackLocalSection j₂ s₂) :
    c₂ (mk s₁ s₂ h) = s₂ :=
  snd_mkSec _ _ _ _ _

private lemma _root_.AlgebraicGeometry.Scheme.Modules.MilnorPatch.ext {U : W.Opens} {s t : Γ(glued hsq L₁ L₂ φ, U)} (h₁ : c₁ s = c₁ t) (h₂ : c₂ s = c₂ t) : s = t :=
  sec_ext _ _ h₁ h₂

p2m_export "AlgebraicGeometry.Scheme.Modules.MilnorPatch" "ext"

lemma c₁_map {U V : W.Opens} (ι : V ⟶ U) (s : Γ(glued hsq L₁ L₂ φ, U)) :
    c₁ ((glued hsq L₁ L₂ φ).presheaf.map ι.op s) = L₁.presheaf.map ((Opens.map i₁.base).map ι).op (c₁ s) := by
  rw [c₁_def, c₁_def, ← map_app, pushforward_obj_presheaf_map]
  rfl

lemma c₂_map {U V : W.Opens} (ι : V ⟶ U) (s : Γ(glued hsq L₁ L₂ φ, U)) :
    c₂ ((glued hsq L₁ L₂ φ).presheaf.map ι.op s) = L₂.presheaf.map ((Opens.map i₂.base).map ι).op (c₂ s) := by
  rw [c₂_def, c₂_def, ← map_app, pushforward_obj_presheaf_map]
  rfl

lemma c₁_smul {U : W.Opens} (r : Γ(W, U)) (s : Γ(glued hsq L₁ L₂ φ, U)) : c₁ (r • s) = i₁.app U r • c₁ s := by
  rw [c₁_def, c₁_def, Scheme.Modules.Hom.app_smul]
  rfl

lemma c₂_smul {U : W.Opens} (r : Γ(W, U)) (s : Γ(glued hsq L₁ L₂ φ, U)) : c₂ (r • s) = i₂.app U r • c₂ s := by
  rw [c₂_def, c₂_def, Scheme.Modules.Hom.app_smul]
  rfl

end Glue

section Frames

variable {X Y : Scheme.{u}}

lemma subsingleton_bot_ring {U : X.Opens} (hU : U = ⊥) (f g : Γ(X, U)) : f = g := by
  subst hU
  exact X.sheaf.eq_of_locally_eq' (fun i : PEmpty.{u + 1} => (⊥ : X.Opens)) ⊥ (fun i => i.elim) bot_le f g
    (fun i => i.elim)

lemma isFrameOn_of_eq_bot {M : X.Modules} {U : X.Opens} (hU : U = ⊥) (s : Γ(M, U)) (V : X.Opens) :
    IsFrameOn s V := by
  intro W hWU _
  have hW : W = ⊥ := le_bot_iff.mp (hWU.trans (le_of_eq hU))
  exact ⟨fun g g' _ => subsingleton_bot_ring hW g g', fun x => ⟨0, subsingleton_bot M hW _ _⟩⟩

private lemma _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.bijective_self {M : X.Modules} {U : X.Opens} {s : Γ(M, U)} (h : IsFrameOn s U) :
    Function.Bijective fun g : Γ(X, U) => g • s := by
  have hb := h le_rfl le_rfl
  rwa [map_id'] at hb

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare.AlgebraicGeometry.Scheme.Modules.IsFrameOn.bijective_self" "AlgebraicGeometry.Scheme.Modules.IsFrameOn.bijective_self"

private lemma _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.exists_isUnit_smul_eq {M : X.Modules} {U : X.Opens} {s s' : Γ(M, U)} (hs : IsFrameOn s U)
    (hs' : IsFrameOn s' U) : ∃ u : Γ(X, U), IsUnit u ∧ s' = u • s := by
  obtain ⟨u, hu⟩ := hs.bijective_self.2 s'
  obtain ⟨v, hv⟩ := hs'.bijective_self.2 s
  change u • s = s' at hu
  change v • s' = s at hv
  refine ⟨u, ?_, hu.symm⟩
  rw [isUnit_iff_exists_inv']
  refine ⟨v, hs.bijective_self.1 ?_⟩
  change (v * u) • s = (1 : Γ(X, U)) • s
  rw [mul_smul, hu, hv, one_smul]

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare.AlgebraicGeometry.Scheme.Modules.IsFrameOn.exists_isUnit_smul_eq" "AlgebraicGeometry.Scheme.Modules.IsFrameOn.exists_isUnit_smul_eq"

private lemma _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.unit_smul {M : X.Modules} {U V : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s V) {u : Γ(X, U)}
    (hu : IsUnit u) : IsFrameOn (u • s) V := by
  intro W hWU hWV
  rw [Scheme.Modules.map_smul]
  set u' := X.presheaf.map (homOfLE hWU).op u with hu'def
  have hu' : IsUnit u' := hu.map _
  obtain ⟨w, hw⟩ := hu'.exists_left_inv
  have hbij : Function.Bijective (fun g : Γ(X, W) => g * u') := by
    refine ⟨fun g g' h => ?_, fun y => ⟨y * w, ?_⟩⟩
    · have h' := congrArg (· * w) h
      simp only [mul_assoc, mul_comm u' w, hw, mul_one] at h'
      exact h'
    · change y * w * u' = y
      rw [mul_assoc, hw, mul_one]
  have heq : (fun g : Γ(X, W) => g • (u' • M.presheaf.map (homOfLE hWU).op s)) =
      (fun g : Γ(X, W) => g • M.presheaf.map (homOfLE hWU).op s) ∘ (fun g => g * u') := by
    funext g
    simp only [Function.comp_apply, mul_smul]
  rw [heq]
  exact (hs hWU hWV).comp hbij

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare.AlgebraicGeometry.Scheme.Modules.IsFrameOn.unit_smul" "AlgebraicGeometry.Scheme.Modules.IsFrameOn.unit_smul"

lemma app_apply_map (f : X ⟶ Y) {U V : Y.Opens} (e : V ≤ U) (s : Γ(Y, U)) :
    f.app V (Y.presheaf.map (homOfLE e).op s) =
      X.presheaf.map (homOfLE (f.preimage_mono e)).op (f.app U s) := by
  have h := CategoryTheory.ConcreteCategory.congr_hom (f.naturality (homOfLE e).op) s
  rw [CategoryTheory.ConcreteCategory.comp_apply, CategoryTheory.ConcreteCategory.comp_apply] at h
  rw [h]
  rfl

lemma exists_preimage_eq (f : X ⟶ Y) [IsClosedImmersion f] (O : X.Opens) :
    ∃ U : Y.Opens, f ⁻¹ᵁ U = O ∧ ∀ y : Y, y ∉ Set.range f.base → y ∈ U := by
  have hce : Topology.IsClosedEmbedding f.base := IsClosedImmersion.isClosedEmbedding f
  have hc : IsClosed (f.base '' ((O : Set X)ᶜ)) := hce.isClosedMap _ O.isOpen.isClosed_compl
  refine ⟨⟨(f.base '' ((O : Set X)ᶜ))ᶜ, hc.isOpen_compl⟩, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      by_contra hxO
      exact hx ⟨x, hxO, rfl⟩
    · rintro hx ⟨x', hx', hxx'⟩
      obtain rfl := hce.injective hxx'
      exact hx' hx
  · rintro y hy ⟨x, -, rfl⟩
    exact hy ⟨x, rfl⟩

lemma preimage_inf_compl_range_eq_bot (f : X ⟶ Y) [IsClosedImmersion f] (O : Y.Opens) :
    f ⁻¹ᵁ (O ⊓ ⟨(Set.range f.base)ᶜ, (IsClosedImmersion.isClosedEmbedding f).isClosed_range.isOpen_compl⟩) = ⊥ := by
  ext x
  constructor
  · rintro ⟨-, hx⟩
    exact (hx ⟨x, rfl⟩).elim
  · intro hx
    exact hx.elim

lemma exists_isFrameOn_preimage (f : X ⟶ Y) [IsClosedImmersion f] {L : X.Modules} (hL : IsInvertible L) (y : Y) :
    ∃ U : Y.Opens, y ∈ U ∧ ∃ e : Γ(L, f ⁻¹ᵁ U), IsFrameOn e (f ⁻¹ᵁ U) := by
  by_cases hy : y ∈ Set.range f.base
  · obtain ⟨x, rfl⟩ := hy
    obtain ⟨O, hxO, ⟨eO⟩⟩ := hL.exists_trivialization x
    obtain ⟨e, he⟩ := exists_isFrameOn_of_pullback_iso_unit O eO
    obtain ⟨U, hU, -⟩ := exists_preimage_eq f O
    subst hU
    exact ⟨U, hxO, e, he⟩
  · obtain ⟨U, hU, hU'⟩ := exists_preimage_eq f ⊥
    exact ⟨U, hU' y hy, 0, isFrameOn_of_eq_bot hU 0 _⟩

lemma exists_unit_lift (f : X ⟶ Y) [IsClosedImmersion f] {O : Y.Opens} {y : Y} (hy : y ∈ O)
    (u : Γ(X, f ⁻¹ᵁ O)) (hu : IsUnit u) :
    ∃ (O' : Y.Opens) (hO' : O' ≤ O), y ∈ O' ∧ ∃ a : Γ(Y, O'), IsUnit a ∧
      f.app O' a = X.presheaf.map (homOfLE (f.preimage_mono hO')).op u := by
  by_cases hyr : y ∈ Set.range f.base
  · obtain ⟨x, rfl⟩ := hyr
    obtain ⟨O₁, hO₁, hxO₁, hO₁O⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := f.base x) (U := O) hy
    set u₁ := X.presheaf.map (homOfLE (f.preimage_mono hO₁O)).op u with hu₁def
    have hu₁ : IsUnit u₁ := hu.map _
    obtain ⟨a₁, ha₁⟩ := f.app_surjective O₁ hO₁ u₁
    have key : (f.stalkMap x).hom (Y.presheaf.germ O₁ (f.base x) hxO₁ a₁) =
        X.presheaf.germ (f ⁻¹ᵁ O₁) x hxO₁ u₁ := by
      rw [← ha₁]
      exact Scheme.Hom.germ_stalkMap_apply f O₁ x hxO₁ a₁
    have hgerm : IsUnit (Y.presheaf.germ O₁ (f.base x) hxO₁ a₁) := by
      apply (isUnit_map_iff (f.stalkMap x).hom _).mp
      rw [key]
      exact hu₁.map _
    have hxD : f.base x ∈ Y.basicOpen a₁ := (Y.mem_basicOpen a₁ _ hxO₁).mpr hgerm
    refine ⟨Y.basicOpen a₁, (Y.basicOpen_le a₁).trans hO₁O, hxD,
      Y.presheaf.map (homOfLE (Y.basicOpen_le a₁)).op a₁, ?_, ?_⟩
    · exact AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen _ a₁
    · rw [app_apply_map, ha₁, hu₁def, ← CategoryTheory.comp_apply, ← Functor.map_comp]
      rfl
  · refine ⟨O ⊓ ⟨(Set.range f.base)ᶜ, (IsClosedImmersion.isClosedEmbedding f).isClosed_range.isOpen_compl⟩,
      inf_le_left, ⟨hy, hyr⟩, 1, isUnit_one, ?_⟩
    exact subsingleton_bot_ring (preimage_inf_compl_range_eq_bot f O) _ _

lemma hom_ext_of_frames {M N : X.Modules} {f g : M ⟶ N} {ι : Type*} (𝒱 : ι → X.Opens) (hcov : ⨆ i, 𝒱 i = ⊤)
    (p : ∀ i, Γ(M, 𝒱 i)) (hp : ∀ i, IsFrameOn (p i) (𝒱 i)) (h : ∀ i, f.app _ (p i) = g.app _ (p i)) :
    f = g := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  let FN : TopCat.Sheaf Ab X.carrier := ⟨N.presheaf, N.isSheaf⟩
  have hcovU : U ≤ ⨆ i, U ⊓ 𝒱 i := by
    intro x hx
    have hx' : x ∈ (⨆ i, 𝒱 i : X.Opens) := by rw [hcov]; trivial
    rw [Opens.mem_iSup] at hx' ⊢
    obtain ⟨i, hi⟩ := hx'
    exact ⟨i, ⟨hx, hi⟩⟩
  apply FN.eq_of_locally_eq' (fun i => U ⊓ 𝒱 i) U (fun i => homOfLE inf_le_left) hcovU
  intro i
  change N.presheaf.map (homOfLE inf_le_left).op (f.app U s) = N.presheaf.map (homOfLE inf_le_left).op (g.app U s)
  rw [map_app, map_app]
  obtain ⟨c, hc⟩ := ((hp i) (inf_le_right : U ⊓ 𝒱 i ≤ 𝒱 i) inf_le_right).2
    (M.presheaf.map (homOfLE (inf_le_left : U ⊓ 𝒱 i ≤ U)).op s)
  change c • M.presheaf.map (homOfLE inf_le_right).op (p i) = _ at hc
  rw [← hc, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, ← map_app, ← map_app, h i]

end Frames

section Matched

variable {W V₁ V₂ Z : Scheme.{u}} {i₁ : V₁ ⟶ W} {i₂ : V₂ ⟶ W} {j₁ : Z ⟶ V₁} {j₂ : Z ⟶ V₂}
  (hsq : j₁ ≫ i₁ = j₂ ≫ i₂) {L₁ : V₁.Modules} (L₂ : V₂.Modules)
  (φ : (Modules.pullback j₁).obj L₁ ≅ (Modules.pullback j₂).obj L₂)

def trFun (U : W.Opens) (g : Γ(Z, j₁ ⁻¹ᵁ (i₁ ⁻¹ᵁ U))) : Γ(Z, j₂ ⁻¹ᵁ (i₂ ⁻¹ᵁ U)) :=
  Z.presheaf.map (eqToHom (preimage_eq hsq U)).op g

lemma trFun_def (U : W.Opens) (g : Γ(Z, j₁ ⁻¹ᵁ (i₁ ⁻¹ᵁ U))) :
    trFun hsq U g = Z.presheaf.map (eqToHom (preimage_eq hsq U)).op g := rfl

def ψ (U : W.Opens) (s₁ : Γ(L₁, i₁ ⁻¹ᵁ U)) : Γ((Modules.pullback j₂).obj L₂, j₂ ⁻¹ᵁ (i₂ ⁻¹ᵁ U)) :=
  tr hsq _ U (φ.hom.app _ (pullbackLocalSection j₁ s₁))

lemma ψ_def (U : W.Opens) (s₁ : Γ(L₁, i₁ ⁻¹ᵁ U)) :
    ψ hsq L₂ φ U s₁ = tr hsq _ U (φ.hom.app _ (pullbackLocalSection j₁ s₁)) := rfl

lemma ψ_smul (U : W.Opens) (g : Γ(V₁, i₁ ⁻¹ᵁ U)) (s₁ : Γ(L₁, i₁ ⁻¹ᵁ U)) :
    ψ hsq L₂ φ U (g • s₁) = trFun hsq U (j₁.app _ g) • ψ hsq L₂ φ U s₁ := by
  rw [ψ_def, ψ_def, pullbackLocalSection_smul, Scheme.Modules.Hom.app_smul, tr_def, tr_def,
    Scheme.Modules.map_smul]
  rfl

lemma ψ_add (U : W.Opens) (s₁ s₁' : Γ(L₁, i₁ ⁻¹ᵁ U)) :
    ψ hsq L₂ φ U (s₁ + s₁') = ψ hsq L₂ φ U s₁ + ψ hsq L₂ φ U s₁' := by
  rw [ψ_def, ψ_def, ψ_def, pullbackLocalSection_add, map_add, tr_def, tr_def, tr_def, map_add]

lemma ψ_map {U V : W.Opens} (hVU : V ≤ U) (s₁ : Γ(L₁, i₁ ⁻¹ᵁ U)) :
    ψ hsq L₂ φ V (L₁.presheaf.map (homOfLE (i₁.preimage_mono hVU)).op s₁) =
      ((Modules.pullback j₂).obj L₂).presheaf.map (homOfLE (j₂.preimage_mono (i₂.preimage_mono hVU))).op
        (ψ hsq L₂ φ U s₁) := by
  rw [ψ_def, ψ_def, ← map_homOfLE_pullbackLocalSection, ← map_app, tr_def, tr_def, map_map, map_map]
  rfl

lemma ψ_map_of_eq {U V : W.Opens} (hVU : V ≤ U) {s₁ : Γ(L₁, i₁ ⁻¹ᵁ U)} {s₂ : Γ(L₂, i₂ ⁻¹ᵁ U)}
    {t : Γ(Z, j₂ ⁻¹ᵁ (i₂ ⁻¹ᵁ U))} (h : ψ hsq L₂ φ U s₁ = t • pullbackLocalSection j₂ s₂) :
    ψ hsq L₂ φ V (L₁.presheaf.map (homOfLE (i₁.preimage_mono hVU)).op s₁) =
      Z.presheaf.map (homOfLE (j₂.preimage_mono (i₂.preimage_mono hVU))).op t •
        pullbackLocalSection j₂ (L₂.presheaf.map (homOfLE (i₂.preimage_mono hVU)).op s₂) := by
  rw [ψ_map hsq L₂ φ hVU, h, Scheme.Modules.map_smul, map_homOfLE_pullbackLocalSection]

lemma ψ_map_of_eq' {U V : W.Opens} (hVU : V ≤ U) {s₁ : Γ(L₁, i₁ ⁻¹ᵁ U)} {s₂ : Γ(L₂, i₂ ⁻¹ᵁ U)}
    (h : ψ hsq L₂ φ U s₁ = pullbackLocalSection j₂ s₂) :
    ψ hsq L₂ φ V (L₁.presheaf.map (homOfLE (i₁.preimage_mono hVU)).op s₁) =
      pullbackLocalSection j₂ (L₂.presheaf.map (homOfLE (i₂.preimage_mono hVU)).op s₂) := by
  rw [ψ_map hsq L₂ φ hVU, h, map_homOfLE_pullbackLocalSection]

lemma trFun_map {U V : W.Opens} (hVU : V ≤ U) (g : Γ(Z, j₁ ⁻¹ᵁ (i₁ ⁻¹ᵁ U))) :
    trFun hsq V (Z.presheaf.map (homOfLE (j₁.preimage_mono (i₁.preimage_mono hVU))).op g) =
      Z.presheaf.map (homOfLE (j₂.preimage_mono (i₂.preimage_mono hVU))).op (trFun hsq U g) := by
  rw [trFun_def, trFun_def, ← CategoryTheory.comp_apply, ← Functor.map_comp, ← CategoryTheory.comp_apply,
    ← Functor.map_comp]
  rfl

variable {L₂ φ}

lemma exists_unit (U : W.Opens) {e₁ : Γ(L₁, i₁ ⁻¹ᵁ U)} {e₂ : Γ(L₂, i₂ ⁻¹ᵁ U)}
    (he₁ : IsFrameOn e₁ (i₁ ⁻¹ᵁ U)) (he₂ : IsFrameOn e₂ (i₂ ⁻¹ᵁ U)) :
    ∃ u : Γ(Z, j₂ ⁻¹ᵁ (i₂ ⁻¹ᵁ U)), IsUnit u ∧ ψ hsq L₂ φ U e₁ = u • pullbackLocalSection j₂ e₂ := by
  have h2 : IsFrameOn (pullbackLocalSection j₂ e₂) (j₂ ⁻¹ᵁ (i₂ ⁻¹ᵁ U)) := he₂.pullbackLocalSection j₂
  have h1 : IsFrameOn (ψ hsq L₂ φ U e₁) (j₂ ⁻¹ᵁ (i₂ ⁻¹ᵁ U)) :=
    ((((he₁.pullbackLocalSection j₁).map_iso φ).map (eqToHom (preimage_eq hsq U))).mono
      (le_of_eq (preimage_eq hsq U)))
  exact h2.exists_isUnit_smul_eq h1

variable [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion j₂]

lemma exists_frames (hL₁ : IsInvertible L₁) (hL₂ : IsInvertible L₂) (w : W) :
    ∃ U : W.Opens, w ∈ U ∧ ∃ (e₁ : Γ(L₁, i₁ ⁻¹ᵁ U)) (e₂ : Γ(L₂, i₂ ⁻¹ᵁ U)),
      IsFrameOn e₁ (i₁ ⁻¹ᵁ U) ∧ IsFrameOn e₂ (i₂ ⁻¹ᵁ U) := by
  obtain ⟨U₁, hw₁, e₁, he₁⟩ := exists_isFrameOn_preimage i₁ hL₁ w
  obtain ⟨U₂, hw₂, e₂, he₂⟩ := exists_isFrameOn_preimage i₂ hL₂ w
  exact ⟨U₁ ⊓ U₂, ⟨hw₁, hw₂⟩, L₁.presheaf.map (homOfLE (i₁.preimage_mono inf_le_left)).op e₁,
    L₂.presheaf.map (homOfLE (i₂.preimage_mono inf_le_right)).op e₂,
    (he₁.map _).mono (i₁.preimage_mono inf_le_left), (he₂.map _).mono (i₂.preimage_mono inf_le_right)⟩

lemma exists_matched_frames (hL₁ : IsInvertible L₁) (hL₂ : IsInvertible L₂) (w : W) :
    ∃ U : W.Opens, w ∈ U ∧ ∃ (e₁ : Γ(L₁, i₁ ⁻¹ᵁ U)) (e₂ : Γ(L₂, i₂ ⁻¹ᵁ U)),
      IsFrameOn e₁ (i₁ ⁻¹ᵁ U) ∧ IsFrameOn e₂ (i₂ ⁻¹ᵁ U) ∧ ψ hsq L₂ φ U e₁ = pullbackLocalSection j₂ e₂ := by
  obtain ⟨U, hwU, e₁, e₂, he₁, he₂⟩ := exists_frames (i₁ := i₁) (i₂ := i₂) hL₁ hL₂ w
  obtain ⟨u, hu, hψ⟩ := exists_unit (hsq := hsq) (φ := φ) U he₁ he₂
  by_cases hw : w ∈ Set.range i₂.base
  · obtain ⟨v, rfl⟩ := hw
    obtain ⟨O', hO'le, hvO', a, ha, hau⟩ := exists_unit_lift j₂ (O := i₂ ⁻¹ᵁ U) hwU u hu
    obtain ⟨U₂, hU₂, -⟩ := exists_preimage_eq i₂ O'
    have h1 : i₁ ⁻¹ᵁ (U ⊓ U₂) ≤ i₁ ⁻¹ᵁ U := i₁.preimage_mono inf_le_left
    have h2 : i₂ ⁻¹ᵁ (U ⊓ U₂) ≤ O' := fun p hp => by rw [← hU₂]; exact hp.2
    have h2U : i₂ ⁻¹ᵁ (U ⊓ U₂) ≤ i₂ ⁻¹ᵁ U := i₂.preimage_mono inf_le_left
    have hvU₂ : v ∈ i₂ ⁻¹ᵁ U₂ := by rw [hU₂]; exact hvO'
    refine ⟨U ⊓ U₂, ⟨hwU, hvU₂⟩, L₁.presheaf.map (homOfLE h1).op e₁,
      V₂.presheaf.map (homOfLE h2).op a • L₂.presheaf.map (homOfLE h2U).op e₂,
      (he₁.map _).mono h1, ((he₂.map _).mono h2U).unit_smul (ha.map _), ?_⟩
    rw [ψ_map_of_eq hsq L₂ φ inf_le_left hψ, pullbackLocalSection_smul]
    congr 1

    have hu' : Z.presheaf.map (homOfLE (j₂.preimage_mono h2U)).op u =
        Z.presheaf.map (homOfLE (j₂.preimage_mono h2)).op
          (Z.presheaf.map (homOfLE (j₂.preimage_mono hO'le)).op u) := by
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
      rfl
    rw [hu', ← hau, app_apply_map]

  · have hbot := preimage_inf_compl_range_eq_bot i₂ U
    refine ⟨U ⊓ ⟨(Set.range i₂.base)ᶜ, (IsClosedImmersion.isClosedEmbedding i₂).isClosed_range.isOpen_compl⟩,
      ⟨hwU, hw⟩, L₁.presheaf.map (homOfLE (i₁.preimage_mono inf_le_left)).op e₁,
      L₂.presheaf.map (homOfLE (i₂.preimage_mono inf_le_left)).op e₂,
      (he₁.map _).mono (i₁.preimage_mono inf_le_left), (he₂.map _).mono (i₂.preimage_mono inf_le_left), ?_⟩
    apply subsingleton_bot
    rw [hbot]
    rfl

end Matched

section GluedFrame

variable {W V₁ V₂ Z : Scheme.{u}} {i₁ : V₁ ⟶ W} {i₂ : V₂ ⟶ W} {j₁ : Z ⟶ V₁} {j₂ : Z ⟶ V₂}
  {hsq : j₁ ≫ i₁ = j₂ ≫ i₂} {L₁ : V₁.Modules} {L₂ : V₂.Modules}
  {φ : (Modules.pullback j₁).obj L₁ ≅ (Modules.pullback j₂).obj L₂}

def Milnor (hsq : j₁ ≫ i₁ = j₂ ≫ i₂) (U : W.Opens) : Prop :=
  Function.Injective (fun f : Γ(W, U) => ((i₁.app U) f, (i₂.app U) f)) ∧
    ∀ (g₁ : Γ(V₁, i₁ ⁻¹ᵁ U)) (g₂ : Γ(V₂, i₂ ⁻¹ᵁ U)), trFun hsq U (j₁.app _ g₁) = j₂.app _ g₂ →
      ∃ f : Γ(W, U), (i₁.app U) f = g₁ ∧ (i₂.app U) f = g₂

lemma c₁_map' {U V : W.Opens} (hVU : V ≤ U) (s : Γ(glued hsq L₁ L₂ φ, U)) :
    c₁ ((glued hsq L₁ L₂ φ).presheaf.map (homOfLE hVU).op s) =
      L₁.presheaf.map (homOfLE (i₁.preimage_mono hVU)).op (c₁ s) :=
  c₁_map _ s

lemma c₂_map' {U V : W.Opens} (hVU : V ≤ U) (s : Γ(glued hsq L₁ L₂ φ, U)) :
    c₂ ((glued hsq L₁ L₂ φ).presheaf.map (homOfLE hVU).op s) =
      L₂.presheaf.map (homOfLE (i₂.preimage_mono hVU)).op (c₂ s) :=
  c₂_map _ s

theorem isFrameOn_mk {U : W.Opens} (hmil : ∀ V : W.Opens, V ≤ U → Milnor hsq V)
    {e₁ : Γ(L₁, i₁ ⁻¹ᵁ U)} {e₂ : Γ(L₂, i₂ ⁻¹ᵁ U)} (he₁ : IsFrameOn e₁ (i₁ ⁻¹ᵁ U))
    (he₂ : IsFrameOn e₂ (i₂ ⁻¹ᵁ U)) (h : ψ hsq L₂ φ U e₁ = pullbackLocalSection j₂ e₂) :
    IsFrameOn (mk e₁ e₂ h : Γ(glued hsq L₁ L₂ φ, U)) U := by
  intro V hVU _
  set e₁' := L₁.presheaf.map (homOfLE (i₁.preimage_mono hVU)).op e₁ with he₁'def
  set e₂' := L₂.presheaf.map (homOfLE (i₂.preimage_mono hVU)).op e₂ with he₂'def
  have hc₁ : c₁ ((glued hsq L₁ L₂ φ).presheaf.map (homOfLE hVU).op (mk e₁ e₂ h)) = e₁' := by
    rw [c₁_map', c₁_mk]
  have hc₂ : c₂ ((glued hsq L₁ L₂ φ).presheaf.map (homOfLE hVU).op (mk e₁ e₂ h)) = e₂' := by
    rw [c₂_map', c₂_mk]
  have he₁' : IsFrameOn e₁' (i₁ ⁻¹ᵁ V) := (he₁.map _).mono (i₁.preimage_mono hVU)
  have he₂' : IsFrameOn e₂' (i₂ ⁻¹ᵁ V) := (he₂.map _).mono (i₂.preimage_mono hVU)
  have h' : ψ hsq L₂ φ V e₁' = pullbackLocalSection j₂ e₂' := ψ_map_of_eq' hsq L₂ φ hVU h
  obtain ⟨hinj, hex⟩ := hmil V hVU
  constructor
  · intro g g' hgg'
    dsimp only at hgg'
    apply hinj
    have h₁ := congrArg c₁ hgg'
    have h₂ := congrArg c₂ hgg'
    rw [c₁_smul, c₁_smul, hc₁] at h₁
    rw [c₂_smul, c₂_smul, hc₂] at h₂
    exact Prod.ext (he₁'.bijective_self.1 h₁) (he₂'.bijective_self.1 h₂)
  · intro s
    obtain ⟨g₁, hg₁⟩ := he₁'.bijective_self.2 (c₁ s)
    obtain ⟨g₂, hg₂⟩ := he₂'.bijective_self.2 (c₂ s)
    change g₁ • e₁' = c₁ s at hg₁
    change g₂ • e₂' = c₂ s at hg₂
    have hagree : trFun hsq V (j₁.app _ g₁) = j₂.app _ g₂ := by
      have hc := cond s
      change ψ hsq L₂ φ V (c₁ s) = pullbackLocalSection j₂ (c₂ s) at hc
      rw [← hg₁, ← hg₂, ψ_smul, h', pullbackLocalSection_smul] at hc
      exact (he₂'.pullbackLocalSection j₂).bijective_self.1 hc
    obtain ⟨f, hf₁, hf₂⟩ := hex g₁ g₂ hagree
    refine ⟨f, ?_⟩
    dsimp only
    apply ext
    · rw [c₁_smul, hc₁, hf₁, hg₁]
    · rw [c₂_smul, hc₂, hf₂, hg₂]

end GluedFrame

section CompCongr

variable {P Y X : Scheme.{u}}

lemma pullbackComp_inv_app_app_pullbackLocalSection (g : P ⟶ Y) (f : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) :
    ((pullbackComp g f).inv.app M).app (g ⁻¹ᵁ (f ⁻¹ᵁ U)) (pullbackLocalSection (g ≫ f) s) =
      pullbackLocalSection g (pullbackLocalSection f s) := by
  have h := congrArg (fun k => (ConcreteCategory.hom k) s) (unit_app_comp_pullbackComp_inv g f M U)
  simp only [CategoryTheory.comp_apply] at h
  exact h

lemma pullbackComp_hom_app_app_pullbackLocalSection (g : P ⟶ Y) (f : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) :
    ((pullbackComp g f).hom.app M).app (g ⁻¹ᵁ (f ⁻¹ᵁ U)) (pullbackLocalSection g (pullbackLocalSection f s)) =
      pullbackLocalSection (g ≫ f) s := by
  rw [← pullbackComp_inv_app_app_pullbackLocalSection]
  exact iso_inv_hom_app_apply ((pullbackComp g f).app M) _ _

lemma pullbackCongr_hom_app_app_pullbackLocalSection {f g : P ⟶ X} (h : f = g) (M : X.Modules) (U : X.Opens)
    (s : Γ(M, U)) :
    ((pullbackCongr h).hom.app M).app (f ⁻¹ᵁ U) (pullbackLocalSection f s) =
      ((Modules.pullback g).obj M).presheaf.map (eqToHom (show f ⁻¹ᵁ U = g ⁻¹ᵁ U by rw [h])).op
        (pullbackLocalSection g s) := by
  subst h
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Scheme.Modules.Hom.id_app,
    eqToHom_refl, op_id, CategoryTheory.Functor.map_id]

end CompCongr

section Main

variable {W V₁ V₂ Z : Scheme.{u}} {i₁ : V₁ ⟶ W} {i₂ : V₂ ⟶ W} {j₁ : Z ⟶ V₁} {j₂ : Z ⟶ V₂}
  (hsq : j₁ ≫ i₁ = j₂ ≫ i₂) (L₁ : V₁.Modules) (L₂ : V₂.Modules)
  (φ : (Modules.pullback j₁).obj L₁ ≅ (Modules.pullback j₂).obj L₂)

def α₁ : (Modules.pullback i₁).obj (glued hsq L₁ L₂ φ) ⟶ L₁ :=
  ((pullbackPushforwardAdjunction i₁).homEquiv _ _).symm (pr₁ hsq L₁ L₂ φ)

def α₂ : (Modules.pullback i₂).obj (glued hsq L₁ L₂ φ) ⟶ L₂ :=
  ((pullbackPushforwardAdjunction i₂).homEquiv _ _).symm (pr₂ hsq L₁ L₂ φ)

lemma α₁_app {U : W.Opens} (s : Γ(glued hsq L₁ L₂ φ, U)) :
    (α₁ hsq L₁ L₂ φ).app (i₁ ⁻¹ᵁ U) (pullbackLocalSection i₁ s) = c₁ s :=
  homEquiv_symm_app_pullbackLocalSection i₁ _ s

lemma α₂_app {U : W.Opens} (s : Γ(glued hsq L₁ L₂ φ, U)) :
    (α₂ hsq L₁ L₂ φ).app (i₂ ⁻¹ᵁ U) (pullbackLocalSection i₂ s) = c₂ s :=
  homEquiv_symm_app_pullbackLocalSection i₂ _ s

variable [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion j₂]

theorem exists_isInvertible (hmil : ∀ U : W.Opens, Milnor hsq U) (hL₁ : IsInvertible L₁)
    (hL₂ : IsInvertible L₂) :
    ∃ (L : W.Modules), IsInvertible L ∧
      ∃ (α₁ : (Modules.pullback i₁).obj L ≅ L₁) (α₂ : (Modules.pullback i₂).obj L ≅ L₂),
        (Modules.pullback j₁).map α₁.hom ≫ φ.hom =
          ((pullbackComp j₁ i₁).app L).hom ≫ ((pullbackCongr hsq).app L).hom ≫
            ((pullbackComp j₂ i₂).app L).inv ≫ (Modules.pullback j₂).map α₂.hom := by

  have H := fun w : W => exists_matched_frames (hsq := hsq) (φ := φ) hL₁ hL₂ w
  choose U hwU e₁ e₂ he₁ he₂ hψ using H
  set L := glued hsq L₁ L₂ φ with hL

  let e : ∀ w : W, Γ(L, U w) := fun w => mk (e₁ w) (e₂ w) (hψ w)
  have hframe : ∀ w, IsFrameOn (e w) (U w) :=
    fun w => isFrameOn_mk (fun V _ => hmil V) (he₁ w) (he₂ w) (hψ w)
  have hcov : ⨆ w, U w = ⊤ := top_le_iff.mp fun w _ => Opens.mem_iSup.mpr ⟨w, hwU w⟩
  have hcov₁ : ⨆ w, i₁ ⁻¹ᵁ U w = ⊤ := by rw [← Scheme.Hom.preimage_iSup, hcov]; rfl
  have hcov₂ : ⨆ w, i₂ ⁻¹ᵁ U w = ⊤ := by rw [← Scheme.Hom.preimage_iSup, hcov]; rfl
  have hcov₁₂ : ⨆ w, j₁ ⁻¹ᵁ (i₁ ⁻¹ᵁ U w) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hcov₁]; rfl

  refine ⟨L, isInvertible_of_forall_exists_isFrameOn (fun w => ⟨U w, e w, hwU w, hframe w⟩), ?_⟩

  haveI hα₁ : IsIso (α₁ hsq L₁ L₂ φ) :=
    isIso_of_isFrameOn_of_iSup_eq_top (α₁ hsq L₁ L₂ φ) (fun w => i₁ ⁻¹ᵁ U w) hcov₁
      (fun w => pullbackLocalSection i₁ (e w)) (fun w => e₁ w)
      (fun w => (hframe w).pullbackLocalSection i₁) (fun w => he₁ w)
      (fun w => by rw [α₁_app]; exact c₁_mk _ _ _)
  haveI hα₂ : IsIso (α₂ hsq L₁ L₂ φ) :=
    isIso_of_isFrameOn_of_iSup_eq_top (α₂ hsq L₁ L₂ φ) (fun w => i₂ ⁻¹ᵁ U w) hcov₂
      (fun w => pullbackLocalSection i₂ (e w)) (fun w => e₂ w)
      (fun w => (hframe w).pullbackLocalSection i₂) (fun w => he₂ w)
      (fun w => by rw [α₂_app]; exact c₂_mk _ _ _)
  refine ⟨asIso (α₁ hsq L₁ L₂ φ), asIso (α₂ hsq L₁ L₂ φ), ?_⟩

  apply hom_ext_of_frames (fun w => j₁ ⁻¹ᵁ (i₁ ⁻¹ᵁ U w)) hcov₁₂
    (fun w => pullbackLocalSection j₁ (pullbackLocalSection i₁ (e w)))
    (fun w => ((hframe w).pullbackLocalSection i₁).pullbackLocalSection j₁)
  intro w

  have E : j₁ ⁻¹ᵁ (i₁ ⁻¹ᵁ U w) = j₂ ⁻¹ᵁ (i₂ ⁻¹ᵁ U w) := (preimage_eq hsq (U w)).symm

  have lhs : ((Modules.pullback j₁).map (asIso (α₁ hsq L₁ L₂ φ)).hom ≫ φ.hom).app _
      (pullbackLocalSection j₁ (pullbackLocalSection i₁ (e w))) =
      φ.hom.app _ (pullbackLocalSection j₁ (e₁ w)) := by
    rw [comp_app_apply, asIso_hom, ← pullbackLocalSection_app, α₁_app]
    exact congrArg _ (congrArg _ (c₁_mk _ _ _))

  have s1 : ((pullbackComp j₁ i₁).app L).hom.app _ (pullbackLocalSection j₁ (pullbackLocalSection i₁ (e w))) =
      pullbackLocalSection (j₁ ≫ i₁) (e w) := by
    rw [Iso.app_hom]
    exact pullbackComp_hom_app_app_pullbackLocalSection j₁ i₁ L (U w) (e w)
  have s2 : ((pullbackCongr hsq).app L).hom.app (j₁ ⁻¹ᵁ (i₁ ⁻¹ᵁ U w)) (pullbackLocalSection (j₁ ≫ i₁) (e w)) =
      ((Modules.pullback (j₂ ≫ i₂)).obj L).presheaf.map (eqToHom E).op (pullbackLocalSection (j₂ ≫ i₂) (e w)) := by
    rw [Iso.app_hom]
    exact pullbackCongr_hom_app_app_pullbackLocalSection hsq L (U w) (e w)
  have s3 : ((pullbackComp j₂ i₂).app L).inv.app (j₁ ⁻¹ᵁ (i₁ ⁻¹ᵁ U w))
      (((Modules.pullback (j₂ ≫ i₂)).obj L).presheaf.map (eqToHom E).op (pullbackLocalSection (j₂ ≫ i₂) (e w))) =
      ((Modules.pullback j₂).obj ((Modules.pullback i₂).obj L)).presheaf.map (eqToHom E).op
        (pullbackLocalSection j₂ (pullbackLocalSection i₂ (e w))) := by
    rw [Iso.app_inv, ← map_app, pullbackComp_inv_app_app_pullbackLocalSection]
    rfl
  have s4 : ((Modules.pullback j₂).map (asIso (α₂ hsq L₁ L₂ φ)).hom).app (j₁ ⁻¹ᵁ (i₁ ⁻¹ᵁ U w))
      (((Modules.pullback j₂).obj ((Modules.pullback i₂).obj L)).presheaf.map (eqToHom E).op
        (pullbackLocalSection j₂ (pullbackLocalSection i₂ (e w)))) =
      ((Modules.pullback j₂).obj L₂).presheaf.map (eqToHom E).op (pullbackLocalSection j₂ (e₂ w)) := by
    rw [← map_app, asIso_hom, ← pullbackLocalSection_app, α₂_app]
    exact congrArg _ (congrArg _ (c₂_mk _ _ _))

  have rhs : (((pullbackComp j₁ i₁).app L).hom ≫ ((pullbackCongr hsq).app L).hom ≫
      ((pullbackComp j₂ i₂).app L).inv ≫ (Modules.pullback j₂).map (asIso (α₂ hsq L₁ L₂ φ)).hom).app _
      (pullbackLocalSection j₁ (pullbackLocalSection i₁ (e w))) =
      ((Modules.pullback j₂).obj L₂).presheaf.map (eqToHom E).op (pullbackLocalSection j₂ (e₂ w)) := by
    erw [comp_app_apply, comp_app_apply, comp_app_apply]
    erw [s1, s2, s3, s4]
  rw [lhs]
  erw [rhs]
  rw [← hψ w, ψ_def, tr_def, map_map, map_id']

end Main

end AlgebraicGeometry.Scheme.Modules.MilnorPatch
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare.AlgebraicGeometry.Scheme.Modules.MilnorPatch"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare.AlgebraicGeometry.Scheme.Modules"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare.AlgebraicGeometry"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare.AlgebraicGeometry.Scheme.Modules.MilnorPatch"

open _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare.AlgebraicGeometry.Scheme.Modules in

theorem solution
    {W V₁ V₂ Z : Scheme.{u}} (i₁ : V₁ ⟶ W) (i₂ : V₂ ⟶ W) (j₁ : Z ⟶ V₁) (j₂ : Z ⟶ V₂)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion j₂] (hsq : j₁ ≫ i₁ = j₂ ≫ i₂)
    (hmil : ∀ U : W.Opens,
      Function.Injective (fun f : Γ(W, U) => ((i₁.app U) f, (i₂.app U) f)) ∧
        ∀ (g₁ : Γ(V₁, i₁ ⁻¹ᵁ U)) (g₂ : Γ(V₂, i₂ ⁻¹ᵁ U)),
          Z.presheaf.map
              (eqToHom (show j₂ ⁻¹ᵁ (i₂ ⁻¹ᵁ U) = j₁ ⁻¹ᵁ (i₁ ⁻¹ᵁ U) by
                rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hsq])).op
            ((j₁.app (i₁ ⁻¹ᵁ U)) g₁) = (j₂.app (i₂ ⁻¹ᵁ U)) g₂ →
          ∃ f : Γ(W, U), (i₁.app U) f = g₁ ∧ (i₂.app U) f = g₂)
    (L₁ : V₁.Modules) (hL₁ : Scheme.Modules.IsInvertible L₁)
    (L₂ : V₂.Modules) (hL₂ : Scheme.Modules.IsInvertible L₂)
    (φ : (Scheme.Modules.pullback j₁).obj L₁ ≅ (Scheme.Modules.pullback j₂).obj L₂) :
    ∃ (L : W.Modules), Scheme.Modules.IsInvertible L ∧
      ∃ (α₁ : (Scheme.Modules.pullback i₁).obj L ≅ L₁) (α₂ : (Scheme.Modules.pullback i₂).obj L ≅ L₂),
        (Scheme.Modules.pullback j₁).map α₁.hom ≫ φ.hom =
          ((Scheme.Modules.pullbackComp j₁ i₁).app L).hom ≫ ((Scheme.Modules.pullbackCongr hsq).app L).hom ≫
            ((Scheme.Modules.pullbackComp j₂ i₂).app L).inv ≫ (Scheme.Modules.pullback j₂).map α₂.hom :=
  AlgebraicGeometry.Scheme.Modules.MilnorPatch.exists_isInvertible hsq L₁ L₂ φ hmil hL₁ hL₂

end S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_iso_of_milnorSquare (solution)
