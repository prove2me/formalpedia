-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsFrameOn.pullbackLocalSection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/163af18b-e93e-5e35-afcc-8d1d1d5940da

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory Opposite AlgebraicGeometry TopologicalSpace CategoryTheory.MonoidalCategory"

namespace PicTanH

variable {X Y Z : Scheme.{u}}

theorem pullbackLocalSection_openImmersion (j : X ⟶ Y) [IsOpenImmersion j] (L : Y.Modules) (U : Y.Opens)
    (s : Γ(L, U)) :
    Scheme.Modules.pullbackLocalSection j s =
      ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app L).app (j ⁻¹ᵁ U)
        (((Scheme.Modules.restrictAdjunction j).unit.app L).app U s) := by
  rw [Scheme.Modules.pullbackLocalSection_def]
  have h := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction j)
    (Scheme.Modules.pullbackPushforwardAdjunction j) L

  change _ = ((Scheme.Modules.restrictAdjunction j).unit.app L ≫
    (Scheme.Modules.pushforward j).map ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app L)).app U s
  rw [show Scheme.Modules.restrictFunctorIsoPullback j =
    (Scheme.Modules.restrictAdjunction j).leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction j) from rfl, h]
  rfl

theorem pullbackComp_hom_app_app_pullbackLocalSection (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules) (U : Z.Opens)
    (s : Γ(L, U)) :
    ((Scheme.Modules.pullbackComp f g).hom.app L).app (f ⁻¹ᵁ (g ⁻¹ᵁ U))
        (Scheme.Modules.pullbackLocalSection f (Scheme.Modules.pullbackLocalSection g s)) =
      Scheme.Modules.pullbackLocalSection (f ≫ g) s := by
  have h := CategoryTheory.unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)) (Scheme.Modules.pullbackComp f g).inv L
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h

  have h' := congrArg (fun k => Scheme.Modules.Hom.app k U s) h
  simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, Adjunction.comp_unit_app,
    Scheme.Modules.pushforward_map_app, Functor.comp_obj,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.Hom.id_app, CategoryTheory.id_apply] at h'
  have key : Scheme.Modules.pullbackLocalSection f (Scheme.Modules.pullbackLocalSection g s) =
      ((Scheme.Modules.pullbackComp f g).inv.app L).app _ (Scheme.Modules.pullbackLocalSection (f ≫ g) s) := by
    rw [Scheme.Modules.pullbackLocalSection_def, Scheme.Modules.pullbackLocalSection_def,
      Scheme.Modules.pullbackLocalSection_def]
    exact h'
  rw [key]
  have h2 := congrArg (fun k => Scheme.Modules.Hom.app k ((f ≫ g) ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection (f ≫ g) s))
    ((Scheme.Modules.pullbackComp f g).inv_hom_id_app L)
  simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, Scheme.Modules.Hom.id_app,
    CategoryTheory.id_apply] at h2
  exact h2

end PicTanH

namespace PicTanH

variable {X Y : Scheme.{u}}

theorem isFrameOn_of_map {M : X.Modules} {U U' W : X.Opens} (h : U' ≤ U) (hW : W ≤ U') {t : Γ(M, U)}
    (ht : Scheme.Modules.IsFrameOn (M.presheaf.map (homOfLE h).op t) W) : Scheme.Modules.IsFrameOn t W := by
  intro W' hW'U hW'W
  have e : M.presheaf.map (homOfLE hW'U).op t =
      M.presheaf.map (homOfLE (hW'W.trans hW)).op (M.presheaf.map (homOfLE h).op t) := by
    rw [← CategoryTheory.comp_apply, ← Functor.map_comp]; rfl
  rw [e]
  exact ht (hW'W.trans hW) hW'W

theorem bijective_smul_congr {M : Y.Modules} {U₀ W₁ W₂ : Y.Opens} (h : W₁ = W₂) (h₁ : W₁ ≤ U₀) (h₂ : W₂ ≤ U₀)
    (r : Γ(M, U₀)) (hb : Function.Bijective fun g : Γ(Y, W₁) => g • M.presheaf.map (homOfLE h₁).op r) :
    Function.Bijective fun g : Γ(Y, W₂) => g • M.presheaf.map (homOfLE h₂).op r := by
  subst h; exact hb

theorem isFrameOn_pullbackLocalSection_congr {f f' : X ⟶ Y} (h : f = f') {L : Y.Modules} {U V : Y.Opens}
    (s : Γ(L, U)) (hs : Scheme.Modules.IsFrameOn (Scheme.Modules.pullbackLocalSection f s) (f ⁻¹ᵁ V)) :
    Scheme.Modules.IsFrameOn (Scheme.Modules.pullbackLocalSection f' s) (f' ⁻¹ᵁ V) := by
  subst h; exact hs

section Restrict

variable (j : X ⟶ Y) [IsOpenImmersion j] (L : Y.Modules)

theorem restrict_map_unit {U : Y.Opens} {W : X.Opens} (hW : W ≤ j ⁻¹ᵁ U) (s : Γ(L, U)) :
    (L.restrict j).presheaf.map (homOfLE hW).op
      (show Γ(L.restrict j, j ⁻¹ᵁ U) from ((Scheme.Modules.restrictAdjunction j).unit.app L).app U s) =
      (show Γ(L.restrict j, W) from
        L.presheaf.map (homOfLE ((j.image_mono hW).trans (j.image_preimage_le U))).op s) := by
  rw [Scheme.Modules.restrictAdjunction_unit_app_app]
  change (L.presheaf.map _ ≫ L.presheaf.map _) s = _
  rw [← Functor.map_comp]
  rfl

theorem isFrameOn_restrict_unit {U V : Y.Opens} {s : Γ(L, U)} (hs : Scheme.Modules.IsFrameOn s V) :
    Scheme.Modules.IsFrameOn
      (show Γ(L.restrict j, j ⁻¹ᵁ U) from ((Scheme.Modules.restrictAdjunction j).unit.app L).app U s) (j ⁻¹ᵁ V) := by
  intro W hWU hWV
  rw [restrict_map_unit j L hWU s]
  have hb := hs ((j.image_mono hWU).trans (j.image_preimage_le U))
    ((j.image_mono hWV).trans (j.image_preimage_le V))

  have : (fun g : Γ(X, W) => g • (show Γ(L.restrict j, W) from
      L.presheaf.map (homOfLE ((j.image_mono hWU).trans (j.image_preimage_le U))).op s)) =
      (fun g' : Γ(Y, j ''ᵁ W) => g' • L.presheaf.map
        (homOfLE ((j.image_mono hWU).trans (j.image_preimage_le U))).op s) ∘
        (fun g => (j.appIso W).inv.hom g) := rfl
  rw [this]
  exact hb.comp (ConcreteCategory.bijective_of_isIso (j.appIso W).inv)

end Restrict

end PicTanH

namespace PicTanH

variable {X Y : Scheme.{u}}

section Restrict2

variable (j : X ⟶ Y) [IsOpenImmersion j] (M : Y.Modules)

theorem image_preimage_eq_of_le {W : X.Opens} {W' : Y.Opens} (h : W' ≤ j ''ᵁ W) : j ''ᵁ (j ⁻¹ᵁ W') = W' := by
  rw [j.image_preimage_eq_opensRange_inf]
  exact inf_eq_right.2 (h.trans (by rw [← j.image_top_eq_opensRange]; exact j.image_mono le_top))

theorem isFrameOn_of_restrict_unit {U₀ : Y.Opens} (r : Γ(M, U₀)) {W : X.Opens}
    (h : Scheme.Modules.IsFrameOn
      (show Γ(M.restrict j, j ⁻¹ᵁ U₀) from ((Scheme.Modules.restrictAdjunction j).unit.app M).app U₀ r) W) :
    Scheme.Modules.IsFrameOn r (j ''ᵁ W) := by
  intro W' hW'U hW'W
  have hW''U : j ⁻¹ᵁ W' ≤ j ⁻¹ᵁ U₀ := fun _ hx => hW'U hx
  have hW''W : j ⁻¹ᵁ W' ≤ W := by
    intro x hx
    have : x ∈ j ⁻¹ᵁ (j ''ᵁ W) := hW'W hx
    rwa [j.preimage_image_eq] at this
  have hb := h hW''U hW''W
  rw [restrict_map_unit j M hW''U r] at hb
  have e : (fun g : Γ(X, j ⁻¹ᵁ W') => g • (show Γ(M.restrict j, j ⁻¹ᵁ W') from
      M.presheaf.map (homOfLE ((j.image_mono hW''U).trans (j.image_preimage_le U₀))).op r)) =
      (fun g' : Γ(Y, j ''ᵁ (j ⁻¹ᵁ W')) => g' • M.presheaf.map
        (homOfLE ((j.image_mono hW''U).trans (j.image_preimage_le U₀))).op r) ∘
        (fun g => (j.appIso (j ⁻¹ᵁ W')).inv.hom g) := rfl
  rw [e] at hb
  have hb' : Function.Bijective (fun g' : Γ(Y, j ''ᵁ (j ⁻¹ᵁ W')) => g' • M.presheaf.map
      (homOfLE ((j.image_mono hW''U).trans (j.image_preimage_le U₀))).op r) := by
    have := hb.comp (ConcreteCategory.bijective_of_isIso (j.appIso (j ⁻¹ᵁ W')).hom)
    convert this using 1
    all_goals try rfl
    funext g
    simp only [Function.comp_apply]
    rw [← CategoryTheory.comp_apply, Iso.hom_inv_id]
    rfl
  exact bijective_smul_congr (image_preimage_eq_of_le j (W := W) hW'W) _ hW'U r hb'

end Restrict2

end PicTanH

namespace PicTanH

variable {X Y : Scheme.{u}}

theorem iso_inv_hom_app_apply {M N : X.Modules} (e : M ≅ N) (U : X.Opens) (x : Γ(M, U)) :
    e.inv.app U (e.hom.app U x) = x := by
  rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]
  rfl

theorem isFrameOn_of_map_iso {M N : X.Modules} (e : M ≅ N) {U V : X.Opens} {s : Γ(M, U)}
    (h : Scheme.Modules.IsFrameOn (e.hom.app U s) V) : Scheme.Modules.IsFrameOn s V := by
  have := h.map_iso e.symm
  rwa [Iso.symm_hom, iso_inv_hom_app_apply] at this

theorem isFrameOn_pullbackLocalSection_congr' {f f' : X ⟶ Y} (h : f = f') {L : Y.Modules} {U : Y.Opens}
    {W : X.Opens} (s : Γ(L, U)) (hs : Scheme.Modules.IsFrameOn (Scheme.Modules.pullbackLocalSection f s) W) :
    Scheme.Modules.IsFrameOn (Scheme.Modules.pullbackLocalSection f' s) W := by
  subst h; exact hs

section OwnDomain

variable {L : Y.Modules} (U : Y.Opens) (s : Γ(L, U))

theorem exists_iso_of_isFrameOn_self (hs : Scheme.Modules.IsFrameOn s U) :
    ∃ e : (𝟙_ (U : Scheme.{u}).Modules) ≅ (Scheme.Modules.pullback U.ι).obj L,
      e.hom.app ⊤ (Scheme.Modules.unitSection ⊤) =
        ((Scheme.Modules.pullback U.ι).obj L).presheaf.map
          (homOfLE (show (⊤ : (U : Scheme.{u}).Opens) ≤ U.ι ⁻¹ᵁ U by rw [Scheme.Opens.ι_preimage_self])).op
          (Scheme.Modules.pullbackLocalSection U.ι s) := by

  have ht : Scheme.Modules.IsFrameOn (Scheme.Modules.pullbackLocalSection U.ι s) (U.ι ⁻¹ᵁ U) := by
    rw [pullbackLocalSection_openImmersion]
    exact (isFrameOn_restrict_unit U.ι L hs).map_iso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L)
  have hle : ∀ W : (U : Scheme.{u}).Opens, W ≤ U.ι ⁻¹ᵁ U := fun W => by
    rw [Scheme.Opens.ι_preimage_self]; exact le_top

  let fam : ((Scheme.Modules.pullback U.ι).obj L).sections :=
    PresheafOfModules.sectionsMk
      (fun W => ((Scheme.Modules.pullback U.ι).obj L).presheaf.map (homOfLE (hle W.unop)).op
        (Scheme.Modules.pullbackLocalSection U.ι s))
      (fun W W' i => by
        change (((Scheme.Modules.pullback U.ι).obj L).presheaf.map _ ≫
          ((Scheme.Modules.pullback U.ι).obj L).presheaf.map i) _ = _
        rw [← Functor.map_comp]
        rfl)
  obtain ⟨μ, hμdef⟩ : ∃ μ : (𝟙_ (U : Scheme.{u}).Modules) ⟶ (Scheme.Modules.pullback U.ι).obj L,
      μ = (((Scheme.Modules.pullback U.ι).obj L).unitHomEquiv).symm fam := ⟨_, rfl⟩
  have hμ : ∀ W : (U : Scheme.{u}).Opens, μ.app W (Scheme.Modules.unitSection W) =
      ((Scheme.Modules.pullback U.ι).obj L).presheaf.map (homOfLE (hle W)).op
        (Scheme.Modules.pullbackLocalSection U.ι s) := by
    intro W
    have h1 := SheafOfModules.unitHomEquiv_apply_coe _ μ (op W)
    rw [hμdef] at h1
    erw [Equiv.apply_symm_apply] at h1
    rw [hμdef]
    exact h1.symm

  haveI : IsIso μ := Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top μ (fun _ : Unit => ⊤) (iSup_const)
    (fun _ => Scheme.Modules.unitSection ⊤)
    (fun _ => ((Scheme.Modules.pullback U.ι).obj L).presheaf.map (homOfLE (hle ⊤)).op
      (Scheme.Modules.pullbackLocalSection U.ι s))
    (fun _ => Scheme.Modules.isFrameOn_unitSection _)
    (fun _ => by
      have := ht.map (homOfLE (hle ⊤))
      intro W hW _
      exact this hW (hle W))
    (fun _ => hμ ⊤)
  exact ⟨asIso μ, hμ ⊤⟩

end OwnDomain

end PicTanH

namespace PicTanH

variable {X Y : Scheme.{u}}

theorem isFrameOn_pullbackLocalSection_self (φ : X ⟶ Y) {L : Y.Modules} (U : Y.Opens) (s : Γ(L, U))
    (hs : Scheme.Modules.IsFrameOn s U) :
    Scheme.Modules.IsFrameOn (Scheme.Modules.pullbackLocalSection φ s) (φ ⁻¹ᵁ U) := by
  obtain ⟨e, he⟩ := exists_iso_of_isFrameOn_self U s hs

  have hle : (⊤ : (U : Scheme.{u}).Opens) ≤ U.ι ⁻¹ᵁ U := by rw [Scheme.Opens.ι_preimage_self]

  let Θ : (𝟙_ ((φ ⁻¹ᵁ U : X.Opens) : Scheme.{u}).Modules) ≅
      (Scheme.Modules.pullback (φ ∣_ U)).obj ((Scheme.Modules.pullback U.ι).obj L) :=
    (Scheme.Modules.pullbackTensorUnitObjIso (φ ∣_ U)).symm ≪≫ (Scheme.Modules.pullback (φ ∣_ U)).mapIso e
  have hΘ : Θ.hom.app ((φ ∣_ U) ⁻¹ᵁ ⊤) (Scheme.Modules.unitSection _) =
      Scheme.Modules.pullbackLocalSection (φ ∣_ U)
        (((Scheme.Modules.pullback U.ι).obj L).presheaf.map (homOfLE hle).op
          (Scheme.Modules.pullbackLocalSection U.ι s)) := by
    rw [← he, Scheme.Modules.pullbackLocalSection_app]
    change ((Scheme.Modules.pullbackTensorUnitObjIso (φ ∣_ U)).inv ≫ (Scheme.Modules.pullback (φ ∣_ U)).map e.hom).app _ _ = _
    rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
    congr 1
    have h825 := Scheme.Modules.pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection (φ ∣_ U) ⊤
    rw [← h825, iso_inv_hom_app_apply]
  have hA : Scheme.Modules.IsFrameOn (Scheme.Modules.pullbackLocalSection (φ ∣_ U)
      (((Scheme.Modules.pullback U.ι).obj L).presheaf.map (homOfLE hle).op
        (Scheme.Modules.pullbackLocalSection U.ι s))) ⊤ := by
    rw [← hΘ]
    exact (Scheme.Modules.isFrameOn_unitSection _).map_iso Θ

  have hB : Scheme.Modules.IsFrameOn (Scheme.Modules.pullbackLocalSection (φ ∣_ U)
      (Scheme.Modules.pullbackLocalSection U.ι s)) ⊤ := by
    rw [← Scheme.Modules.map_homOfLE_pullbackLocalSection] at hA
    exact isFrameOn_of_map _ le_top hA

  have hC : Scheme.Modules.IsFrameOn (Scheme.Modules.pullbackLocalSection ((φ ⁻¹ᵁ U).ι ≫ φ) s) ⊤ := by
    have := hB.map_iso ((Scheme.Modules.pullbackComp (φ ∣_ U) U.ι).app L)
    rw [Iso.app_hom] at this
    have key := pullbackComp_hom_app_app_pullbackLocalSection (φ ∣_ U) U.ι L U s
    exact isFrameOn_pullbackLocalSection_congr' (morphismRestrict_ι φ U) s (key ▸ this)

  have hD : Scheme.Modules.IsFrameOn (Scheme.Modules.pullbackLocalSection (φ ⁻¹ᵁ U).ι
      (Scheme.Modules.pullbackLocalSection φ s)) ⊤ := by
    have key := pullbackComp_hom_app_app_pullbackLocalSection (φ ⁻¹ᵁ U).ι φ L U s
    exact isFrameOn_of_map_iso ((Scheme.Modules.pullbackComp (φ ⁻¹ᵁ U).ι φ).app L) (key.symm ▸ hC)
  rw [pullbackLocalSection_openImmersion] at hD
  have hE := isFrameOn_of_map_iso ((Scheme.Modules.restrictFunctorIsoPullback (φ ⁻¹ᵁ U).ι).app _) hD
  have hF := isFrameOn_of_restrict_unit (φ ⁻¹ᵁ U).ι _ _ hE
  rwa [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι] at hF

end PicTanH

theorem solution {X Y : Scheme.{u}} (φ : X ⟶ Y)
    {L : Y.Modules} {U V : Y.Opens} {s : Γ(L, U)} (hs : Scheme.Modules.IsFrameOn s V) :
    Scheme.Modules.IsFrameOn (Scheme.Modules.pullbackLocalSection φ s) (φ ⁻¹ᵁ V) := by

  have hs' : Scheme.Modules.IsFrameOn (L.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s) (U ⊓ V) :=
    (hs.map _).mono inf_le_right
  have h := PicTanH.isFrameOn_pullbackLocalSection_self φ (U ⊓ V) _ hs'
  rw [← Scheme.Modules.map_homOfLE_pullbackLocalSection] at h
  have h2 : Scheme.Modules.IsFrameOn (Scheme.Modules.pullbackLocalSection φ s) (φ ⁻¹ᵁ (U ⊓ V)) :=
    PicTanH.isFrameOn_of_map _ le_rfl h
  apply Scheme.Modules.IsFrameOn.of_inf
  rw [inf_comm]
  exact h2

end S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection (solution)
