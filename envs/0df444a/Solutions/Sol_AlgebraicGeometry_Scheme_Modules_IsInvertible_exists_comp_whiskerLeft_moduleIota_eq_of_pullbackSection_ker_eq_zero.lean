-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_comp_whiskerLeft_moduleIota_eq_of_pullbackSection_ker_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/6d1bf0e3-5a55-5aec-be9a-c6b6a52b7ad7

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_mono_whiskerLeft_moduleIota
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_range_moduleIota_app_and_injective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_mono_iff_injective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_whiskerLeft_app_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_rightUnitor_hom_app_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_comp_whiskerLeft_moduleIota_eq_of_pullbackSection_ker_eq_zero
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal'"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

namespace LiftAux

variable {X Z : Scheme.{u}} (f : Z ⟶ X) [IsClosedImmersion f] {L : X.Modules}

noncomputable abbrev φ : L ⊗ f.ker.module ⟶ L := (L ◁ f.ker.moduleι) ≫ (ρ_ L).hom

theorem mono_φ (hL : Scheme.Modules.IsInvertible L) : Mono (φ f (L := L)) := by
  haveI : Mono (L ◁ f.ker.moduleι) :=
    AlgebraicGeometry.Scheme.IdealSheafData.mono_whiskerLeft_moduleIota f.ker L
      ((AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible L).mpr hL)
  exact mono_comp _ _

theorem injective_φ_app (hL : Scheme.Modules.IsInvertible L) (U : X.Opens) : Function.Injective ((φ f (L := L)).app U) :=
  (AlgebraicGeometry.Scheme.Modules.Hom.mono_iff_injective _).mp (mono_φ f hL) U

theorem exists_local_lift (hL : Scheme.Modules.IsInvertible L) (s : 𝟙_ X.Modules ⟶ L) (hs : Scheme.Modules.pullbackSection f s = 0) (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U) (t : Γ(L ⊗ f.ker.module, U)),
      (φ f (L := L)).app U t = s.app U (Scheme.Modules.unitSection U) := by
  classical

  obtain ⟨U₀, hxU₀, ⟨eU₀⟩⟩ := hL.exists_trivialization x
  obtain ⟨e, he⟩ := AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit U₀ eU₀
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUU₀⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (U₀ : Set X) from hxU₀) U₀.isOpen

  let eU : Γ(L, U) := L.presheaf.map (homOfLE hUU₀).op e
  obtain ⟨a, ha⟩ := (he.bijective hUU₀ hUU₀).surjective (s.app U (Scheme.Modules.unitSection U))

  have S2 : (f.app U).hom a = 0 := by

    have heU : Scheme.Modules.IsFrameOn eU U₀ := he.map (homOfLE hUU₀)
    have hfeU := AlgebraicGeometry.Scheme.Modules.IsFrameOn.pullbackLocalSection f heU

    have h1 := congrArg (Scheme.Modules.pullbackLocalSection f) ha
    rw [Scheme.Modules.pullbackLocalSection_smul, Scheme.Modules.pullbackLocalSection_app] at h1

    have h2 : ((Scheme.Modules.pullback f).map s).app (f ⁻¹ᵁ U)
        (Scheme.Modules.pullbackLocalSection f (Scheme.Modules.unitSection U)) = 0 := by
      have e0 : (Scheme.Modules.pullback f).map s =
          (Scheme.Modules.pullbackUnitIso f).hom ≫ Scheme.Modules.pullbackSection f s := by
        simp only [Scheme.Modules.pullbackSection_def, Iso.hom_inv_id_assoc]
        rfl
      rw [e0]
      erw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, hs, Scheme.Modules.Hom.zero_app]
      rfl
    rw [h2] at h1

    have h3 := (hfeU.smul_eq_zero_iff (le_refl (f ⁻¹ᵁ U)) (fun y hy => hUU₀ hy) ((f.app U).hom a)).mp
    apply h3
    have e4 : ((Scheme.Modules.pullback f).obj L).presheaf.map (homOfLE (le_refl (f ⁻¹ᵁ U))).op
        (Scheme.Modules.pullbackLocalSection f eU) = Scheme.Modules.pullbackLocalSection f eU := by
      have : (homOfLE (le_refl (f ⁻¹ᵁ U))).op = 𝟙 _ := rfl
      rw [this, CategoryTheory.Functor.map_id]; rfl
    rw [e4]
    exact h1

  have h3 : a ∈ f.ker.ideal ⟨U, hU⟩ := by
    rw [Scheme.Hom.ker_apply f ⟨U, hU⟩]
    exact S2
  obtain ⟨hrange, -⟩ := AlgebraicGeometry.Scheme.IdealSheafData.range_moduleIota_app_and_injective f.ker ⟨U, hU⟩
  obtain ⟨b, hb⟩ : a ∈ Set.range (f.ker.moduleι.app U) := by
    change a ∈ Set.range (f.ker.moduleι.app (⟨U, hU⟩ : X.affineOpens)); rw [hrange]; exact h3

  have S4 : (φ f (L := L)).app U (Scheme.Modules.tensorSections eU b) = (show Γ(X, U) from f.ker.moduleι.app U b) • eU := by
    change ((L ◁ f.ker.moduleι) ≫ (ρ_ L).hom).app U (Scheme.Modules.tensorSections eU b) = _
    rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
      AlgebraicGeometry.Scheme.Modules.whiskerLeft_app_tensorSections,
      AlgebraicGeometry.Scheme.Modules.rightUnitor_hom_app_tensorSections]
  refine ⟨U, hxU, Scheme.Modules.tensorSections eU b, ?_⟩
  rw [S4, hb]
  exact ha

theorem φ_app_map (s : 𝟙_ X.Modules ⟶ L) {V W : X.Opens} (h : W ≤ V) (t : Γ(L ⊗ f.ker.module, V))
    (ht : (φ f (L := L)).app V t = s.app V (Scheme.Modules.unitSection V)) :
    (φ f (L := L)).app W ((L ⊗ f.ker.module).presheaf.map (homOfLE h).op t) = s.app W (Scheme.Modules.unitSection W) := by
  have nφ := (φ f (L := L)).mapPresheaf.naturality (homOfLE h).op
  have ns := s.mapPresheaf.naturality (homOfLE h).op
  have e1 := congrArg (fun k => k t) nφ
  have e2 := congrArg (fun k => k (Scheme.Modules.unitSection V)) ns
  simp only [CategoryTheory.comp_apply, Scheme.Modules.mapPresheaf_app, Opposite.unop_op] at e1 e2
  rw [e1, ht, ← e2, Scheme.Modules.map_unitSection]

theorem exists_global_lift (hL : Scheme.Modules.IsInvertible L) (s : 𝟙_ X.Modules ⟶ L) (hs : Scheme.Modules.pullbackSection f s = 0) :
    ∃ t : Γ(L ⊗ f.ker.module, ⊤), (φ f (L := L)).app ⊤ t = s.app ⊤ (Scheme.Modules.unitSection ⊤) := by
  classical

  choose U hxU tU htU using fun x : X => exists_local_lift f hL s hs x
  let FM : TopCat.Sheaf Ab X := ⟨(L ⊗ f.ker.module).presheaf, Scheme.Modules.isSheaf _⟩
  have hcov : (⊤ : X.Opens) ≤ iSup U := fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩

  have hcompat : TopCat.Presheaf.IsCompatible FM.1 U tU := by
    intro i j
    apply injective_φ_app f hL (U i ⊓ U j)
    change (φ f (L := L)).app _ ((L ⊗ f.ker.module).presheaf.map (homOfLE inf_le_left).op (tU i)) =
      (φ f (L := L)).app _ ((L ⊗ f.ker.module).presheaf.map (homOfLE inf_le_right).op (tU j))
    rw [φ_app_map f s inf_le_left (tU i) (htU i), φ_app_map f s inf_le_right (tU j) (htU j)]
  obtain ⟨t, ht, -⟩ := FM.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) hcov tU hcompat
  refine ⟨t, ?_⟩

  let FL : TopCat.Sheaf Ab X := ⟨L.presheaf, Scheme.Modules.isSheaf L⟩
  apply FL.eq_of_locally_eq' U ⊤ (fun i => homOfLE le_top) hcov
  intro i
  have hti : (L ⊗ f.ker.module).presheaf.map (homOfLE (le_top (a := U i))).op t = tU i := ht i
  have lhs := φ_app_map f s (le_top (a := U i)) t
  change L.presheaf.map (homOfLE le_top).op ((φ f (L := L)).app ⊤ t) =
    L.presheaf.map (homOfLE le_top).op (s.app ⊤ (Scheme.Modules.unitSection ⊤))

  have nφ := (φ f (L := L)).mapPresheaf.naturality (homOfLE (le_top (a := U i))).op
  have ns := s.mapPresheaf.naturality (homOfLE (le_top (a := U i))).op
  have e1 := congrArg (fun k => k t) nφ
  have e2 := congrArg (fun k => k (Scheme.Modules.unitSection ⊤)) ns
  simp only [CategoryTheory.comp_apply, Scheme.Modules.mapPresheaf_app, Opposite.unop_op] at e1 e2
  rw [← e1, hti, htU i, ← e2, Scheme.Modules.map_unitSection]

theorem exists_hom_of_section (hL : Scheme.Modules.IsInvertible L) (s : 𝟙_ X.Modules ⟶ L) (t : Γ(L ⊗ f.ker.module, ⊤))
    (ht : (φ f (L := L)).app ⊤ t = s.app ⊤ (Scheme.Modules.unitSection ⊤)) :
    ∃ s' : 𝟙_ X.Modules ⟶ L ⊗ f.ker.module, s' ≫ φ f (L := L) = s := by
  classical
  let M : X.Modules := L ⊗ f.ker.module

  let fam : SheafOfModules.sections M :=
    PresheafOfModules.sectionsMk
      (fun U => M.presheaf.map (homOfLE (le_top (a := U.unop))).op t)
      (by
        intro U V i
        change M.presheaf.map i (M.presheaf.map _ t) = _
        rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp]
        rfl)
  refine ⟨(SheafOfModules.unitHomEquiv M).symm fam, ?_⟩
  set s' : 𝟙_ X.Modules ⟶ M := (SheafOfModules.unitHomEquiv M).symm fam with hs'
  have hfam : ∀ U : X.Opens, s'.app U (Scheme.Modules.unitSection U) =
      M.presheaf.map (homOfLE (le_top (a := U))).op t := by
    intro U
    have h1 := SheafOfModules.unitHomEquiv_apply_coe M s' (Opposite.op U)
    rw [hs', Equiv.apply_symm_apply] at h1
    exact h1.symm
  apply Scheme.Modules.hom_ext
  intro U
  ext g

  have hg : g = (show Γ(X, U) from g) • Scheme.Modules.unitSection U :=
    (Scheme.Modules.smul_unitSection (show Γ(X, U) from g)).symm
  rw [hg, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul]
  congr 1
  rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, hfam]

  have nφ := (φ f (L := L)).mapPresheaf.naturality (homOfLE (le_top (a := U))).op
  have ns := s.mapPresheaf.naturality (homOfLE (le_top (a := U))).op
  have e1 := congrArg (fun k => k t) nφ
  have e2 := congrArg (fun k => k (Scheme.Modules.unitSection ⊤)) ns
  simp only [CategoryTheory.comp_apply, Scheme.Modules.mapPresheaf_app, Opposite.unop_op] at e1 e2
  rw [e1, ht, ← e2, Scheme.Modules.map_unitSection]

end LiftAux

theorem solution
    {X Z : Scheme.{u}} (f : Z ⟶ X) [IsClosedImmersion f]
    {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) (s : 𝟙_ X.Modules ⟶ L)
    (hs : Scheme.Modules.pullbackSection f s = 0) :
    ∃ s' : 𝟙_ X.Modules ⟶ L ⊗ f.ker.module, s' ≫ (L ◁ f.ker.moduleι) ≫ (ρ_ L).hom = s := by
  obtain ⟨t, ht⟩ := LiftAux.exists_global_lift f hL s hs
  exact LiftAux.exists_hom_of_section f hL s t ht

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_comp_whiskerLeft_moduleIota_eq_of_pullbackSection_ker_eq_zero
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_comp_whiskerLeft_moduleIota_eq_of_pullbackSection_ker_eq_zero (solution)
