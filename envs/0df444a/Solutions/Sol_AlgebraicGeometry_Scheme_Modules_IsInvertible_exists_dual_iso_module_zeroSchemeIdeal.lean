-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_dual_iso_module_zeroSchemeIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a1d7a1bc-69d3-56e2-b2b6-058c0e179142

import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_range_moduleIota_app_and_injective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_of_locallySurjective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_dual_iso_module_zeroSchemeIdeal
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_dual_iso_module_zeroSchemeIdeal.AlgebraicGeometry"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.Modules.Hom Scheme Scheme.Modules Scheme.Modules.zeroSchemeIdeal Scheme.Modules.sectionDual Scheme.Modules.dual Scheme.Modules.IsInvertible"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul ringCatSheaf Hom Γ Modules.Hom affineOpens Modules Opens IdealSheafData Modules.zeroSchemeIdeal Modules.sectionDual Modules.dual Modules.IsInvertible"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext Hom.app_smul pushforward presheaf Hom isSheaf ofUnitSection ofUnitSection_injective ofUnitSection_smul restrictSection coeff coeffIdeal coeff_mem_coeffIdeal zeroSchemeIdeal sectionDual dual IsInvertible ihomEval map_ihomEval ihomEval_pre_app unitIsoSelf_hom_app ihomSectionsEquiv ihomSectionsEquiv_app_apply restrictUnitIso' restrictUnitIso_ι_hom_app_apply unitSection map_unitSection IsInvertible.isIso_of_locallySurjective IsInvertible.dual"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace SectionDualIso

variable {X : Scheme.{u}} {M : X.Modules}

abbrev sVal (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) : Γ(M, U) := s.app U (unitSection U)

lemma map_sVal (s : 𝟙_ X.Modules ⟶ M) {U V : X.Opens} (i : V ⟶ U) :
    M.presheaf.map i.op (sVal s U) = sVal s V := by
  have h := (NatTrans.naturality_apply s.mapPresheaf i.op (unitSection U)).symm
  rw [map_unitSection] at h
  exact h

lemma sectionDual_app (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) (t : Γ(Scheme.Modules.dual M, U)) :
    (sectionDual s).app U t = ihomEval M (𝟙_ X.Modules) U (sVal s U) t := by
  change (MonoidalClosed.unitIsoSelf (𝟙_ X.Modules)).hom.app U
      (((MonoidalClosed.pre s).app (𝟙_ X.Modules)).app U t) = _
  rw [unitIsoSelf_hom_app, ihomEval_pre_app]

lemma ofUnitSection_sectionDual_app (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens)
    (t : Γ(Scheme.Modules.dual M, U)) :
    ofUnitSection U ((sectionDual s).app U t) =
      coeff s U (ihomSectionsEquiv M (𝟙_ X.Modules) U t ≫ (restrictUnitIso' U.ι).hom) := by
  rw [sectionDual_app]
  have e1 := ihomSectionsEquiv_app_apply U t ⊤ (restrictSection s U)
  have e2 := restrictUnitIso_ι_hom_app_apply U ⊤
    ((ihomSectionsEquiv M (𝟙_ X.Modules) U t).app ⊤ (restrictSection s U))
  change _ = X.presheaf.map (eqToHom U.ι_image_top.symm).op
      ((restrictUnitIso' U.ι).hom.app ⊤
        ((ihomSectionsEquiv M (𝟙_ X.Modules) U t).app ⊤ (restrictSection s U)))
  rw [e2]
  change ihomEval M (𝟙_ X.Modules) U (sVal s U) t =
    (𝟙_ X.Modules).presheaf.map (eqToHom U.ι_image_top.symm).op
      ((ihomSectionsEquiv M (𝟙_ X.Modules) U t).app ⊤ (restrictSection s U))
  rw [e1, map_ihomEval]
  congr 1
  · exact (map_sVal s _).symm
  · change t = ((Scheme.Modules.dual M).presheaf.map _ ≫ (Scheme.Modules.dual M).presheaf.map _) t
    rw [← Functor.map_comp, ← op_comp,
      show (eqToHom U.ι_image_top.symm ≫ homOfLE (U.ι_image_le ⊤) : U ⟶ U) = 𝟙 U from
        Subsingleton.elim _ _, op_id, CategoryTheory.Functor.map_id]
    rfl

lemma sectionDual_app_mem (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (V : X.affineOpens) (t : Γ(Scheme.Modules.dual M, V.1)) :
    ofUnitSection V.1 ((sectionDual s).app V.1 t) ∈ (zeroSchemeIdeal s).ideal V := by
  rw [ofUnitSection_sectionDual_app]
  exact (hM.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq s).1 V (coeff_mem_coeffIdeal s V.1 _)

def pushUnit (I : X.IdealSheafData) : X.Modules :=
  (show SheafOfModules X.ringCatSheaf from
    (SheafOfModules.pushforward I.subschemeι.toRingCatSheafHom).obj
      (SheafOfModules.unit I.subscheme.ringCatSheaf))

def resMap (I : X.IdealSheafData) : 𝟙_ X.Modules ⟶ pushUnit I :=
  I.subschemeι.unitToPushforwardUnit

lemma resMap_app_moduleι_app (I : X.IdealSheafData) (U : X.Opens) (y : Γ(I.module, U)) :
    (resMap I).app U (I.moduleι.app U y) = 0 := by
  change ((kernel.ι I.subschemeι.unitToPushforwardUnit ≫ I.subschemeι.unitToPushforwardUnit).val.app
    (Opposite.op U)) y = 0
  rw [kernel.condition]
  first
    | rfl
    | simp

lemma resMap_app_sectionDual_app (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (U : X.Opens) (t : Γ(Scheme.Modules.dual M, U)) :
    (resMap (zeroSchemeIdeal s)).app U ((sectionDual s).app U t) = 0 := by
  change (sectionDual s ≫ resMap (zeroSchemeIdeal s)).app U t = 0
  refine TopCat.Presheaf.IsSheaf.section_ext (pushUnit (zeroSchemeIdeal s)).isSheaf
    (U := Opposite.op U) ?_
  intro x hx
  obtain ⟨V, hxV, hVU, -⟩ := hM.exists_restrict_iso hx
  refine ⟨V.1, hVU, hxV, ?_⟩
  rw [map_zero]
  have nat := (NatTrans.naturality_apply (sectionDual s ≫ resMap (zeroSchemeIdeal s)).mapPresheaf
    (homOfLE hVU).op t).symm
  refine nat.trans ?_
  change (resMap (zeroSchemeIdeal s)).app V.1 ((sectionDual s).app V.1
    ((Scheme.Modules.dual M).presheaf.map (homOfLE hVU).op t)) = 0
  obtain ⟨y, hy⟩ : (sectionDual s).app V.1
      ((Scheme.Modules.dual M).presheaf.map (homOfLE hVU).op t) ∈
        Set.range ((zeroSchemeIdeal s).moduleι.app V) := by
    rw [((zeroSchemeIdeal s).range_moduleIota_app_and_injective V).1]
    exact sectionDual_app_mem hM s V _
  rw [← hy]
  exact resMap_app_moduleι_app (zeroSchemeIdeal s) V.1 y

lemma sectionDual_comp_eq_zero (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M) :
    @CategoryStruct.comp (SheafOfModules X.ringCatSheaf) _
      (Scheme.Modules.dual M) (SheafOfModules.unit X.ringCatSheaf) _ (sectionDual s)
      (zeroSchemeIdeal s).subschemeι.unitToPushforwardUnit = 0 := by
  apply SheafOfModules.hom_ext
  ext U t
  first
    | exact resMap_app_sectionDual_app hM s U.unop t
    | simpa using resMap_app_sectionDual_app hM s U.unop t

lemma isIso_of_comp_moduleι_eq (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (I : X.IdealSheafData) (hI : zeroSchemeIdeal s = I) (hZ : I.IsInvertible)
    (ψ₀ : Scheme.Modules.dual M ⟶ I.module) (hψ₀ : ψ₀ ≫ I.moduleι = sectionDual s) :
    IsIso ψ₀ := by
  refine (IsInvertible.dual hM).1.isIso_of_locallySurjective hZ.isInvertible_module ψ₀ ?_
  intro U y x hx
  obtain ⟨V, hxV, hVU, ⟨τ⟩⟩ := hM.exists_restrict_iso hx
  refine ⟨V.1, hVU, hxV, ?_⟩
  obtain ⟨hspan, -⟩ := (hM.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq s).2 V τ
  rw [hI] at hspan
  have hmem : ofUnitSection V.1 (I.moduleι.app V.1 (I.module.presheaf.map (homOfLE hVU).op y)) ∈
      Ideal.span {coeff s V.1 τ.hom} := by
    rw [← hspan]
    have hr : I.moduleι.app V.1 (I.module.presheaf.map (homOfLE hVU).op y) ∈
        Set.range (I.moduleι.app V) := ⟨_, rfl⟩
    rw [(I.range_moduleIota_app_and_injective V).1] at hr
    exact hr
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : Γ(Scheme.Modules.dual M, V.1),
      ihomSectionsEquiv M (𝟙_ X.Modules) V.1 t₀ = τ.hom ≫ (restrictUnitIso' V.1.ι).inv :=
    ⟨_, AddEquiv.apply_symm_apply _ _⟩
  refine ⟨a • t₀, ?_⟩
  apply (I.range_moduleIota_app_and_injective V).2
  apply ofUnitSection_injective V.1
  change ofUnitSection V.1 ((ψ₀ ≫ I.moduleι).app V.1 (a • t₀)) =
    ofUnitSection V.1 (I.moduleι.app V.1 (I.module.presheaf.map (homOfLE hVU).op y))
  rw [← ha, hψ₀, Scheme.Modules.Hom.app_smul, ofUnitSection_smul, ofUnitSection_sectionDual_app,
    ht₀, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem exists_dual_iso (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (hZ : (zeroSchemeIdeal s).IsInvertible) :
    ∃ ψ : Scheme.Modules.dual M ≅ (zeroSchemeIdeal s).module,
      ψ.hom ≫ (zeroSchemeIdeal s).moduleι = sectionDual s := by
  have h0 := sectionDual_comp_eq_zero hM s
  let ψ₀ : Scheme.Modules.dual M ⟶ (zeroSchemeIdeal s).module :=
    kernel.lift (C := SheafOfModules X.ringCatSheaf)
      (zeroSchemeIdeal s).subschemeι.unitToPushforwardUnit (sectionDual s) h0
  have hψ₀ : ψ₀ ≫ (zeroSchemeIdeal s).moduleι = sectionDual s :=
    kernel.lift_ι (C := SheafOfModules X.ringCatSheaf)
      (zeroSchemeIdeal s).subschemeι.unitToPushforwardUnit (sectionDual s) h0
  haveI : IsIso ψ₀ := isIso_of_comp_moduleι_eq hM s _ rfl hZ ψ₀ hψ₀
  exact ⟨asIso ψ₀, hψ₀⟩

end SectionDualIso

end AlgebraicGeometry.Scheme.Modules

end

theorem solution
    {X : Scheme.{u}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (hZ : (Scheme.Modules.zeroSchemeIdeal s).IsInvertible) :
    ∃ ψ : Scheme.Modules.dual M ≅ (Scheme.Modules.zeroSchemeIdeal s).module,
      ψ.hom ≫ (Scheme.Modules.zeroSchemeIdeal s).moduleι = Scheme.Modules.sectionDual s :=
  AlgebraicGeometry.Scheme.Modules.SectionDualIso.exists_dual_iso hM s hZ

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_dual_iso_module_zeroSchemeIdeal
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_dual_iso_module_zeroSchemeIdeal (solution)
