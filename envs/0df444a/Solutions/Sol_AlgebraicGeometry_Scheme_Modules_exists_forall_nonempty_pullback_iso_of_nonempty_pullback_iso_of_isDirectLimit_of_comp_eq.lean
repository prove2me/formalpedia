-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_forall_nonempty_pullback_iso_of_nonempty_pullback_iso_of_isDirectLimit_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/ace26991-34d7-53b2-91cf-8e86c86361bf

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_forall_nonempty_pullback_iso_of_nonempty_pullback_iso_of_isDirectLimit_of_comp_eq
p2m_attr_erase "instance" "PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace T3Sol

noncomputable def moveIso {X Y Z : Scheme.{u}} (κ : Z ⟶ Y) (ρ : Y ⟶ X) (σ : Z ⟶ X) (h : κ ≫ ρ = σ)
    {M₁ M₂ : X.Modules} (e : (Scheme.Modules.pullback ρ).obj M₁ ≅ (Scheme.Modules.pullback ρ).obj M₂) :
    (Scheme.Modules.pullback σ).obj M₁ ≅ (Scheme.Modules.pullback σ).obj M₂ :=
  ((Scheme.Modules.pullbackCongr h).app M₁).symm ≪≫
    ((Scheme.Modules.pullbackComp κ ρ).app M₁).symm ≪≫
    (Scheme.Modules.pullback κ).mapIso e ≪≫
    (Scheme.Modules.pullbackComp κ ρ).app M₂ ≪≫
    (Scheme.Modules.pullbackCongr h).app M₂

end T3Sol

theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) [QuasiCompact f] [QuasiSeparated f]
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {K : Type u} [CommRing K] (g : ∀ i, G i →+* K)
    (hK : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (s : ∀ i, S →+* G i) (hs : ∀ (i j : ι) (h : i ≤ j), (φ i j h).comp (s i) = s j)
    (sK : S →+* K) (hsK : ∀ i, (g i).comp (s i) = sK)
    (i₀ : ι) (𝓛₁ 𝓛₂ : (Limits.pullback f (Spec.map (CommRingCat.ofHom (s i₀)))).Modules)
    (h₁ : Scheme.Modules.IsInvertible 𝓛₁) (h₂ : Scheme.Modules.IsInvertible 𝓛₂)
    (ρ : Limits.pullback f (Spec.map (CommRingCat.ofHom sK)) ⟶ Limits.pullback f (Spec.map (CommRingCat.ofHom (s i₀))))
    (hρ₁ : ρ ≫ Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (s i₀))) = Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sK)))
    (hρ₂ : ρ ≫ Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (s i₀))) =
      Limits.pullback.snd f (Spec.map (CommRingCat.ofHom sK)) ≫ Spec.map (CommRingCat.ofHom (g i₀)))
    (hiso : Nonempty ((Scheme.Modules.pullback ρ).obj 𝓛₁ ≅ (Scheme.Modules.pullback ρ).obj 𝓛₂)) :
    ∃ (j : ι) (hij : i₀ ≤ j),
      ∀ ρ' : Limits.pullback f (Spec.map (CommRingCat.ofHom (s j))) ⟶ Limits.pullback f (Spec.map (CommRingCat.ofHom (s i₀))),
        ρ' ≫ Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (s i₀))) = Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (s j))) →
        ρ' ≫ Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (s i₀))) =
          Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (s j))) ≫ Spec.map (CommRingCat.ofHom (φ i₀ j hij)) →
        Nonempty ((Scheme.Modules.pullback ρ').obj 𝓛₁ ≅ (Scheme.Modules.pullback ρ').obj 𝓛₂) := by

  set π₀ := Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (s i₀))) with hπ₀
  have hSpecK : Spec.map (CommRingCat.ofHom sK) =
      Spec.map (CommRingCat.ofHom (g i₀)) ≫ Spec.map (CommRingCat.ofHom (s i₀)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hsK]

  let κ : Limits.pullback π₀ (Spec.map (CommRingCat.ofHom (g i₀))) ⟶ Limits.pullback f (Spec.map (CommRingCat.ofHom sK)) :=
    Limits.pullback.lift (Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _) (Limits.pullback.snd _ _)
      (by rw [Category.assoc, Limits.pullback.condition, hSpecK, ← Category.assoc, hπ₀, Limits.pullback.condition, Category.assoc])
  have hκ : κ ≫ ρ = Limits.pullback.fst π₀ (Spec.map (CommRingCat.ofHom (g i₀))) := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, hρ₁, Limits.pullback.lift_fst]
    · rw [Category.assoc, hρ₂, ← Category.assoc, Limits.pullback.lift_snd, hπ₀, Limits.pullback.condition]
  obtain ⟨e⟩ := hiso
  obtain ⟨j, hij, ⟨ej⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit
      φ g hK i₀ π₀ 𝓛₁ 𝓛₂ h₁ h₂ ⟨T3Sol.moveIso κ ρ _ hκ e⟩
  refine ⟨j, hij, fun ρ' hρ'₁ hρ'₂ => ?_⟩

  let lam : Limits.pullback f (Spec.map (CommRingCat.ofHom (s j))) ⟶
      Limits.pullback π₀ (Spec.map (CommRingCat.ofHom (φ i₀ j hij))) :=
    Limits.pullback.lift ρ' (Limits.pullback.snd _ _) (by rw [hπ₀, hρ'₂])
  have hlam : lam ≫ Limits.pullback.fst π₀ (Spec.map (CommRingCat.ofHom (φ i₀ j hij))) = ρ' :=
    Limits.pullback.lift_fst _ _ _
  exact ⟨T3Sol.moveIso lam _ ρ' hlam ej⟩

end S_AlgebraicGeometry_Scheme_Modules_exists_forall_nonempty_pullback_iso_of_nonempty_pullback_iso_of_isDirectLimit_of_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_forall_nonempty_pullback_iso_of_nonempty_pullback_iso_of_isDirectLimit_of_comp_eq (solution)
