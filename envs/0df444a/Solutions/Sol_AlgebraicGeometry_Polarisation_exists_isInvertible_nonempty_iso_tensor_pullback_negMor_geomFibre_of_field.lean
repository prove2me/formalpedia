-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.exists_isInvertible_nonempty_iso_tensor_pullback_negMor_geomFibre_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/f81bc332-b38c-53cc-a191-f4e1e218c23c

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_SheafOfModules_MonoidalV2
import Theorems.Thm_Algebra_exists_isDirectLimit_of_finitePresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_forall_nonempty_pullback_iso_of_isDirectLimit_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_forall_nonempty_pullback_iso_of_nonempty_pullback_iso_of_isDirectLimit_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_tensor_pullback_negMor_iso_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_iso_tensor_pullback_negMor_pullback_of_comp_eq
import Theorems.Thm_Module_FaithfullyFlat_exists_ringHom_comp_algebraMap_eq_of_finiteType_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_exists_isInvertible_nonempty_iso_tensor_pullback_negMor_geomFibre_of_field
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (hA : AbelianSchemePropertyBundle S f) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k)
    (K : Type) [Field K] (sK : S →+* K) (ι : k →+* K) (hι : ι.comp sk = sK)
    (𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom sK))).Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (e : Nonempty ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom sK)))).obj 𝓛 ≅
      𝓛₀ ⊗ (Scheme.Modules.pullback
        (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom sK))) (L.baseChange (Spec.map (CommRingCat.ofHom sK))))).obj 𝓛₀)) :
    ∃ 𝓛₁ : (pullback f (Spec.map (CommRingCat.ofHom sk))).Modules,
      Scheme.Modules.IsInvertible 𝓛₁ ∧
      Nonempty ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj 𝓛 ≅
        𝓛₁ ⊗ (Scheme.Modules.pullback
          (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom sk))) (L.baseChange (Spec.map (CommRingCat.ofHom sk))))).obj 𝓛₁) := by
  classical
  letI : Algebra k K := ι.toAlgebra
  have hιalg : algebraMap k K = ι := RingHom.algebraMap_toAlgebra ι
  haveI : IsProper f := hA.proper

  obtain ⟨J, _, _, _, G, _, _, hfp, t, c, hDS, hDL⟩ := Algebra.exists_isDirectLimit_of_finitePresentation k K
  let φ : ∀ i j : J, i ≤ j → G i →+* G j := fun i j h => (t i j h).toRingHom
  let g : ∀ i : J, G i →+* K := fun i => (c i).toRingHom
  haveI hDS' : DirectedSystem G fun i j h => ⇑(φ i j h) := hDS
  have hDL' : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i) := hDL

  let s : ∀ i : J, S →+* G i := fun i => (algebraMap k (G i)).comp sk
  have hs : ∀ (i j : J) (h : i ≤ j), (φ i j h).comp (s i) = s j := by
    intro i j h; ext x; simp [φ, s]
  have hsK : ∀ i, (g i).comp (s i) = sK := by
    intro i; ext x; simp [g, s, ← hι, hιalg]

  obtain ⟨j₁, 𝓜, h𝓜, H𝓜⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_isInvertible_forall_nonempty_pullback_iso_of_isDirectLimit_of_comp_eq
      f φ g hDL' s hs sK hsK 𝓛₀ h𝓛₀

  let ρ₁ : pullback f (Spec.map (CommRingCat.ofHom sK)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (s j₁))) :=
    pullback.lift (pullback.fst f _) (pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom (g j₁)))
      (by rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hsK j₁]; exact pullback.condition)
  have hρ₁a : ρ₁ ≫ pullback.fst f _ = pullback.fst f _ := pullback.lift_fst _ _ _
  have hρ₁b : ρ₁ ≫ pullback.snd f _ = pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom (g j₁)) := pullback.lift_snd _ _ _
  obtain ⟨iso1⟩ := H𝓜 ρ₁ hρ₁a hρ₁b
  obtain ⟨tr1⟩ := AlgebraicGeometry.Polarisation.nonempty_pullback_tensor_pullback_negMor_iso_of_comp_eq
    f L (s j₁) sK (g j₁) (hsK j₁) ρ₁ hρ₁a hρ₁b 𝓜
  obtain ⟨e₀⟩ := e

  let 𝓛₁' : (pullback f (Spec.map (CommRingCat.ofHom (s j₁)))).Modules :=
    (Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (s j₁))))).obj 𝓛
  let 𝓛₂' : (pullback f (Spec.map (CommRingCat.ofHom (s j₁)))).Modules :=
    𝓜 ⊗ (Scheme.Modules.pullback
      (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (s j₁)))) (L.baseChange (Spec.map (CommRingCat.ofHom (s j₁)))))).obj 𝓜
  have h₁' : Scheme.Modules.IsInvertible 𝓛₁' := h𝓛.pullback _
  have h₂' : Scheme.Modules.IsInvertible 𝓛₂' := h𝓜.tensor_monoidalV2 (h𝓜.pullback _)
  have hisoK : Nonempty ((Scheme.Modules.pullback ρ₁).obj 𝓛₁' ≅ (Scheme.Modules.pullback ρ₁).obj 𝓛₂') :=
    ⟨(Scheme.Modules.pullbackComp ρ₁ (pullback.fst f (Spec.map (CommRingCat.ofHom (s j₁))))).app 𝓛 ≪≫
      (Scheme.Modules.pullbackCongr hρ₁a).app 𝓛 ≪≫ e₀ ≪≫
      (iso1.symm ⊗ᵢ (Scheme.Modules.pullback
        (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom sK))) (L.baseChange (Spec.map (CommRingCat.ofHom sK))))).mapIso iso1.symm) ≪≫
      tr1.symm⟩

  obtain ⟨j₂, h12, Hiso⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_forall_nonempty_pullback_iso_of_nonempty_pullback_iso_of_isDirectLimit_of_comp_eq
      f φ g hDL' s hs sK hsK j₁ 𝓛₁' 𝓛₂' h₁' h₂' ρ₁ hρ₁a hρ₁b hisoK
  let ρ₂ : pullback f (Spec.map (CommRingCat.ofHom (s j₂))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (s j₁))) :=
    pullback.lift (pullback.fst f _) (pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom (φ j₁ j₂ h12)))
      (by rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hs j₁ j₂ h12]; exact pullback.condition)
  have hρ₂a : ρ₂ ≫ pullback.fst f _ = pullback.fst f _ := pullback.lift_fst _ _ _
  have hρ₂b : ρ₂ ≫ pullback.snd f _ = pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom (φ j₁ j₂ h12)) :=
    pullback.lift_snd _ _ _
  obtain ⟨iso2⟩ := Hiso ρ₂ hρ₂a hρ₂b
  obtain ⟨tr2⟩ := AlgebraicGeometry.Polarisation.nonempty_pullback_tensor_pullback_negMor_iso_of_comp_eq
    f L (s j₁) (s j₂) (φ j₁ j₂ h12) (hs j₁ j₂ h12) ρ₂ hρ₂a hρ₂b 𝓜

  have rootB : Nonempty ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (s j₂))))).obj 𝓛 ≅
      (Scheme.Modules.pullback ρ₂).obj 𝓜 ⊗ (Scheme.Modules.pullback
        (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (s j₂)))) (L.baseChange (Spec.map (CommRingCat.ofHom (s j₂)))))).obj
          ((Scheme.Modules.pullback ρ₂).obj 𝓜)) :=
    ⟨((Scheme.Modules.pullbackCongr hρ₂a).app 𝓛).symm ≪≫
      ((Scheme.Modules.pullbackComp ρ₂ (pullback.fst f (Spec.map (CommRingCat.ofHom (s j₁))))).app 𝓛).symm ≪≫ iso2 ≪≫ tr2⟩

  haveI : Nontrivial (G j₂) := (g j₂).domain_nontrivial
  haveI : Algebra.FinitePresentation k (G j₂) := hfp j₂
  obtain ⟨σ, hσ⟩ :=
    Module.FaithfullyFlat.exists_ringHom_comp_algebraMap_eq_of_finiteType_of_isAlgClosed (S := k) (G j₂) k (RingHom.id k)
  have hσ' : σ.comp (s j₂) = sk := by
    show σ.comp ((algebraMap k (G j₂)).comp sk) = sk
    rw [← RingHom.comp_assoc, hσ, RingHom.id_comp]
  let ρk : pullback f (Spec.map (CommRingCat.ofHom sk)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (s j₂))) :=
    pullback.lift (pullback.fst f _) (pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom σ))
      (by rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hσ']; exact pullback.condition)
  have hρka : ρk ≫ pullback.fst f _ = pullback.fst f _ := pullback.lift_fst _ _ _
  have hρkb : ρk ≫ pullback.snd f _ = pullback.snd f _ ≫ Spec.map (CommRingCat.ofHom σ) := pullback.lift_snd _ _ _

  refine ⟨(Scheme.Modules.pullback ρk).obj ((Scheme.Modules.pullback ρ₂).obj 𝓜), (h𝓜.pullback ρ₂).pullback ρk, ?_⟩
  exact AlgebraicGeometry.Polarisation.nonempty_iso_tensor_pullback_negMor_pullback_of_comp_eq
    f L (s j₂) sk σ hσ' ρk hρka hρkb 𝓛 ((Scheme.Modules.pullback ρ₂).obj 𝓜) rootB

end S_AlgebraicGeometry_Polarisation_exists_isInvertible_nonempty_iso_tensor_pullback_negMor_geomFibre_of_field
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_exists_isInvertible_nonempty_iso_tensor_pullback_negMor_geomFibre_of_field (solution)
