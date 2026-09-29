-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_isInvertible_pullback_map_iso_unit_nonempty_pullback_iso_of_isDirectLimit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/1e394782-d50a-5446-af5c-fab0da22d3d1

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_map_iso_unit_nonempty_pullback_iso_of_isDirectLimit
p2m_attr_erase "instance" "PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback TwoChartCech.Sections.M0_moduleA"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option maxHeartbeats 3200000 in
theorem solution
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {P X : Scheme.{u}} (fP : P ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fP] [QuasiSeparated fP]
    (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX] [QuasiSeparated fX]
    (s : X ⟶ P) (hs : s ≫ fP = fX)
    (𝓛 : (Limits.pullback fP (Spec.map (CommRingCat.ofHom (g i)))).Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (htriv : Nonempty ((Scheme.Modules.pullback
        (Limits.pullback.map fX (Spec.map (CommRingCat.ofHom (g i))) fP (Spec.map (CommRingCat.ofHom (g i))) s (𝟙 _) (𝟙 _)
          (by rw [hs, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp]))).obj 𝓛 ≅
      SheafOfModules.unit (Limits.pullback fX (Spec.map (CommRingCat.ofHom (g i)))).ringCatSheaf)) :
    ∃ (k : ι) (hik : i ≤ k) (𝓛k : (Limits.pullback fP (Spec.map (CommRingCat.ofHom (φ i k hik)))).Modules),
      Scheme.Modules.IsInvertible 𝓛k ∧
      Nonempty ((Scheme.Modules.pullback
          (Limits.pullback.map fX (Spec.map (CommRingCat.ofHom (φ i k hik))) fP (Spec.map (CommRingCat.ofHom (φ i k hik))) s (𝟙 _) (𝟙 _)
            (by rw [hs, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp]))).obj 𝓛k ≅
        SheafOfModules.unit (Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i k hik)))).ringCatSheaf) ∧
      ∀ c : Limits.pullback fP (Spec.map (CommRingCat.ofHom (g i))) ⟶ Limits.pullback fP (Spec.map (CommRingCat.ofHom (φ i k hik))),
        c ≫ Limits.pullback.fst fP (Spec.map (CommRingCat.ofHom (φ i k hik))) = Limits.pullback.fst fP (Spec.map (CommRingCat.ofHom (g i))) →
        c ≫ Limits.pullback.snd fP (Spec.map (CommRingCat.ofHom (φ i k hik))) =
          Limits.pullback.snd fP (Spec.map (CommRingCat.ofHom (g i))) ≫ Spec.map (CommRingCat.ofHom (g k)) →
        Nonempty ((Scheme.Modules.pullback c).obj 𝓛k ≅ 𝓛) := by
  classical

  let σ : ∀ j : ι, Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (G j)) := fun j => Spec.map (CommRingCat.ofHom (g j))
  let τ : ∀ (j k : ι) (h : j ≤ k), Spec (CommRingCat.of (G k)) ⟶ Spec (CommRingCat.of (G j)) :=
    fun j k h => Spec.map (CommRingCat.ofHom (φ j k h))
  have hστ : ∀ (j k : ι) (h : j ≤ k), σ k ≫ τ j k h = σ j := by
    intro j k h
    show Spec.map (CommRingCat.ofHom (g k)) ≫ Spec.map (CommRingCat.ofHom (φ j k h)) = Spec.map (CommRingCat.ofHom (g j))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun x => hR.compatibility j k h x
  have hττ : ∀ (j k l : ι) (h : j ≤ k) (h' : k ≤ l), τ k l h' ≫ τ j k h = τ j l (h.trans h') := by
    intro j k l h h'
    show Spec.map (CommRingCat.ofHom (φ k l h')) ≫ Spec.map (CommRingCat.ofHom (φ j k h)) = Spec.map (CommRingCat.ofHom (φ j l _))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun x => DirectedSystem.map_map (f := fun i j h => ⇑(φ i j h)) h h' x

  obtain ⟨j, hij, 𝓛j, h𝓛j, H1⟩ :=
    Scheme.Modules.exists_isInvertible_nonempty_pullback_iso_of_isInvertible_of_isDirectLimit φ g hR i fP 𝓛 h𝓛

  let cP : pullback fP (σ i) ⟶ pullback fP (τ i j hij) :=
    pullback.lift (pullback.fst fP (σ i)) (pullback.snd fP (σ i) ≫ σ j)
      (by rw [pullback.condition, Category.assoc, hστ])
  have hcP1 : cP ≫ pullback.fst fP (τ i j hij) = pullback.fst fP (σ i) := pullback.lift_fst _ _ _
  have hcP2 : cP ≫ pullback.snd fP (τ i j hij) = pullback.snd fP (σ i) ≫ σ j := pullback.lift_snd _ _ _
  obtain ⟨e𝓛⟩ := H1 cP hcP1 hcP2

  let sj : pullback fX (τ i j hij) ⟶ pullback fP (τ i j hij) :=
    pullback.map fX (τ i j hij) fP (τ i j hij) s (𝟙 _) (𝟙 _) (by rw [hs, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])
  let sR : pullback fX (σ i) ⟶ pullback fP (σ i) :=
    pullback.map fX (σ i) fP (σ i) s (𝟙 _) (𝟙 _) (by rw [hs, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])
  have hsj1 : sj ≫ pullback.fst fP (τ i j hij) = pullback.fst fX (τ i j hij) ≫ s := pullback.lift_fst _ _ _
  have hsj2 : sj ≫ pullback.snd fP (τ i j hij) = pullback.snd fX (τ i j hij) ≫ 𝟙 _ := pullback.lift_snd _ _ _
  have hsR1 : sR ≫ pullback.fst fP (σ i) = pullback.fst fX (σ i) ≫ s := pullback.lift_fst _ _ _
  have hsR2 : sR ≫ pullback.snd fP (σ i) = pullback.snd fX (σ i) ≫ 𝟙 _ := pullback.lift_snd _ _ _
  let fXj : pullback fX (τ i j hij) ⟶ Spec (CommRingCat.of (G j)) := pullback.snd fX (τ i j hij)

  let a : pullback fXj (σ j) ⟶ pullback fX (τ i j hij) := pullback.fst fXj (σ j)
  let cXR : pullback fXj (σ j) ⟶ pullback fX (σ i) :=
    pullback.lift (a ≫ pullback.fst fX (τ i j hij)) (pullback.snd fXj (σ j))
      (by rw [Category.assoc, pullback.condition, ← Category.assoc]
          show (a ≫ fXj) ≫ τ i j hij = _
          rw [pullback.condition, Category.assoc, hστ])
  have hcXR1 : cXR ≫ pullback.fst fX (σ i) = a ≫ pullback.fst fX (τ i j hij) := pullback.lift_fst _ _ _
  have hcXR2 : cXR ≫ pullback.snd fX (σ i) = pullback.snd fXj (σ j) := pullback.lift_snd _ _ _
  have hkey : a ≫ sj = cXR ≫ sR ≫ cP := by
    apply pullback.hom_ext
    · rw [Category.assoc, hsj1, Category.assoc, Category.assoc, hcP1, hsR1, ← Category.assoc cXR, hcXR1, Category.assoc]
    · rw [Category.assoc, hsj2, Category.comp_id, Category.assoc, Category.assoc, hcP2, ← Category.assoc (sR), hsR2,
        Category.comp_id, ← Category.assoc, hcXR2]
      exact pullback.condition
  have hiso : Nonempty ((Scheme.Modules.pullback (pullback.fst fXj (σ j))).obj ((Scheme.Modules.pullback sj).obj 𝓛j) ≅
      (Scheme.Modules.pullback (pullback.fst fXj (σ j))).obj
        (SheafOfModules.unit (pullback fX (τ i j hij)).ringCatSheaf)) := by
    obtain ⟨eT⟩ := htriv
    exact ⟨(Scheme.Modules.pullbackComp a sj).app _ ≪≫ (Scheme.Modules.pullbackCongr hkey).app _ ≪≫
      ((Scheme.Modules.pullbackComp cXR (sR ≫ cP)).app _).symm ≪≫
      (Scheme.Modules.pullback cXR).mapIso (((Scheme.Modules.pullbackComp sR cP).app _).symm ≪≫
        (Scheme.Modules.pullback sR).mapIso e𝓛 ≪≫ eT) ≪≫
      Scheme.Modules.pullbackUnitIso cXR ≪≫ (Scheme.Modules.pullbackUnitIso a).symm⟩
  obtain ⟨k, hjk, ⟨eK⟩⟩ :=
    Scheme.Modules.exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit φ g hR j fXj
      ((Scheme.Modules.pullback sj).obj 𝓛j) (SheafOfModules.unit (pullback fX (τ i j hij)).ringCatSheaf)
      (Scheme.Modules.IsInvertible.pullback _ h𝓛j) (Scheme.Modules.isInvertible_unit _) hiso

  have hik : i ≤ k := hij.trans hjk
  let cPjk : pullback fP (τ i k hik) ⟶ pullback fP (τ i j hij) :=
    pullback.lift (pullback.fst fP (τ i k hik)) (pullback.snd fP (τ i k hik) ≫ τ j k hjk)
      (by rw [pullback.condition, Category.assoc, hττ])
  have hcPjk1 : cPjk ≫ pullback.fst fP (τ i j hij) = pullback.fst fP (τ i k hik) := pullback.lift_fst _ _ _
  have hcPjk2 : cPjk ≫ pullback.snd fP (τ i j hij) = pullback.snd fP (τ i k hik) ≫ τ j k hjk := pullback.lift_snd _ _ _
  let 𝓛k := (Scheme.Modules.pullback cPjk).obj 𝓛j
  refine ⟨k, hik, 𝓛k, Scheme.Modules.IsInvertible.pullback _ h𝓛j, ?_, ?_⟩
  ·
    let sk : pullback fX (τ i k hik) ⟶ pullback fP (τ i k hik) :=
      pullback.map fX (τ i k hik) fP (τ i k hik) s (𝟙 _) (𝟙 _) (by rw [hs, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])
    have hsk1 : sk ≫ pullback.fst fP (τ i k hik) = pullback.fst fX (τ i k hik) ≫ s := pullback.lift_fst _ _ _
    have hsk2 : sk ≫ pullback.snd fP (τ i k hik) = pullback.snd fX (τ i k hik) ≫ 𝟙 _ := pullback.lift_snd _ _ _
    let cXjk : pullback fX (τ i k hik) ⟶ pullback fX (τ i j hij) :=
      pullback.lift (pullback.fst fX (τ i k hik)) (pullback.snd fX (τ i k hik) ≫ τ j k hjk)
        (by rw [pullback.condition, Category.assoc, hττ])
    have hcX1 : cXjk ≫ pullback.fst fX (τ i j hij) = pullback.fst fX (τ i k hik) := pullback.lift_fst _ _ _
    have hcX2 : cXjk ≫ pullback.snd fX (τ i j hij) = pullback.snd fX (τ i k hik) ≫ τ j k hjk := pullback.lift_snd _ _ _
    let lam : pullback fX (τ i k hik) ⟶ pullback fXj (τ j k hjk) :=
      pullback.lift cXjk (pullback.snd fX (τ i k hik)) hcX2
    have hlam : lam ≫ pullback.fst fXj (τ j k hjk) = cXjk := pullback.lift_fst _ _ _
    have hsq : sk ≫ cPjk = (lam ≫ pullback.fst fXj (τ j k hjk)) ≫ sj := by
      rw [hlam]
      apply pullback.hom_ext
      · rw [Category.assoc, hcPjk1, hsk1, Category.assoc, hsj1, ← Category.assoc, hcX1]
      · rw [Category.assoc, hcPjk2, ← Category.assoc, hsk2, Category.comp_id, Category.assoc, hsj2, Category.comp_id, hcX2]
    show Nonempty ((Scheme.Modules.pullback sk).obj ((Scheme.Modules.pullback cPjk).obj 𝓛j) ≅ _)
    exact ⟨(Scheme.Modules.pullbackComp sk cPjk).app _ ≪≫ (Scheme.Modules.pullbackCongr hsq).app _ ≪≫
      ((Scheme.Modules.pullbackComp (lam ≫ pullback.fst fXj (τ j k hjk)) sj).app _).symm ≪≫
      ((Scheme.Modules.pullbackComp lam (pullback.fst fXj (τ j k hjk))).app _).symm ≪≫
      (Scheme.Modules.pullback lam).mapIso eK ≪≫
      (Scheme.Modules.pullbackComp lam (pullback.fst fXj (τ j k hjk))).app _ ≪≫
      Scheme.Modules.pullbackUnitIso _⟩
  ·
    intro c hc1 hc2
    have h1' : (c ≫ cPjk) ≫ pullback.fst fP (τ i j hij) = pullback.fst fP (σ i) := by rw [Category.assoc, hcPjk1, hc1]
    have h2' : (c ≫ cPjk) ≫ pullback.snd fP (τ i j hij) = pullback.snd fP (σ i) ≫ σ j := by
      rw [Category.assoc, hcPjk2, ← Category.assoc, hc2, Category.assoc, hστ]
    obtain ⟨e⟩ := H1 (c ≫ cPjk) h1' h2'
    exact ⟨((Scheme.Modules.pullbackComp c cPjk).app _) ≪≫ e⟩

end S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_map_iso_unit_nonempty_pullback_iso_of_isDirectLimit
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullback_map_iso_unit_nonempty_pullback_iso_of_isDirectLimit (solution)
