-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_pullbackAlong_iso_unit_of_smallExtension_of_locIsoOnBase_faces
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/64058d7d-a9c0-5aa1-a482-b0f0d7811093

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing
import Theorems.Thm_AlgebraicGeometry_isPullback_lift_fst_comp_fst_snd_comp_fst_prodStr
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_pullbackAlong_iso_unit_of_smallExtension_of_locIsoOnBase_faces
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintype AlgebraicGeometry.Scheme.OrderedOpenFamily.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedOpenFamily.instLinearOrder AlgebraicGeometry.Scheme.OrderedOpenFamily.instFintypeIdx CochainCx.Bounded.abGrp CochainCx.Bounded.modR PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj"
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.injEq AlgebraicGeometry.Scheme.OrderedOpenFamily.mk.sizeOf_spec CochainCx.Bounded.mk.sizeOf_spec CochainCx.Bounded.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply"
p2m_attr_erase "simp" "IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard"

namespace Ws23RC

universe u

noncomputable def pullbackComp₃ {X Y Z W : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W) (M : W.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback c).obj M)) ≅
      (Scheme.Modules.pullback (a ≫ b ≫ c)).obj M :=
  (Scheme.Modules.pullback a).mapIso ((Scheme.Modules.pullbackComp b c).app M) ≪≫ (Scheme.Modules.pullbackComp a (b ≫ c)).app M

noncomputable def pullbackInvHomIso {X Y : Scheme.{u}} (e : X ≅ Y) (M : Y.Modules) :
    (Scheme.Modules.pullback e.inv).obj ((Scheme.Modules.pullback e.hom).obj M) ≅ M :=
  (Scheme.Modules.pullbackComp e.inv e.hom).app M ≪≫ (Scheme.Modules.pullbackCongr e.inv_hom_id).app M ≪≫
    (Scheme.Modules.pullbackId Y).app M

theorem one_coe_congr {S : Type} [CommRing S] {A Z : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {b₁ b₂ : Z ⟶ Spec (CommRingCat.of S)} (hb : b₁ = b₂) : (L.one b₁).1 = (L.one b₂).1 := by
  subst hb; rfl

theorem comp_one_coe {S : Type} [CommRing S] {A Z Z' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (t : Z ⟶ Spec (CommRingCat.of S)) (ψ : Z' ⟶ Z) : ψ ≫ (L.one t).1 = (L.one (ψ ≫ t)).1 := by
  have := congrArg Subtype.val (L.one_natural t (ψ ≫ t) ψ rfl)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
  exact this

end Ws23RC

theorem solution
    {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (M : RigidifiedLineBundle (prodStr f f) ((L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) f)

    (h₁ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift
          (pullback.lift (L.one (prodStr f f)).1 (pullback.fst f f) (by rw [(L.one _).2]))
          (pullback.snd f f)
          (by rw [pullback.lift_fst_assoc, (L.one _).2]; exact pullback.condition))).obj M.L) (𝟙_ _))

    (h₂ : LocIsoOnBase (prodStr f f)
      ((Scheme.Modules.pullback
        (pullback.lift
          (pullback.lift (pullback.fst f f) (L.one (prodStr f f)).1 (by rw [(L.one _).2]))
          (pullback.snd f f)
          (by rw [pullback.lift_fst_assoc]; exact pullback.condition))).obj M.L) (𝟙_ _))
    (T' T : Type) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [CommRing T] [Nontrivial T]
    (p : T' →+* T) (hp : Function.Surjective p) (hsmall : RingHom.ker p * IsLocalRing.maximalIdeal T' = ⊥)
    (s : Spec (CommRingCat.of T') ⟶ A)
    (hs : Nonempty ((M.pullbackAlong
        (⟨Spec.map (CommRingCat.ofHom p) ≫ s, rfl⟩ : SchemeHomOver ((Spec.map (CommRingCat.ofHom p) ≫ s) ≫ f) f)).L ≅
      (RigidifiedLineBundle.unit (c := prodStr f f) (ε := (L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) _).L)) :
    Nonempty ((M.pullbackAlong (⟨s, rfl⟩ : SchemeHomOver (s ≫ f) f)).L ≅
      (RigidifiedLineBundle.unit (c := prodStr f f) (ε := (L.prod L).one (𝟙 (Spec (CommRingCat.of S)))) _).L) := by
  classical
  obtain ⟨iT⟩ := hs
  letI : Algebra T' T := p.toAlgebra

  let σ : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of S) := s ≫ f
  let f₁ := pullback.snd f σ
  let g₁ := pullback.fst f σ
  let L₁ : RelativeGroupLaw T' f₁ := L.baseChange σ
  have hA₁ : AbelianSchemePropertyBundle T' f₁ := hA.of_isPullback (IsPullback.of_hasPullback f σ)

  let π : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of T') := Spec.map (CommRingCat.ofHom (algebraMap T' T))
  let f₀ := pullback.snd f₁ π
  let g := pullback.fst f₁ π
  have hg : IsPullback g f₀ f₁ (Spec.map (CommRingCat.ofHom (algebraMap T' T))) := IsPullback.of_hasPullback f₁ π
  let L₀ : RelativeGroupLaw T (pullback.snd f₁ π) := L₁.baseChange π

  have hβ := AlgebraicGeometry.isPullback_lift_fst_comp_fst_snd_comp_fst_prodStr f σ
  let e : pullback f₁ f₁ ≅ pullback (prodStr f f) σ := hβ.isoPullback
  have he₁ : e.hom ≫ pullback.fst _ _ = pullback.lift (pullback.fst f₁ f₁ ≫ g₁) (pullback.snd f₁ f₁ ≫ g₁)
      (by rw [Category.assoc, Category.assoc, (IsPullback.of_hasPullback f σ).w, ← Category.assoc, pullback.condition,
          Category.assoc]) := hβ.isoPullback_hom_fst
  have he₂ : e.hom ≫ pullback.snd _ _ = pullback.fst f₁ f₁ ≫ f₁ := hβ.isoPullback_hom_snd

  let N := (M.pullbackAlong (⟨s, rfl⟩ : SchemeHomOver (s ≫ f) f)).L
  let M₈ : (pullback f₁ f₁).Modules := (Scheme.Modules.pullback e.hom).obj N
  have hM₈ : Scheme.Modules.IsInvertible M₈ := (M.pullbackAlong (⟨s, rfl⟩ : SchemeHomOver (s ≫ f) f)).isInvertible.pullback _

  have hkm : RingHom.ker (algebraMap T' T) ≤ IsLocalRing.maximalIdeal T' :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top (algebraMap T' T))
  have hKm : IsLocalRing.maximalIdeal T' * RingHom.ker (algebraMap T' T) = ⊥ := by
    rw [mul_comm]; exact hsmall
  have hK : RingHom.ker (algebraMap T' T) * RingHom.ker (algebraMap T' T) = ⊥ :=
    le_bot_iff.1 ((Ideal.mul_mono_left hkm).trans (le_of_eq hKm))

  have h0 : Nonempty
      ((Scheme.Modules.pullback
          (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
            (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]))).obj M₈ ≅
        (Scheme.Modules.pullback
          (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
            (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc]))).obj (𝟙_ _)) := by
    have hc₁ : g₁ ≫ f = f₁ ≫ σ := pullback.condition
    have hc₀ : g ≫ f₁ = f₀ ≫ π := pullback.condition
    have hc₀₀ : pullback.fst f₀ f₀ ≫ f₀ = pullback.snd f₀ f₀ ≫ f₀ := pullback.condition
    have hπ : π = Spec.map (CommRingCat.ofHom p) := rfl
    have he₁₁ : e.hom ≫ pullback.fst _ _ ≫ pullback.fst f f = pullback.fst f₁ f₁ ≫ g₁ := by
      rw [← Category.assoc, he₁, pullback.lift_fst]
    have he₁₂ : e.hom ≫ pullback.fst _ _ ≫ pullback.snd f f = pullback.snd f₁ f₁ ≫ g₁ := by
      rw [← Category.assoc, he₁, pullback.lift_snd]
    let gg : pullback f₀ f₀ ⟶ pullback f₁ f₁ := pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
      (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, pullback.condition, Category.assoc])
    have hgg₁ : gg ≫ pullback.fst f₁ f₁ = pullback.fst f₀ f₀ ≫ g := pullback.lift_fst _ _ _
    have hgg₂ : gg ≫ pullback.snd f₁ f₁ = pullback.snd f₀ f₀ ≫ g := pullback.lift_snd _ _ _
    let ψ₀ : SchemeHomOver ((Spec.map (CommRingCat.ofHom p) ≫ s) ≫ f) f := ⟨Spec.map (CommRingCat.ofHom p) ≫ s, rfl⟩
    let κ : pullback f₀ f₀ ⟶ pullback (prodStr f f) ((Spec.map (CommRingCat.ofHom p) ≫ s) ≫ f) :=
      pullback.lift
        (pullback.lift (pullback.fst f₀ f₀ ≫ g ≫ g₁) (pullback.snd f₀ f₀ ≫ g ≫ g₁)
          (by rw [Category.assoc, Category.assoc, hc₁, reassoc_of% hc₀, Category.assoc, Category.assoc, hc₁, reassoc_of% hc₀,
            reassoc_of% hc₀₀]))
        (pullback.fst f₀ f₀ ≫ f₀)
        (by
          show _ ≫ (pullback.fst f f ≫ f) = _
          rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, hc₁, reassoc_of% hc₀]
          simp only [Category.assoc]
          rfl)
    have hκa : κ ≫ pullback.fst _ _ ≫ pullback.fst f f = pullback.fst f₀ f₀ ≫ g ≫ g₁ := by
      rw [pullback.lift_fst_assoc, pullback.lift_fst]
    have hκb : κ ≫ pullback.fst _ _ ≫ pullback.snd f f = pullback.snd f₀ f₀ ≫ g ≫ g₁ := by
      rw [pullback.lift_fst_assoc, pullback.lift_snd]
    have hκc : κ ≫ pullback.snd _ _ = pullback.fst f₀ f₀ ≫ f₀ := pullback.lift_snd _ _ _
    have hb1 : baseChangeSnd (prodStr f f) (⟨s, rfl⟩ : SchemeHomOver (s ≫ f) f) ≫ pullback.fst _ _ = pullback.fst _ _ := by
      simp only [RelPicard.baseChangeSnd, pullback.lift_fst, Category.comp_id]
    have hb2 : baseChangeSnd (prodStr f f) (⟨s, rfl⟩ : SchemeHomOver (s ≫ f) f) ≫ pullback.snd _ _ = pullback.snd _ _ ≫ s := by
      simp only [RelPicard.baseChangeSnd, pullback.lift_snd]
    have hb1' : baseChangeSnd (prodStr f f) ψ₀ ≫ pullback.fst _ _ = pullback.fst _ _ := by
      simp only [RelPicard.baseChangeSnd, pullback.lift_fst, Category.comp_id]
    have hb2' : baseChangeSnd (prodStr f f) ψ₀ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ (Spec.map (CommRingCat.ofHom p) ≫ s) := by
      simp only [RelPicard.baseChangeSnd, pullback.lift_snd]
      rfl
    have hκ : gg ≫ e.hom ≫ baseChangeSnd (prodStr f f) (⟨s, rfl⟩ : SchemeHomOver (s ≫ f) f) =
        κ ≫ baseChangeSnd (prodStr f f) ψ₀ := by
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp only [Category.assoc]
          rw [reassoc_of% hb1, he₁₁, reassoc_of% hgg₁, reassoc_of% hb1', hκa]
        · simp only [Category.assoc]
          rw [reassoc_of% hb1, he₁₂, reassoc_of% hgg₂, reassoc_of% hb1', hκb]
      · simp only [Category.assoc]
        rw [hb2, reassoc_of% he₂, reassoc_of% hgg₁, reassoc_of% hc₀, hb2', reassoc_of% hκc]
    refine ⟨Ws23RC.pullbackComp₃ _ _ _ M.L ≪≫ (Scheme.Modules.pullbackCongr hκ).app M.L ≪≫
      ((Scheme.Modules.pullbackComp κ _).app M.L).symm ≪≫ (Scheme.Modules.pullback κ).mapIso iT ≪≫
      Scheme.Modules.pullbackUnitIso κ ≪≫ (Scheme.Modules.pullbackUnitIso _).symm⟩

  let θ : pullback f₁ (𝟙 (Spec (CommRingCat.of T'))) ⟶ pullback f f :=
    pullback.lift (pullback.fst f₁ (𝟙 _) ≫ g₁) (pullback.fst f₁ (𝟙 _) ≫ f₁ ≫ s)
      (by rw [Category.assoc, pullback.condition, Category.assoc, Category.assoc])
  have hθc : θ ≫ prodStr f f = pullback.snd f₁ (𝟙 _) ≫ σ := by
    show θ ≫ (pullback.fst f f ≫ f) = _
    rw [← Category.assoc, pullback.lift_fst, Category.assoc, pullback.condition, ← Category.assoc,
      pullback.condition, Category.assoc, Category.id_comp]
  have he₁₁ : e.hom ≫ pullback.fst _ _ ≫ pullback.fst f f = pullback.fst f₁ f₁ ≫ g₁ := by
    rw [← Category.assoc, he₁, pullback.lift_fst]
  have he₁₂ : e.hom ≫ pullback.fst _ _ ≫ pullback.snd f f = pullback.snd f₁ f₁ ≫ g₁ := by
    rw [← Category.assoc, he₁, pullback.lift_snd]
  have hone₁ : (L₁.one (𝟙 (Spec (CommRingCat.of T')))).1 ≫ g₁ = (L.one (𝟙 _ ≫ σ)).1 :=
    congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_one σ L (𝟙 _))
  have hone₁f : (L₁.one (𝟙 (Spec (CommRingCat.of T')))).1 ≫ f₁ = 𝟙 _ := (L₁.one (𝟙 _)).2

  let face₂ : pullback f f ⟶ pullback (prodStr f f) f :=
    pullback.lift (pullback.lift (pullback.fst f f) (L.one (prodStr f f)).1 (by rw [(L.one _).2]))
      (pullback.snd f f) (by rw [pullback.lift_fst_assoc]; exact pullback.condition)
  let face₁ : pullback f f ⟶ pullback (prodStr f f) f :=
    pullback.lift (pullback.lift (L.one (prodStr f f)).1 (pullback.fst f f) (by rw [(L.one _).2]))
      (pullback.snd f f) (by rw [pullback.lift_fst_assoc, (L.one _).2]; exact pullback.condition)
  have hF2a : face₂ ≫ pullback.fst _ _ ≫ pullback.fst f f = pullback.fst f f := by
    rw [pullback.lift_fst_assoc, pullback.lift_fst]
  have hF2b : face₂ ≫ pullback.fst _ _ ≫ pullback.snd f f = (L.one (prodStr f f)).1 := by
    rw [pullback.lift_fst_assoc, pullback.lift_snd]
  have hF2c : face₂ ≫ pullback.snd _ _ = pullback.snd f f := pullback.lift_snd _ _ _
  have hF1a : face₁ ≫ pullback.fst _ _ ≫ pullback.fst f f = (L.one (prodStr f f)).1 := by
    rw [pullback.lift_fst_assoc, pullback.lift_fst]
  have hF1b : face₁ ≫ pullback.fst _ _ ≫ pullback.snd f f = pullback.fst f f := by
    rw [pullback.lift_fst_assoc, pullback.lift_snd]
  have hF1c : face₁ ≫ pullback.snd _ _ = pullback.snd f f := pullback.lift_snd _ _ _
  have hθa : θ ≫ pullback.fst f f = pullback.fst f₁ (𝟙 _) ≫ g₁ := pullback.lift_fst _ _ _
  have hθb : θ ≫ pullback.snd f f = pullback.fst f₁ (𝟙 _) ≫ f₁ ≫ s := pullback.lift_snd _ _ _
  have hsla : sliceAt f₁ (L₁.one (𝟙 (Spec (CommRingCat.of T')))) ≫ pullback.fst f₁ f₁ = pullback.fst f₁ (𝟙 _) := by
    rw [sliceAt, pullback.lift_fst]
  have hslb : sliceAt f₁ (L₁.one (𝟙 (Spec (CommRingCat.of T')))) ≫ pullback.snd f₁ f₁ =
      pullback.snd f₁ (𝟙 _) ≫ (L₁.one (𝟙 _)).1 := by
    rw [sliceAt, pullback.lift_snd]
  have hbcs1 : baseChangeSnd (prodStr f f) (⟨s, rfl⟩ : SchemeHomOver (s ≫ f) f) ≫ pullback.fst _ _ = pullback.fst _ _ := by
    simp only [RelPicard.baseChangeSnd, pullback.lift_fst, Category.comp_id]
  have hbcs2 : baseChangeSnd (prodStr f f) (⟨s, rfl⟩ : SchemeHomOver (s ≫ f) f) ≫ pullback.snd _ _ = pullback.snd _ _ ≫ s := by
    simp only [RelPicard.baseChangeSnd, pullback.lift_snd]
  have hpb₁ : pullback.fst f₁ (𝟙 (Spec (CommRingCat.of T'))) ≫ f₁ = pullback.snd f₁ (𝟙 _) := by
    rw [pullback.condition, Category.comp_id]

  have hone : pullback.snd f₁ (𝟙 (Spec (CommRingCat.of T'))) ≫ (L₁.one (𝟙 _)).1 ≫ g₁ = θ ≫ (L.one (prodStr f f)).1 := by
    rw [hone₁, Ws23RC.comp_one_coe, Ws23RC.comp_one_coe]
    exact Ws23RC.one_coe_congr L (by rw [Category.id_comp, hθc])
  have hθ₁ : sliceAt f₁ (L₁.one (𝟙 _)) ≫ e.hom ≫ baseChangeSnd (prodStr f f) (⟨s, rfl⟩ : SchemeHomOver (s ≫ f) f) =
      θ ≫ face₂ := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc]
        rw [reassoc_of% hbcs1, he₁₁, ← Category.assoc, hsla, hF2a, hθa]
      · simp only [Category.assoc]
        rw [reassoc_of% hbcs1, he₁₂, ← Category.assoc, hslb, Category.assoc, hone, hF2b]
    · simp only [Category.assoc]
      rw [hbcs2, reassoc_of% he₂, ← Category.assoc, hsla, hF2c, hθb]
  have hθ₂ : sliceAt f₁ (L₁.one (𝟙 _)) ≫ (pullbackSymmetry f₁ f₁).hom ≫ e.hom ≫
        baseChangeSnd (prodStr f f) (⟨s, rfl⟩ : SchemeHomOver (s ≫ f) f) = θ ≫ face₁ := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc]
        rw [reassoc_of% hbcs1, he₁₁, pullbackSymmetry_hom_comp_fst_assoc, ← Category.assoc, hslb, Category.assoc, hone, hF1a]
      · simp only [Category.assoc]
        rw [reassoc_of% hbcs1, he₁₂, pullbackSymmetry_hom_comp_snd_assoc, ← Category.assoc, hsla, hF1b, hθa]
    · simp only [Category.assoc]
      rw [hbcs2, reassoc_of% he₂, pullbackSymmetry_hom_comp_fst_assoc, ← Category.assoc, hslb, Category.assoc,
        reassoc_of% hone₁f, hF1c, hθb, reassoc_of% hpb₁]

  have glob : ∀ (F : pullback f f ⟶ pullback (prodStr f f) f),
      LocIsoOnBase (prodStr f f) ((Scheme.Modules.pullback F).obj M.L) (𝟙_ _) →
      Nonempty ((Scheme.Modules.pullback (θ ≫ F)).obj M.L ≅ 𝟙_ _) := by
    intro F hF
    have hloc := LocIsoOnBase.pullback_of_comp_eq (pullback.snd f₁ (𝟙 (Spec (CommRingCat.of T')))) θ σ hθc hF
    obtain ⟨i⟩ := (locIsoOnBase_iff_nonempty_iso_of_isLocalRing _ _ _).1 hloc
    exact ⟨((Scheme.Modules.pullbackComp θ F).app M.L).symm ≪≫ i ≪≫ Scheme.Modules.pullbackUnitIso θ⟩
  have h1 : Nonempty ((Scheme.Modules.pullback (sliceAt f₁ (L₁.one (𝟙 (Spec (CommRingCat.of T')))))).obj M₈ ≅ 𝟙_ _) := by
    obtain ⟨i⟩ := glob face₂ h₂
    exact ⟨Ws23RC.pullbackComp₃ _ _ _ M.L ≪≫ (Scheme.Modules.pullbackCongr hθ₁).app M.L ≪≫ i⟩
  have h2 : Nonempty ((Scheme.Modules.pullback (sliceAt f₁ (L₁.one (𝟙 (Spec (CommRingCat.of T')))))).obj
      ((Scheme.Modules.pullback (pullbackSymmetry f₁ f₁).hom).obj M₈) ≅ 𝟙_ _) := by
    obtain ⟨i⟩ := glob face₁ h₁
    exact ⟨(Scheme.Modules.pullback _).mapIso (Ws23RC.pullbackComp₃ _ _ _ M.L) ≪≫
      (Scheme.Modules.pullbackComp _ _).app M.L ≪≫ (Scheme.Modules.pullbackCongr hθ₂).app M.L ≪≫ i⟩
  have h1' : Nonempty ((Scheme.Modules.pullback (sliceAt f₁ (L₁.one (𝟙 (Spec (CommRingCat.of T')))))).obj
      (𝟙_ (pullback f₁ f₁).Modules) ≅ 𝟙_ _) := ⟨Scheme.Modules.pullbackUnitIso _⟩
  have h2' : Nonempty ((Scheme.Modules.pullback (sliceAt f₁ (L₁.one (𝟙 (Spec (CommRingCat.of T')))))).obj
      ((Scheme.Modules.pullback (pullbackSymmetry f₁ f₁).hom).obj (𝟙_ (pullback f₁ f₁).Modules)) ≅ 𝟙_ _) :=
    ⟨(Scheme.Modules.pullback _).mapIso (Scheme.Modules.pullbackUnitIso _) ≪≫ Scheme.Modules.pullbackUnitIso _⟩

  obtain ⟨i₈⟩ := GoodReductionJacobian.AbelianSchemePropertyBundle.nonempty_iso_of_pullback_iso_of_sliceAt_one_of_isPullback_of_ker_mul_self_of_isNoetherianRing
    hp hK hKm L₁ hA₁ L₀ g hg
    (fun t' P Q => congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_mul π L₁ t' P Q))
    M₈ (𝟙_ _) hM₈ (Scheme.Modules.isInvertible_unit _) h0 h1 h2 h1' h2'

  exact ⟨(Ws23RC.pullbackInvHomIso e N).symm ≪≫ (Scheme.Modules.pullback e.inv).mapIso i₈ ≪≫ Scheme.Modules.pullbackUnitIso e.inv⟩

end S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_pullbackAlong_iso_unit_of_smallExtension_of_locIsoOnBase_faces
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_pullbackAlong_iso_unit_of_smallExtension_of_locIsoOnBase_faces (solution)
