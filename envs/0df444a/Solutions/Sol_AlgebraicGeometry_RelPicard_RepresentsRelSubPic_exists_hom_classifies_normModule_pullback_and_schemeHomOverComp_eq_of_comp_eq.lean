-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_hom_classifies_normModule_pullback_and_schemeHomOverComp_eq_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/1e5a38df-4076-5e90-9bbc-263293c8d67d

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_JacJ1Iface
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_normModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_tensor_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_rigidify_pullback_tensor_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_normModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_normModule_pullback_pullback_iso_pullback
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_hom_classifies_rigidify_normModule_pullback_curveChange
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_hom_classifies_normModule_pullback_and_schemeHomOverComp_eq_of_comp_eq
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

universe u
p2m_open "CategoryTheory.MonoidalCategory"

theorem isPullback_fst_curveChange {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)} (f : C' ⟶ C) (hf : f ≫ c = c')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    IsPullback (pullback.fst c' t) (curveChange f hf t) f (pullback.fst c t) := by

  have big : IsPullback (pullback.fst c' t) (pullback.snd c' t) c' t := IsPullback.of_hasPullback c' t
  have right : IsPullback (pullback.fst c t) (pullback.snd c t) c t := IsPullback.of_hasPullback c t
  have hsnd : curveChange f hf t ≫ pullback.snd c t = pullback.snd c' t := curveChange_snd f hf t
  have hfst : curveChange f hf t ≫ pullback.fst c t = pullback.fst c' t ≫ f := by
    simp only [curveChange, pullback.lift_fst]
  refine IsPullback.of_bot ?_ hfst.symm right
  rw [hsnd, hf]
  exact big

set_option maxHeartbeats 12800000 in
theorem solution
    {R : Type u} [CommRing R]

    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)

    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R)) (πα πβ : Y ⟶ C) (Hα : πα ≫ c = y) (Hβ : πβ ≫ c = y)
    [IsFinite πα] [Flat πα] [LocallyOfFinitePresentation πα] (d : ℕ) (hd : ∀ x : C, πα.finrank x = d)

    (T : SchemeHomOver D.toBase D.toBase)
    (hT : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
      Nonempty ((h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a T)).L ≅
        Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
          (Scheme.Modules.normModule (curveChange (c' := y) πα Hα t) d
            ((Scheme.Modules.pullback (curveChange (c' := y) πβ Hβ t)).obj (h.poincare.pullbackAlong a).L))))

    {Ca : Scheme.{u}} (ca : Ca ⟶ Spec (CommRingCat.of R)) (εa : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) ca)
    (Da : RelativePic0Designation R ca) (ha : RepresentsRelSubPic ca εa (algEquivZeroCut ca εa) Da)
    (i : Ca ⟶ C) (hi : i ≫ c = ca)

    (ν : SchemeHomOver D.toBase Da.toBase)
    (hν : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
      Nonempty ((ha.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν)).L ≅
        Scheme.Modules.rigidify (rigSection ca t εa) (pullback.snd ca t)
          ((Scheme.Modules.pullback (curveChange i hi t)).obj (h.poincare.pullbackAlong a).L)))

    (e : pullback πα i ⟶ Ca) (he : e ≫ i = pullback.fst πα i ≫ πβ)
    (he' : e ≫ ca = pullback.snd πα i ≫ ca) :
    ∃ u : SchemeHomOver Da.toBase Da.toBase,
      (∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)) (b : SchemeHomOver t Da.toBase),
        Nonempty ((ha.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b u)).L ≅
          Scheme.Modules.rigidify (rigSection ca t εa) (pullback.snd ca t)
            (Scheme.Modules.normModule
              (curveChange (c := ca) (c' := pullback.snd πα i ≫ ca) (pullback.snd πα i) rfl t) d
              ((Scheme.Modules.pullback
                  (curveChange (c := ca) (c' := pullback.snd πα i ≫ ca) e he' t)).obj
                (ha.poincare.pullbackAlong b).L)))) ∧
      (∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
        NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp a T) ν =
          NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp a ν) u) := by

  have sqE : IsPullback (pullback.fst πα i) (pullback.snd πα i) πα i := IsPullback.of_hasPullback πα i
  haveI : IsFinite (pullback.snd πα i) := MorphismProperty.of_isPullback (P := @IsFinite) sqE inferInstance
  haveI : Flat (pullback.snd πα i) := MorphismProperty.of_isPullback (P := @Flat) sqE inferInstance
  haveI : LocallyOfFinitePresentation (pullback.snd πα i) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) sqE inferInstance
  have hdE : ∀ x : Ca, (pullback.snd πα i).finrank x = d := fun x => by
    rw [Scheme.Hom.finrank_pullback_snd]; exact hd _

  obtain ⟨u, hu⟩ := AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_hom_classifies_rigidify_normModule_pullback_curveChange
    ca εa Da ha (pullback.snd πα i ≫ ca) (pullback.snd πα i) e rfl he' d hdE
  refine ⟨u, fun t b => hu t b, ?_⟩

  intro S t a
  apply ha.ext_of_iso t

  let E := pullback πα i
  let yE : E ⟶ Spec (CommRingCat.of R) := pullback.snd πα i ≫ ca
  have hfy : pullback.fst πα i ≫ y = yE := by
    rw [← Hα, ← Category.assoc, pullback.condition, Category.assoc, hi]
  let g := curveChange i hi t
  let q := pullback.snd c t
  let qa := pullback.snd ca t
  let σ := rigSection c t ε
  let σa := rigSection ca t εa
  let πat := curveChange (c := c) (c' := y) πα Hα t
  let πbt := curveChange (c := c) (c' := y) πβ Hβ t
  let prt := curveChange (c := ca) (c' := yE) (pullback.snd πα i) rfl t
  let et := curveChange (c := ca) (c' := yE) e he' t
  let G := curveChange (c := y) (c' := yE) (pullback.fst πα i) hfy t
  let Pa := (h.poincare.pullbackAlong a).L
  have hPa : Scheme.Modules.IsInvertible Pa := (h.poincare.pullbackAlong a).isInvertible

  have sqA : IsPullback (pullback.fst yE t) prt (pullback.snd πα i) (pullback.fst ca t) :=
    isPullback_fst_curveChange (c := ca) (c' := yE) (pullback.snd πα i) rfl t
  have sqC : IsPullback (pullback.fst y t) πat πα (pullback.fst c t) := isPullback_fst_curveChange πα Hα t
  have hGfst : G ≫ pullback.fst y t = pullback.fst yE t ≫ pullback.fst πα i := by simp only [G, curveChange, pullback.lift_fst]
  have hgfst : g ≫ pullback.fst c t = pullback.fst ca t ≫ i := by simp only [g, curveChange, pullback.lift_fst]
  have hGπ : G ≫ πat = prt ≫ g := by
    apply pullback.hom_ext
    · simp only [G, πat, prt, g, curveChange, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.condition]
    · simp only [G, πat, prt, g, curveChange, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
  have sqEt : IsPullback G prt πat g := by
    have outer : IsPullback (G ≫ pullback.fst y t) prt πα (g ≫ pullback.fst c t) := by
      rw [hGfst, hgfst]; exact sqA.paste_horiz sqE
    exact IsPullback.of_right outer hGπ sqC
  haveI : IsFinite prt := MorphismProperty.of_isPullback (P := @IsFinite) sqA inferInstance
  haveI : Flat prt := MorphismProperty.of_isPullback (P := @Flat) sqA inferInstance
  haveI : LocallyOfFinitePresentation prt := MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) sqA inferInstance
  haveI : IsFinite πat := MorphismProperty.of_isPullback (P := @IsFinite) sqC inferInstance
  haveI : Flat πat := MorphismProperty.of_isPullback (P := @Flat) sqC inferInstance
  haveI : LocallyOfFinitePresentation πat := MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) sqC inferInstance
  have hdprt : ∀ z, prt.finrank z = d := fun z => by
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sqA]; exact hdE _
  have hdπat : ∀ z, πat.finrank z = d := fun z => by
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sqC]; exact hd _

  have hgq : g ≫ q = qa := curveChange_snd i hi t
  have hetq : et ≫ qa = prt ≫ qa := by
    show curveChange (c := ca) (c' := yE) e he' t ≫ pullback.snd ca t = curveChange (c := ca) (c' := yE) (pullback.snd πα i) rfl t ≫ pullback.snd ca t
    rw [curveChange_snd, curveChange_snd]
  have hGe : G ≫ πbt = et ≫ g := by
    apply pullback.hom_ext
    · simp only [G, πbt, et, g, curveChange, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, he]
    · simp only [G, πbt, et, g, curveChange, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
  have hσq : σa ≫ qa = 𝟙 _ := by simp only [σa, qa, rigSection, pullback.lift_snd]

  let NX := Scheme.Modules.normModule πat d ((Scheme.Modules.pullback πbt).obj Pa)
  have hNX : Scheme.Modules.IsInvertible NX := Scheme.Modules.IsInvertible.normModule πat d hdπat (hPa.pullback πbt)
  let Z := Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj NX)
  have hZ : Scheme.Modules.IsInvertible Z := (hNX.pullback σ).dual.1

  let RIGN := Scheme.Modules.rigidify σa qa (Scheme.Modules.normModule prt d
    ((Scheme.Modules.pullback et).obj ((Scheme.Modules.pullback g).obj Pa)))

  have lhs : (ha.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp a T) ν)).L ≅ RIGN := by
    refine (hν t (NeronModelInfra.schemeHomOverComp a T)).some ≪≫
      Scheme.Modules.rigidifyMapIso σa qa ((Scheme.Modules.pullback g).mapIso (hT t a).some) ≪≫ ?_

    refine Scheme.Modules.rigidifyMapIso σa qa
        (Scheme.Modules.pullbackTensorObjIso g NX ((Scheme.Modules.pullback q).obj Z) ≪≫
          whiskerLeftIso _ ((Scheme.Modules.pullbackComp g q).app Z ≪≫ (Scheme.Modules.pullbackCongr hgq).app Z) ≪≫ β_ _ _) ≪≫
      (Scheme.Modules.IsInvertible.nonempty_rigidify_pullback_tensor_iso hσq hZ (hNX.pullback g)).some ≪≫ ?_

    refine Scheme.Modules.rigidifyMapIso σa qa
      ((Scheme.Modules.nonempty_pullback_normModule_iso πat d hdπat g prt G sqEt (hPa.pullback πbt)).some ≪≫
        Scheme.Modules.normModuleMapIso prt d
          ((Scheme.Modules.pullbackComp G πbt).app Pa ≪≫ (Scheme.Modules.pullbackCongr hGe).app Pa ≪≫
            ((Scheme.Modules.pullbackComp et g).app Pa).symm))

  let X := (Scheme.Modules.pullback et).obj ((Scheme.Modules.pullback g).obj Pa)
  have hX : Scheme.Modules.IsInvertible X := (hPa.pullback g).pullback et
  have hNmX : Scheme.Modules.IsInvertible (Scheme.Modules.normModule prt d X) := Scheme.Modules.IsInvertible.normModule prt d hdprt hX
  let Za := Scheme.Modules.dual ((Scheme.Modules.pullback σa).obj ((Scheme.Modules.pullback g).obj Pa))
  have hZa : Scheme.Modules.IsInvertible Za := ((hPa.pullback g).pullback σa).dual.1
  obtain ⟨N, hN, ⟨eN⟩⟩ := AlgebraicGeometry.Scheme.Modules.exists_isInvertible_normModule_pullback_pullback_iso_pullback
    prt d hdprt qa hZa
  have rhs : (ha.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp a ν) u)).L ≅ RIGN := by
    refine (hu t (NeronModelInfra.schemeHomOverComp a ν)).some ≪≫ Scheme.Modules.rigidifyMapIso σa qa ?_ ≪≫
      (Scheme.Modules.IsInvertible.nonempty_rigidify_pullback_tensor_iso hσq hN hNmX).some

    refine Scheme.Modules.normModuleMapIso prt d
        ((Scheme.Modules.pullback et).mapIso (hν t a).some ≪≫
          Scheme.Modules.pullbackTensorObjIso et ((Scheme.Modules.pullback g).obj Pa) ((Scheme.Modules.pullback qa).obj Za) ≪≫
          whiskerLeftIso X ((Scheme.Modules.pullbackComp et qa).app Za ≪≫ (Scheme.Modules.pullbackCongr hetq).app Za ≪≫
            ((Scheme.Modules.pullbackComp prt qa).app Za).symm)) ≪≫
      (Scheme.Modules.nonempty_normModule_tensor_iso prt d hdprt X ((Scheme.Modules.pullback prt).obj ((Scheme.Modules.pullback qa).obj Za))
        hX ((hZa.pullback qa).pullback prt)).some ≪≫
      whiskerLeftIso _ eN ≪≫ β_ _ _
  exact ⟨lhs ≪≫ rhs.symm⟩

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_hom_classifies_normModule_pullback_and_schemeHomOverComp_eq_of_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_hom_classifies_normModule_pullback_and_schemeHomOverComp_eq_of_comp_eq (solution)
