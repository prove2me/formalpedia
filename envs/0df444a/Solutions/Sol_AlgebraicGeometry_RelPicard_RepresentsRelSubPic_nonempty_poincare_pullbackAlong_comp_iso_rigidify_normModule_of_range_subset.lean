-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_comp_iso_rigidify_normModule_of_range_subset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/0691d2db-03e7-593b-8a53-4f9991d80a24

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_pullback_rigidify_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_normModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_morphismRestrict_eq_finrank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_comp_iso_rigidify_normModule_of_range_subset
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_comp_iso_rigidify_normModule_of_range_subset.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_comp_iso_rigidify_normModule_of_range_subset.AlgebraicGeometry.RelPicard"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsOpenImmersion.lift morphismRestrict_ι morphismRestrict_base_coe Scheme.Modules.pullback Scheme.Opens.range_ι Scheme.Hom IsFinite isPullback_morphismRestrict Spec Scheme IsOpenImmersion Flat Scheme.Hom.finrank_of_isPullback Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Opens LocallyOfFinitePresentation IsOpenImmersion.lift_fac Scheme.Hom.comp_apply Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.rigidify Scheme.Modules.rigidifyMapIso Scheme.Modules.normModule Scheme.Modules.normModuleMapIso RelPicard.BaseChange.baseChangeSnd_fst' Scheme.Modules.IsInvertible.nonempty_pullback_rigidify_iso Scheme.Modules.nonempty_pullback_normModule_iso Scheme.Hom.finrank_morphismRestrict_eq_finrank"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection baseChangeSnd_comp rigSection_baseChangeSnd SubPicCondition RepresentsRelSubPic curveChange curveChange_baseChangeSnd curveChange_snd baseChangeSnd_snd BaseChange.baseChangeSnd_fst'"
namespace C2_8f7a3a05
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}

private theorem curveChange_fst (f : C' ⟶ C) (hf : f ≫ c = c') {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    curveChange f hf t ≫ pullback.fst c t = pullback.fst c' t ≫ f := by
  simp only [curveChange, pullback.lift_fst]

private theorem isPullback_curveChange (f : C' ⟶ C) (hf : f ≫ c = c') {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    IsPullback (pullback.fst c' t) (curveChange f hf t) f (pullback.fst c t) := by
  have big : IsPullback (curveChange f hf t ≫ pullback.snd c t) (pullback.fst c' t) t (f ≫ c) := by
    rw [curveChange_snd, hf]
    exact (IsPullback.of_hasPullback c' t).flip
  exact (big.of_right (curveChange_fst f hf t) (IsPullback.of_hasPullback c t).flip).flip

private theorem exists_isPullback_curveChange_restrict (f : C' ⟶ C) (hf : f ≫ c = c') {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (U : C.Opens) :
    ∃ k : ↑((curveChange f hf t) ⁻¹ᵁ ((pullback.fst c t) ⁻¹ᵁ U)) ⟶ ↑(f ⁻¹ᵁ U),
      IsPullback k (curveChange f hf t ∣_ (pullback.fst c t) ⁻¹ᵁ U) (f ∣_ U) (pullback.fst c t ∣_ U) := by
  have s : IsPullback
      (((curveChange f hf t) ⁻¹ᵁ ((pullback.fst c t) ⁻¹ᵁ U)).ι ≫ pullback.fst c' t)
      (curveChange f hf t ∣_ (pullback.fst c t) ⁻¹ᵁ U) f (((pullback.fst c t) ⁻¹ᵁ U).ι ≫ pullback.fst c t) :=
    (isPullback_morphismRestrict (curveChange f hf t) ((pullback.fst c t) ⁻¹ᵁ U)).flip.paste_horiz
      (isPullback_curveChange f hf t)
  have w : (curveChange f hf t ∣_ (pullback.fst c t) ⁻¹ᵁ U ≫ pullback.fst c t ∣_ U) ≫ U.ι =
      (((curveChange f hf t) ⁻¹ᵁ ((pullback.fst c t) ⁻¹ᵁ U)).ι ≫ pullback.fst c' t) ≫ f := by
    rw [Category.assoc, morphismRestrict_ι]
    exact s.w.symm
  refine ⟨(isPullback_morphismRestrict f U).lift _ _ w, ?_⟩
  refine IsPullback.of_right (h₁₂ := (f ⁻¹ᵁ U).ι) (h₂₂ := U.ι) ?_ (IsPullback.lift_fst _ _ _ _)
    (isPullback_morphismRestrict f U).flip
  rw [IsPullback.lift_snd, morphismRestrict_ι]
  exact s

end AlgebraicGeometry.RelPicard.C2_8f7a3a05

open AlgebraicGeometry.RelPicard.C2_8f7a3a05 in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P D)

    (πa πb : SchemeHomOver c' c) [IsFinite πa.1] [LocallyOfFinitePresentation πa.1]

    (U : C.Opens) (d : ℕ) (hfl : Flat (πa.1 ∣_ U)) (hrk : ∀ y : C, y ∈ U → πa.1.finrank y = d)

    (𝒩 : (pullback c D.toBase).Modules) (h𝒩 : Scheme.Modules.IsInvertible 𝒩)
    (hNe : ∀ (V : (pullback c D.toBase).Opens) (d' : ℕ),
      Flat ((curveChange πa.1 πa.2 D.toBase) ∣_ V) → LocallyOfFinitePresentation ((curveChange πa.1 πa.2 D.toBase) ∣_ V) →
      (∀ y : V, ((curveChange πa.1 πa.2 D.toBase) ∣_ V).finrank y = d') →
      Nonempty ((Scheme.Modules.pullback V.ι).obj 𝒩 ≅
        Scheme.Modules.normModule ((curveChange πa.1 πa.2 D.toBase) ∣_ V) d'
          ((Scheme.Modules.pullback ((curveChange πa.1 πa.2 D.toBase) ⁻¹ᵁ V).ι).obj
            ((Scheme.Modules.pullback (curveChange πb.1 πb.2 D.toBase)).obj h.poincare.L))))

    (T : SchemeHomOver D.toBase D.toBase)
    (hT : Nonempty ((h.poincare.pullbackAlong T).L ≅
      Scheme.Modules.rigidify (rigSection c D.toBase ε) (pullback.snd c D.toBase) 𝒩))

    {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase)
    (hU : Set.range (pullback.fst c t).base ⊆ (U : Set C)) :
    Nonempty ((h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a T)).L ≅
      Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
        (Scheme.Modules.normModule (curveChange πa.1 πa.2 t) d
          ((Scheme.Modules.pullback (curveChange πb.1 πb.2 t)).obj (h.poincare.pullbackAlong a).L))) := by

  have e1 : (h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a T)).L ≅
      (Scheme.Modules.pullback (baseChangeSnd c a)).obj ((h.poincare.pullbackAlong T).L) := by
    change (Scheme.Modules.pullback (baseChangeSnd c (NeronModelInfra.schemeHomOverComp a T))).obj h.poincare.L ≅
      (Scheme.Modules.pullback (baseChangeSnd c a)).obj ((Scheme.Modules.pullback (baseChangeSnd c T)).obj h.poincare.L)
    have hc : baseChangeSnd c (NeronModelInfra.schemeHomOverComp a T) = baseChangeSnd c a ≫ baseChangeSnd c T :=
      (baseChangeSnd_comp c T a).symm
    exact (Scheme.Modules.pullbackCongr hc).app h.poincare.L ≪≫
      ((Scheme.Modules.pullbackComp (baseChangeSnd c a) (baseChangeSnd c T)).app h.poincare.L).symm

  obtain ⟨eT⟩ := hT
  obtain ⟨eR⟩ := Scheme.Modules.IsInvertible.nonempty_pullback_rigidify_iso (σ := rigSection c D.toBase ε)
    (q := pullback.snd c D.toBase) (σ' := rigSection c t ε) (q' := pullback.snd c t) a.1 (baseChangeSnd c a)
    (rigSection_baseChangeSnd c ε a) (baseChangeSnd_snd (c := c) a) h𝒩

  let V : (pullback c D.toBase).Opens := (pullback.fst c D.toBase) ⁻¹ᵁ U
  have hgV : Set.range (baseChangeSnd c a).base ⊆ (V : Set ↥(pullback c D.toBase)) := by
    rintro _ ⟨x, rfl⟩
    show (pullback.fst c D.toBase).base ((baseChangeSnd c a).base x) ∈ U
    rw [← Scheme.Hom.comp_apply, AlgebraicGeometry.RelPicard.BaseChange.baseChangeSnd_fst']
    exact hU ⟨x, rfl⟩
  have sqD := isPullback_curveChange (c := c) πa.1 πa.2 D.toBase
  obtain ⟨kV, sqV⟩ := exists_isPullback_curveChange_restrict (c := c) πa.1 πa.2 D.toBase U
  haveI : IsFinite (curveChange πa.1 πa.2 D.toBase) := MorphismProperty.of_isPullback sqD ‹_›
  haveI : LocallyOfFinitePresentation (curveChange πa.1 πa.2 D.toBase) := MorphismProperty.of_isPullback sqD ‹_›
  have hflV : Flat ((curveChange πa.1 πa.2 D.toBase) ∣_ V) := by
    haveI : Flat (πa.1 ∣_ U) := hfl
    exact MorphismProperty.of_isPullback sqV ‹_›
  have hlfpV : LocallyOfFinitePresentation ((curveChange πa.1 πa.2 D.toBase) ∣_ V) := inferInstance
  have hrkV : ∀ y : V, ((curveChange πa.1 πa.2 D.toBase) ∣_ V).finrank y = d := by
    intro y
    haveI : Flat (πa.1 ∣_ U) := hfl
    have hyU : (pullback.fst c D.toBase).base y.1 ∈ U := y.2
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sqV y]
    have hy : ((pullback.fst c D.toBase) ∣_ U).base y = ⟨(pullback.fst c D.toBase).base y.1, hyU⟩ :=
      Subtype.ext (morphismRestrict_base_coe _ _ _)
    rw [hy, Scheme.Hom.finrank_morphismRestrict_eq_finrank]
    exact hrk _ hyU
  obtain ⟨eN⟩ := hNe V d hflV hlfpV hrkV

  have hgV' : Set.range (baseChangeSnd c a).base ⊆ Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι]; exact hgV
  let g₀ : pullback c t ⟶ V := IsOpenImmersion.lift V.ι (baseChangeSnd c a) hgV'
  have hg₀ : g₀ ≫ V.ι = baseChangeSnd c a := IsOpenImmersion.lift_fac _ _ _

  have bigsq : IsPullback (baseChangeSnd c' a) (curveChange πa.1 πa.2 t) (curveChange πa.1 πa.2 D.toBase)
      (baseChangeSnd c a) := by
    have s : IsPullback (baseChangeSnd c' a ≫ pullback.fst c' D.toBase) (curveChange πa.1 πa.2 t) πa.1
        (baseChangeSnd c a ≫ pullback.fst c D.toBase) := by
      rw [AlgebraicGeometry.RelPicard.BaseChange.baseChangeSnd_fst',
        AlgebraicGeometry.RelPicard.BaseChange.baseChangeSnd_fst']
      exact isPullback_curveChange (c := c) πa.1 πa.2 t
    exact s.of_right (curveChange_baseChangeSnd πa.1 πa.2 a).symm sqD

  have w2 : (curveChange πa.1 πa.2 t ≫ g₀) ≫ V.ι = baseChangeSnd c' a ≫ curveChange πa.1 πa.2 D.toBase := by
    rw [Category.assoc, hg₀]; exact curveChange_baseChangeSnd πa.1 πa.2 a
  let g' := (isPullback_morphismRestrict (curveChange πa.1 πa.2 D.toBase) V).lift _ _ w2
  have hg' : g' ≫ ((curveChange πa.1 πa.2 D.toBase) ⁻¹ᵁ V).ι = baseChangeSnd c' a :=
    IsPullback.lift_snd _ _ _ _
  have sqg : IsPullback g' (curveChange πa.1 πa.2 t) ((curveChange πa.1 πa.2 D.toBase) ∣_ V) g₀ := by
    refine IsPullback.of_right (h₁₂ := ((curveChange πa.1 πa.2 D.toBase) ⁻¹ᵁ V).ι) (h₂₂ := V.ι) ?_
      (IsPullback.lift_fst _ _ _ _) (isPullback_morphismRestrict _ V).flip
    rw [hg', hg₀]; exact bigsq
  haveI : Flat ((curveChange πa.1 πa.2 D.toBase) ∣_ V) := hflV
  obtain ⟨eBC⟩ := Scheme.Modules.nonempty_pullback_normModule_iso ((curveChange πa.1 πa.2 D.toBase) ∣_ V) d hrkV
    g₀ (curveChange πa.1 πa.2 t) g' sqg ((h.poincare.isInvertible.pullback _).pullback _)

  have eL : (Scheme.Modules.pullback g').obj ((Scheme.Modules.pullback ((curveChange πa.1 πa.2 D.toBase) ⁻¹ᵁ V).ι).obj
        ((Scheme.Modules.pullback (curveChange πb.1 πb.2 D.toBase)).obj h.poincare.L)) ≅
      (Scheme.Modules.pullback (curveChange πb.1 πb.2 t)).obj (h.poincare.pullbackAlong a).L :=
    (Scheme.Modules.pullbackComp g' _).app _ ≪≫
      (Scheme.Modules.pullbackCongr hg').app _ ≪≫
      (Scheme.Modules.pullbackComp (baseChangeSnd c' a) (curveChange πb.1 πb.2 D.toBase)).app h.poincare.L ≪≫
      (Scheme.Modules.pullbackCongr (curveChange_baseChangeSnd πb.1 πb.2 a).symm).app h.poincare.L ≪≫
      ((Scheme.Modules.pullbackComp (curveChange πb.1 πb.2 t) (baseChangeSnd c a)).app h.poincare.L).symm
  have e4 : (Scheme.Modules.pullback (baseChangeSnd c a)).obj 𝒩 ≅
      Scheme.Modules.normModule (curveChange πa.1 πa.2 t) d
        ((Scheme.Modules.pullback (curveChange πb.1 πb.2 t)).obj (h.poincare.pullbackAlong a).L) :=
    (Scheme.Modules.pullbackCongr hg₀.symm).app 𝒩 ≪≫ ((Scheme.Modules.pullbackComp g₀ V.ι).app 𝒩).symm ≪≫
      (Scheme.Modules.pullback g₀).mapIso eN ≪≫ eBC ≪≫ Scheme.Modules.normModuleMapIso _ d eL
  exact ⟨e1 ≪≫ (Scheme.Modules.pullback (baseChangeSnd c a)).mapIso eT ≪≫ eR ≪≫ Scheme.Modules.rigidifyMapIso _ _ e4⟩

#print axioms solution

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_comp_iso_rigidify_normModule_of_range_subset
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_comp_iso_rigidify_normModule_of_range_subset (solution)
