-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.schemeHomOverComp_mul_eq_mul_and_zeroSection_comp_of_classifies_normModule_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a3a20065-2069-5409-8fb1-482fdf7c032b

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_JacJ1Iface

import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_comp_mul_eq_mul_comp_of_transform
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_normModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_unit_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_tensor_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_FibrewiseAlgEquivZero_ofInvertible_normModule_curveChange
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_pullbackMap_of_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_schemeHomOverComp_mul_eq_mul_and_zeroSection_comp_of_classifies_normModule_pullback
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc"
p2m_attr_erase "simp" "AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

universe u

p2m_open "CategoryTheory.MonoidalCategory"

noncomputable section

namespace G5HomCrux

section CurveChange

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  (π : C' ⟶ C) (hπ : π ≫ c = c')

theorem isFinite_curveChange [IsFinite π] {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    IsFinite (curveChange π hπ t) :=
  MorphismProperty.pullbackMap (P := @IsFinite) ‹IsFinite π› (inferInstance : IsFinite (𝟙 T)) hπ.symm
    (Category.id_comp t).symm

theorem flat_curveChange [Flat π] {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Flat (curveChange π hπ t) :=
  MorphismProperty.pullbackMap (P := @Flat) ‹Flat π› (inferInstance : Flat (𝟙 T)) hπ.symm
    (Category.id_comp t).symm

theorem locallyOfFinitePresentation_curveChange [LocallyOfFinitePresentation π] {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) : LocallyOfFinitePresentation (curveChange π hπ t) :=
  MorphismProperty.pullbackMap (P := @LocallyOfFinitePresentation) ‹LocallyOfFinitePresentation π›
    (inferInstance : LocallyOfFinitePresentation (𝟙 T)) hπ.symm (Category.id_comp t).symm

theorem finrank_curveChange [Flat π] [IsFinite π] {d : ℕ} (hd : ∀ y : C, π.finrank y = d)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    ∀ y, (curveChange π hπ t).finrank y = d :=
  fun y => (Scheme.Hom.finrank_pullbackMap_of_comp_eq c c' t π hπ y).trans (hd _)

end CurveChange

section Transform

variable {R : Type u} [CommRing R] {C E : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {cE : E ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  (φ ψ : E ⟶ C) (hφ : φ ≫ c = cE) (hψ : ψ ≫ c = cE)
  [IsFinite φ] [Flat φ] [LocallyOfFinitePresentation φ]
  (d : ℕ) (hd : ∀ y : C, φ.finrank y = d)

def pullL {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    (pullback cE t).Modules :=
  (Scheme.Modules.pullback (curveChange (c := c) (c' := cE) ψ hψ t)).obj M.L

theorem pullL_isInvertible {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    Scheme.Modules.IsInvertible (pullL (ε := ε) ψ hψ t M) :=
  M.isInvertible.pullback _

include hd

theorem hinv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    Scheme.Modules.IsInvertible
      (Scheme.Modules.normModule (curveChange (c := c) (c' := cE) φ hφ t) d (pullL (ε := ε) ψ hψ t M)) :=
  haveI := isFinite_curveChange φ hφ t
  haveI := flat_curveChange φ hφ t
  haveI := locallyOfFinitePresentation_curveChange φ hφ t
  Scheme.Modules.IsInvertible.normModule _ d (finrank_curveChange φ hφ hd t) (pullL_isInvertible ψ hψ t M)

def Phi {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    RigidifiedLineBundle c ε t :=
  RigidifiedLineBundle.ofInvertible (ε := ε)
    (Scheme.Modules.normModule (curveChange (c := c) (c' := cE) φ hφ t) d (pullL (ε := ε) ψ hψ t M))
    (hinv φ ψ hφ hψ d hd t M)

theorem hcut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
    (hM : FibrewiseAlgEquivZero M) : FibrewiseAlgEquivZero (Phi (ε := ε) φ ψ hφ hψ d hd t M) := by
  refine FibrewiseAlgEquivZero.ofInvertible_normModule_curveChange (ε := ε) φ hφ d hd
    (pullL (ε := ε) ψ hψ t M) (pullL_isInvertible ψ hψ t M) ?_ (hinv φ ψ hφ hψ d hd t M)
  intro k _ _ s
  let e : Limits.pullback (pullback.snd cE t) s ⟶ Limits.pullback (pullback.snd c t) s :=
    pullback.map _ _ _ _ (curveChange (c := c) (c' := cE) ψ hψ t) (𝟙 _) (𝟙 T)
      (by rw [Category.comp_id, curveChange_snd]) (by simp)
  have he : e ≫ fibreAt c t s = fibreAt cE t s := by
    simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
  have hfst : e ≫ pullback.fst (pullback.snd c t) s =
      pullback.fst (pullback.snd cE t) s ≫ curveChange (c := c) (c' := cE) ψ hψ t := by
    simp only [e, pullback.lift_fst]
  refine IsAlgEquivZero.of_iso ?_ ((hM k s).pullback e he)
  exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr hfst).app M.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.L).symm

theorem hunit {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Nonempty ((Phi (ε := ε) φ ψ hφ hψ d hd t (RigidifiedLineBundle.unit (c := c) (ε := ε) t)).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) t).L) := by
  haveI := isFinite_curveChange φ hφ t
  haveI := flat_curveChange φ hφ t
  haveI := locallyOfFinitePresentation_curveChange φ hφ t
  obtain ⟨eN⟩ := Scheme.Modules.nonempty_normModule_unit_iso (curveChange (c := c) (c' := cE) φ hφ t) d
    (finrank_curveChange φ hφ hd t)
  let eP : pullL (ε := ε) ψ hψ t (RigidifiedLineBundle.unit (c := c) (ε := ε) t) ≅ 𝟙_ _ :=
    Scheme.Modules.pullbackUnitIso _
  obtain ⟨e1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    (hinv φ ψ hφ hψ d hd t (RigidifiedLineBundle.unit t))
    (RigidifiedLineBundle.unit (c := c) (ε := ε) t).isInvertible (Scheme.Modules.normModuleMapIso _ d eP ≪≫ eN)
  obtain ⟨e2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified
    (RigidifiedLineBundle.unit (c := c) (ε := ε) t)
  exact ⟨e1 ≪≫ e2⟩

theorem htensor {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c ε t) :
    Nonempty ((Phi (ε := ε) φ ψ hφ hψ d hd t (M.tensor M')).L ≅
      ((Phi (ε := ε) φ ψ hφ hψ d hd t M).tensor (Phi (ε := ε) φ ψ hφ hψ d hd t M')).L) := by
  haveI := isFinite_curveChange φ hφ t
  haveI := flat_curveChange φ hφ t
  haveI := locallyOfFinitePresentation_curveChange φ hφ t
  let eP : pullL (ε := ε) ψ hψ t (M.tensor M') ≅ pullL (ε := ε) ψ hψ t M ⊗ pullL (ε := ε) ψ hψ t M' :=
    Scheme.Modules.pullbackTensorObjIso _ _ _
  obtain ⟨eT⟩ := Scheme.Modules.nonempty_normModule_tensor_iso (curveChange (c := c) (c' := cE) φ hφ t) d
    (finrank_curveChange φ hφ hd t) _ _ (pullL_isInvertible ψ hψ t M) (pullL_isInvertible ψ hψ t M')
  obtain ⟨e1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    (hinv φ ψ hφ hψ d hd t (M.tensor M'))
    ((hinv φ ψ hφ hψ d hd t M).tensor (hinv φ ψ hφ hψ d hd t M')) (Scheme.Modules.normModuleMapIso _ d eP ≪≫ eT)
  obtain ⟨e2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_tensor_iso (ε := ε)
    (hinv φ ψ hφ hψ d hd t M) (hinv φ ψ hφ hψ d hd t M')
  exact ⟨e1 ≪≫ e2⟩

end Transform

end G5HomCrux

end

open G5HomCrux in

theorem solution
    {R : Type u} [CommRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)

    {E : Scheme.{u}} (cE : E ⟶ Spec (CommRingCat.of R)) (φ ψ : E ⟶ C) (hφ : φ ≫ c = cE) (hψ : ψ ≫ c = cE)
    [IsFinite φ] [Flat φ] [LocallyOfFinitePresentation φ] (d : ℕ) (hd : ∀ x : C, φ.finrank x = d)

    (u : SchemeHomOver D.toBase D.toBase)
    (hu : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)) (b : SchemeHomOver t D.toBase),
      Nonempty ((h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b u)).L ≅
        Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
          (Scheme.Modules.normModule (curveChange (c := c) (c' := cE) φ hφ t) d
            ((Scheme.Modules.pullback (curveChange (c := c) (c' := cE) ψ hψ t)).obj (h.poincare.pullbackAlong b).L)))) :
    (∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s x y) u =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s
            (NeronModelInfra.schemeHomOverComp x u) (NeronModelInfra.schemeHomOverComp y u)) ∧
      D.zeroSection ≫ u.1 = D.zeroSection := by

  have hcl : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
      (hM : (algEquivZeroCut c ε).P t M),
      postComp u (h.classify t M hM) =
        h.classify t (Phi (ε := ε) φ ψ hφ hψ d hd t M) (hcut (ε := ε) φ ψ hφ hψ d hd t M hM) := by
    intro T t M hM
    apply h.classify_unique
    obtain ⟨e1⟩ := hu t (h.classify t M hM)
    obtain ⟨e2⟩ := h.classify_spec t M hM
    exact ⟨e1 ≪≫ Scheme.Modules.rigidifyMapIso _ _
      (Scheme.Modules.normModuleMapIso _ d ((Scheme.Modules.pullback _).mapIso e2))⟩
  have hhom := RepresentsRelSubPic.comp_mul_eq_mul_comp_of_transform
    (P := algEquivZeroGroupCut c ε) (P' := algEquivZeroGroupCut c ε) h h (Phi (ε := ε) φ ψ hφ hψ d hd)
    (fun t M hM => hcut (ε := ε) φ ψ hφ hψ d hd t M hM) (fun t M M' => htensor (ε := ε) φ ψ hφ hψ d hd t M M')
    (fun t => hunit (ε := ε) φ ψ hφ hψ d hd t) u (fun t M hM => hcl t M hM)
  exact ⟨fun s x y => hhom.1 s x y, hhom.2⟩

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_schemeHomOverComp_mul_eq_mul_and_zeroSection_comp_of_classifies_normModule_pullback
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_schemeHomOverComp_mul_eq_mul_and_zeroSection_comp_of_classifies_normModule_pullback (solution)
