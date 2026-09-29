-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_normHom_abelJacobi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/161bcaf9-a4a1-5d52-9a76-83dd9ff6123e

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_hom_of_transform
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_comp_mul_eq_mul_comp_of_transform
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_normModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_normModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_unit_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_tensor_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_invModule_ker_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_FibrewiseAlgEquivZero_ofInvertible_normModule_curveChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_isPullback_baseChangeSnd_curveChange
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_pullbackMap_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_normHom_abelJacobi
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian"

universe u

noncomputable section

namespace P2mNormHom

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

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
  (π : C' ⟶ C) (hπ : π ≫ c = c')
  [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
  (d : ℕ) (hd : ∀ y : C, π.finrank y = d)

include hd

theorem hinv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t) :
    Scheme.Modules.IsInvertible (Scheme.Modules.normModule (curveChange π hπ t) d M.L) :=
  haveI := isFinite_curveChange π hπ t
  haveI := flat_curveChange π hπ t
  haveI := locallyOfFinitePresentation_curveChange π hπ t
  Scheme.Modules.IsInvertible.normModule _ d (finrank_curveChange π hπ hd t) M.isInvertible

def Phi {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t) :
    RigidifiedLineBundle c ε t :=
  RigidifiedLineBundle.ofInvertible (ε := ε)
    (Scheme.Modules.normModule (curveChange π hπ t) d M.L) (hinv π hπ d hd t M)

theorem Phi_L {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t) :
    (Phi (ε := ε) π hπ d hd t M).L =
      (RigidifiedLineBundle.ofInvertible (ε := ε)
        (Scheme.Modules.normModule (curveChange π hπ t) d M.L) (hinv π hπ d hd t M)).L := rfl

theorem hcongr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c' ε' t)
    (h : Nonempty (M.L ≅ M'.L)) :
    Nonempty ((Phi (ε := ε) π hπ d hd t M).L ≅ (Phi (ε := ε) π hπ d hd t M').L) :=
  RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso _ _
    (Scheme.Modules.normModuleMapIso _ d h.some)

theorem hcut {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t)
    (hM : FibrewiseAlgEquivZero M) : FibrewiseAlgEquivZero (Phi (ε := ε) π hπ d hd t M) :=
  FibrewiseAlgEquivZero.ofInvertible_normModule_curveChange (ε := ε) π hπ d hd M.L M.isInvertible
    (fun k _ _ s => hM k s) (hinv π hπ d hd t M)

theorem hunit {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Nonempty ((Phi (ε := ε) π hπ d hd t (RigidifiedLineBundle.unit (c := c') (ε := ε') t)).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) t).L) := by
  haveI := isFinite_curveChange π hπ t
  haveI := flat_curveChange π hπ t
  haveI := locallyOfFinitePresentation_curveChange π hπ t
  obtain ⟨eN⟩ := Scheme.Modules.nonempty_normModule_unit_iso (curveChange π hπ t) d
    (finrank_curveChange π hπ hd t)
  obtain ⟨e1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    (hinv π hπ d hd t (RigidifiedLineBundle.unit t))
    (RigidifiedLineBundle.unit (c := c) (ε := ε) t).isInvertible eN
  obtain ⟨e2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified
    (RigidifiedLineBundle.unit (c := c) (ε := ε) t)
  exact ⟨e1 ≪≫ e2⟩

theorem htensor {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c' ε' t) :
    Nonempty ((Phi (ε := ε) π hπ d hd t (M.tensor M')).L ≅
      ((Phi (ε := ε) π hπ d hd t M).tensor (Phi (ε := ε) π hπ d hd t M')).L) := by
  haveI := isFinite_curveChange π hπ t
  haveI := flat_curveChange π hπ t
  haveI := locallyOfFinitePresentation_curveChange π hπ t
  obtain ⟨eT⟩ := Scheme.Modules.nonempty_normModule_tensor_iso (curveChange π hπ t) d
    (finrank_curveChange π hπ hd t) _ _ M.isInvertible M'.isInvertible
  obtain ⟨e1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    (hinv π hπ d hd t (M.tensor M')) ((hinv π hπ d hd t M).tensor (hinv π hπ d hd t M')) eT
  obtain ⟨e2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_tensor_iso (ε := ε)
    (hinv π hπ d hd t M) (hinv π hπ d hd t M')
  exact ⟨e1 ≪≫ e2⟩

theorem hnat {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c' ε' t) :
    Nonempty (((Phi (ε := ε) π hπ d hd t M).pullbackAlong ψ).L ≅
      (Phi (ε := ε) π hπ d hd t' (M.pullbackAlong ψ)).L) := by
  haveI := isFinite_curveChange π hπ t
  haveI := flat_curveChange π hπ t
  haveI := locallyOfFinitePresentation_curveChange π hπ t

  obtain ⟨e1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso (ε := ε) ψ
    (hinv π hπ d hd t M)

  obtain ⟨e2⟩ := Scheme.Modules.nonempty_pullback_normModule_iso (curveChange π hπ t) d
    (finrank_curveChange π hπ hd t) (baseChangeSnd c ψ) (curveChange π hπ t') (baseChangeSnd c' ψ)
    (isPullback_baseChangeSnd_curveChange π hπ ψ) M.isInvertible
  obtain ⟨e3⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    ((hinv π hπ d hd t M).pullback (baseChangeSnd c ψ)) (hinv π hπ d hd t' (M.pullbackAlong ψ)) e2
  exact ⟨e1 ≪≫ e3⟩

end Transform

section Points

theorem poincare_mul {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t D.toBase) :
    Nonempty ((h.poincare.pullbackAlong (h.relativeGroupLaw.mul t x y)).L ≅
      (h.poincare.pullbackAlong x).L ⊗ (h.poincare.pullbackAlong y).L) :=
  h.nonempty_poincare_pullbackAlong_mul_iso (T := Over.mk t)
    (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)

variable {K : Type u} [Field K]

local notation "SK" => Spec (CommRingCat.of K)

theorem norm_ofPoint_lineBundle {C C' : Scheme.{u}} (c : C ⟶ SK) (c' : C' ⟶ SK)
    [IsProper c] [SmoothOfRelativeDimension 1 c] [IsProper c'] [SmoothOfRelativeDimension 1 c']
    (π : C' ⟶ C) (hπ : π ≫ c = c') [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ y : C, π.finrank y = d)
    (y : SK ⟶ C') (hy : y ≫ c' = 𝟙 _) (x : SK ⟶ C) (hx : x ≫ c = 𝟙 _) (hyx : y ≫ π = x) :
    Nonempty (Scheme.Modules.normModule (curveChange π hπ (𝟙 SK)) d
        (RelEffCartierDiv.ofPoint c' y hy).lineBundle ≅
      (RelEffCartierDiv.ofPoint c x hx).lineBundle) := by
  haveI : IsSeparated (pullback.snd c (𝟙 SK)) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  haveI : IsSeparated (pullback.snd c' (𝟙 SK)) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  haveI := @smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c (𝟙 SK)) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c' (𝟙 SK)) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  haveI := isFinite_curveChange π hπ (𝟙 SK)
  haveI := flat_curveChange π hπ (𝟙 SK)
  haveI := locallyOfFinitePresentation_curveChange π hπ (𝟙 SK)
  obtain ⟨e⟩ := Scheme.Modules.nonempty_normModule_invModule_ker_iso (pullback.snd c (𝟙 SK))
    (pullback.snd c' (𝟙 SK)) (curveChange π hπ (𝟙 SK)) (curveChange_snd π hπ (𝟙 SK)) d
    (finrank_curveChange π hπ hd (𝟙 SK)) ⟨graphOver c' y hy, graphOver_snd c' y hy⟩
  have hg : graphOver c' y hy ≫ curveChange π hπ (𝟙 SK) = graphOver c x hx := by
    apply pullback.hom_ext
    · simp only [curveChange, Category.assoc, pullback.lift_fst, graphOver_fst_assoc, hyx, graphOver_fst]
    · simp only [curveChange, Category.assoc, pullback.lift_snd, Category.comp_id, graphOver_snd]
  exact ⟨e ≪≫ eqToIso (congrArg (fun f : SK ⟶ pullback c (𝟙 SK) => f.ker.invModule) hg)⟩

set_option maxHeartbeats 6400000 in

theorem normHom_abelJacobi
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : {q : Spec (CommRingCat.of K) ⟶ C // q ≫ c = 𝟙 _})
    (D : RelativePic0Designation K c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (aj : SchemeHomOver c D.toBase)
    (haj : ∀ x : {q : Spec (CommRingCat.of K) ⟶ C // q ≫ c = 𝟙 _},
      Nonempty ((h.poincare.pullbackAlong
          ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint c (𝟙 (Spec (CommRingCat.of K)) ≫ ε.1)
            ((Category.assoc _ _ _).trans ((congrArg (𝟙 (Spec (CommRingCat.of K)) ≫ ·) ε.2).trans
              (Category.comp_id _)))).idealModule))
    {C' : Scheme.{u}} (c' : C' ⟶ Spec (CommRingCat.of K)) [IsProper c'] [SmoothOfRelativeDimension 1 c']
    (ε' : {q : Spec (CommRingCat.of K) ⟶ C' // q ≫ c' = 𝟙 _})
    (D' : RelativePic0Designation K c')
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    (aj' : SchemeHomOver c' D'.toBase)
    (haj' : ∀ x : {q : Spec (CommRingCat.of K) ⟶ C' // q ≫ c' = 𝟙 _},
      Nonempty ((h'.poincare.pullbackAlong
          ⟨x.1 ≫ aj'.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj'.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint c' x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint c' (𝟙 (Spec (CommRingCat.of K)) ≫ ε'.1)
            ((Category.assoc _ _ _).trans ((congrArg (𝟙 (Spec (CommRingCat.of K)) ≫ ·) ε'.2).trans
              (Category.comp_id _)))).idealModule))
    (π : C' ⟶ C) (hπ : π ≫ c = c') [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ x : C, π.finrank x = d)
    (N : SchemeHomOver D'.toBase D.toBase)
    (hN : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (M : RigidifiedLineBundle c' ε' t)
        (hM : (algEquivZeroCut c' ε').P t M),
        postComp N (h'.classify t M hM) =
          h.classify t (Phi (ε := ε) π hπ d hd t M) (hcut (ε := ε) π hπ d hd t M hM))
    (y : {q : Spec (CommRingCat.of K) ⟶ C' // q ≫ c' = 𝟙 _}) :
    (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul (𝟙 _)
        ⟨(y.1 ≫ aj'.1) ≫ N.1,
          (Category.assoc _ _ _).trans ((congrArg ((y.1 ≫ aj'.1) ≫ ·) N.2).trans
            ((Category.assoc _ _ _).trans ((congrArg (y.1 ≫ ·) aj'.2).trans y.2)))⟩
        ⟨(ε'.1 ≫ π) ≫ aj.1,
          (Category.assoc _ _ _).trans ((congrArg ((ε'.1 ≫ π) ≫ ·) aj.2).trans
            ((Category.assoc _ _ _).trans ((congrArg (ε'.1 ≫ ·) hπ).trans ε'.2)))⟩ =
      ⟨(y.1 ≫ π) ≫ aj.1,
        (Category.assoc _ _ _).trans ((congrArg ((y.1 ≫ π) ≫ ·) aj.2).trans
          ((Category.assoc _ _ _).trans ((congrArg (y.1 ≫ ·) hπ).trans y.2)))⟩ := by
  haveI := isFinite_curveChange π hπ (𝟙 SK)
  haveI := flat_curveChange π hπ (𝟙 SK)
  haveI := locallyOfFinitePresentation_curveChange π hπ (𝟙 SK)
  have hd₁ := finrank_curveChange π hπ hd (𝟙 SK)

  have pε : (𝟙 SK ≫ ε.1) ≫ c = 𝟙 _ :=
    (Category.assoc _ _ _).trans ((congrArg (𝟙 SK ≫ ·) ε.2).trans (Category.comp_id _))
  have pε' : (𝟙 SK ≫ ε'.1) ≫ c' = 𝟙 _ :=
    (Category.assoc _ _ _).trans ((congrArg (𝟙 SK ≫ ·) ε'.2).trans (Category.comp_id _))
  have pb : (ε'.1 ≫ π) ≫ c = 𝟙 _ := (Category.assoc _ _ _).trans ((congrArg (ε'.1 ≫ ·) hπ).trans ε'.2)
  have pg : (y.1 ≫ π) ≫ c = 𝟙 _ := (Category.assoc _ _ _).trans ((congrArg (y.1 ≫ ·) hπ).trans y.2)
  let a' : SchemeHomOver (𝟙 SK) D'.toBase :=
    ⟨y.1 ≫ aj'.1, (Category.assoc _ _ _).trans ((congrArg (y.1 ≫ ·) aj'.2).trans y.2)⟩
  let b : SchemeHomOver (𝟙 SK) D.toBase :=
    ⟨(ε'.1 ≫ π) ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg ((ε'.1 ≫ π) ≫ ·) aj.2).trans pb)⟩
  let g : SchemeHomOver (𝟙 SK) D.toBase :=
    ⟨(y.1 ≫ π) ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg ((y.1 ≫ π) ≫ ·) aj.2).trans pg)⟩

  let M : RigidifiedLineBundle c' ε' (𝟙 SK) := h'.poincare.pullbackAlong a'
  have hM : (algEquivZeroCut c' ε').P (𝟙 SK) M :=
    (algEquivZeroCut c' ε').pullback_mem _ _ a' _ h'.poincare_mem
  have ha' : a' = h'.classify (𝟙 SK) M hM := h'.classify_unique _ M hM a' ⟨Iso.refl _⟩
  have hNa' : postComp N a' = h.classify (𝟙 SK) (Phi (ε := ε) π hπ d hd (𝟙 SK) M)
      (hcut (ε := ε) π hπ d hd (𝟙 SK) M hM) := by
    conv_lhs => rw [ha']
    exact hN (𝟙 SK) M hM
  obtain ⟨e1⟩ : Nonempty ((h.poincare.pullbackAlong (postComp N a')).L ≅
      (Phi (ε := ε) π hπ d hd (𝟙 SK) M).L) := by
    rw [hNa']
    exact h.classify_spec _ _ _

  have hOy' : Scheme.Modules.IsInvertible (RelEffCartierDiv.ofPoint c' y.1 y.2).lineBundle :=
    (RelEffCartierDiv.isInvertible_I _).isInvertible_invModule
  have hIε' : Scheme.Modules.IsInvertible (RelEffCartierDiv.ofPoint c' (𝟙 SK ≫ ε'.1) pε').idealModule :=
    (RelEffCartierDiv.isInvertible_I _).isInvertible_module
  have hOε' : Scheme.Modules.IsInvertible (RelEffCartierDiv.ofPoint c' (𝟙 SK ≫ ε'.1) pε').lineBundle :=
    (RelEffCartierDiv.isInvertible_I _).isInvertible_invModule

  obtain ⟨iM⟩ := haj' y
  obtain ⟨ib⟩ := haj ⟨ε'.1 ≫ π, pb⟩
  obtain ⟨ig⟩ := haj ⟨y.1 ≫ π, pg⟩

  obtain ⟨n1⟩ := norm_ofPoint_lineBundle c c' π hπ d hd y.1 y.2 (y.1 ≫ π) pg rfl
  obtain ⟨n2⟩ := norm_ofPoint_lineBundle c c' π hπ d hd (𝟙 SK ≫ ε'.1) pε' (ε'.1 ≫ π) pb
    (by rw [Category.id_comp])
  obtain ⟨u⟩ := Scheme.Modules.nonempty_normModule_unit_iso (curveChange π hπ (𝟙 SK)) d hd₁
  obtain ⟨t1⟩ := Scheme.Modules.nonempty_normModule_tensor_iso (curveChange π hπ (𝟙 SK)) d hd₁ _ _ hOy' hIε'
  obtain ⟨t2⟩ := Scheme.Modules.nonempty_normModule_tensor_iso (curveChange π hπ (𝟙 SK)) d hd₁ _ _ hIε' hOε'
  obtain ⟨dd⟩ := hIε'.dual.2

  have raw : Scheme.Modules.normModule (curveChange π hπ (𝟙 SK)) d M.L ⊗ (h.poincare.pullbackAlong b).L ≅
      (h.poincare.pullbackAlong g).L :=
    (Scheme.Modules.normModuleMapIso _ d iM ⊗ᵢ ib) ≪≫
    (t1 ⊗ᵢ Iso.refl _) ≪≫
    ((n1 ⊗ᵢ Iso.refl _) ⊗ᵢ (n2.symm ⊗ᵢ Iso.refl _)) ≪≫
    α_ _ _ _ ≪≫
    (Iso.refl _ ⊗ᵢ ((α_ _ _ _).symm ≪≫ (t2.symm ⊗ᵢ Iso.refl _) ≪≫
      (Scheme.Modules.normModuleMapIso _ d dd ⊗ᵢ Iso.refl _) ≪≫ (u ⊗ᵢ Iso.refl _) ≪≫ λ_ _)) ≪≫
    ig.symm

  have hinvM := hinv (ε' := ε') π hπ d hd (𝟙 SK) M
  obtain ⟨r1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified (h.poincare.pullbackAlong b)
  obtain ⟨r2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_tensor_iso (ε := ε) hinvM
    (h.poincare.pullbackAlong b).isInvertible
  obtain ⟨r3⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    (hinvM.tensor (h.poincare.pullbackAlong b).isInvertible) (h.poincare.pullbackAlong g).isInvertible raw
  obtain ⟨r4⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified (h.poincare.pullbackAlong g)
  have key : (Phi (ε := ε) π hπ d hd (𝟙 SK) M).L ⊗ (h.poincare.pullbackAlong b).L ≅
      (h.poincare.pullbackAlong g).L :=
    (Iso.refl _ ⊗ᵢ r1.symm) ≪≫ r2.symm ≪≫ r3 ≪≫ r4

  obtain ⟨emul⟩ := poincare_mul (P := algEquivZeroGroupCut c ε) h (𝟙 SK) (postComp N a') b
  exact h.ext_of_iso (𝟙 SK) _ _ ⟨emul ≪≫ (e1 ⊗ᵢ Iso.refl _) ≪≫ key⟩

end Points

end P2mNormHom

end

open P2mNormHom in
theorem solution
    {K : Type u} [Field K]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : {q : Spec (CommRingCat.of K) ⟶ C // q ≫ c = 𝟙 _})
    (D : RelativePic0Designation K c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (aj : SchemeHomOver c D.toBase)
    (haj : ∀ x : {q : Spec (CommRingCat.of K) ⟶ C // q ≫ c = 𝟙 _},
      Nonempty ((h.poincare.pullbackAlong
          ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint c (𝟙 (Spec (CommRingCat.of K)) ≫ ε.1)
            ((Category.assoc _ _ _).trans ((congrArg (𝟙 (Spec (CommRingCat.of K)) ≫ ·) ε.2).trans
              (Category.comp_id _)))).idealModule))
    {C' : Scheme.{u}} (c' : C' ⟶ Spec (CommRingCat.of K)) [IsProper c'] [SmoothOfRelativeDimension 1 c']
    (ε' : {q : Spec (CommRingCat.of K) ⟶ C' // q ≫ c' = 𝟙 _})
    (D' : RelativePic0Designation K c')
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    (aj' : SchemeHomOver c' D'.toBase)
    (haj' : ∀ x : {q : Spec (CommRingCat.of K) ⟶ C' // q ≫ c' = 𝟙 _},
      Nonempty ((h'.poincare.pullbackAlong
          ⟨x.1 ≫ aj'.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj'.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint c' x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint c' (𝟙 (Spec (CommRingCat.of K)) ≫ ε'.1)
            ((Category.assoc _ _ _).trans ((congrArg (𝟙 (Spec (CommRingCat.of K)) ≫ ·) ε'.2).trans
              (Category.comp_id _)))).idealModule))
    (π : C' ⟶ C) (hπ : π ≫ c = c') [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ x : C, π.finrank x = d) :
    ∃ N : SchemeHomOver D'.toBase D.toBase,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t D'.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c' ε') h').mul t x y) N =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t
            (NeronModelInfra.schemeHomOverComp x N) (NeronModelInfra.schemeHomOverComp y N)) ∧
      D'.zeroSection ≫ N.1 = D.zeroSection ∧
      ∀ y : {q : Spec (CommRingCat.of K) ⟶ C' // q ≫ c' = 𝟙 _},
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul (𝟙 _)
            ⟨(y.1 ≫ aj'.1) ≫ N.1,
              (Category.assoc _ _ _).trans ((congrArg ((y.1 ≫ aj'.1) ≫ ·) N.2).trans
                ((Category.assoc _ _ _).trans ((congrArg (y.1 ≫ ·) aj'.2).trans y.2)))⟩
            ⟨(ε'.1 ≫ π) ≫ aj.1,
              (Category.assoc _ _ _).trans ((congrArg ((ε'.1 ≫ π) ≫ ·) aj.2).trans
                ((Category.assoc _ _ _).trans ((congrArg (ε'.1 ≫ ·) hπ).trans ε'.2)))⟩ =
          ⟨(y.1 ≫ π) ≫ aj.1,
            (Category.assoc _ _ _).trans ((congrArg ((y.1 ≫ π) ≫ ·) aj.2).trans
              ((Category.assoc _ _ _).trans ((congrArg (y.1 ≫ ·) hπ).trans y.2)))⟩ := by

  obtain ⟨N, hN, -⟩ := RepresentsRelSubPic.existsUnique_hom_of_transform h h' (Phi (ε := ε) π hπ d hd)
    (fun t M M' e => hcongr (ε := ε) π hπ d hd t M M' e) (fun ψ M => hnat (ε := ε) π hπ d hd ψ M)
    (fun t M hM => hcut (ε := ε) π hπ d hd t M hM)

  have hhom := RepresentsRelSubPic.comp_mul_eq_mul_comp_of_transform
    (P := algEquivZeroGroupCut c ε) (P' := algEquivZeroGroupCut c' ε') h h' (Phi (ε := ε) π hπ d hd)
    (fun t M hM => hcut (ε := ε) π hπ d hd t M hM) (fun t M M' => htensor (ε := ε) π hπ d hd t M M')
    (fun t => hunit (ε := ε) π hπ d hd t) N hN
  refine ⟨N, fun t x y => hhom.1 t x y, hhom.2, fun y => ?_⟩

  exact normHom_abelJacobi c ε D h aj haj c' ε' D' h' aj' haj' π hπ d hd N (fun t M hM => hN t M hM) y

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_normHom_abelJacobi
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_normHom_abelJacobi (solution)
