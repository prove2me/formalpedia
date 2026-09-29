-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mul_comp_eq_of_classifies_rigidify_normModule_of_ofPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/4caea1bd-ea48-5b82-b16b-6c53d6f95b8f

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
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_normModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_unit_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_tensor_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_invModule_ker_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_pullbackMap_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id_of_mem_opens
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_mul_comp_eq_of_classifies_rigidify_normModule_of_ofPoint
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian"

universe u

noncomputable section

namespace P3aNormAJ

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

theorem poincare_mul {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t D.toBase) :
    Nonempty ((h.poincare.pullbackAlong (h.relativeGroupLaw.mul t x y)).L ≅
      (h.poincare.pullbackAlong x).L ⊗ (h.poincare.pullbackAlong y).L) :=
  h.nonempty_poincare_pullbackAlong_mul_iso (T := Over.mk t)
    (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)

theorem norm_ofPoint_lineBundle {R : Type u} [CommRing R] {K : Type u} [Field K] {C C' : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) (c' : C' ⟶ Spec (CommRingCat.of R)) [IsSeparated c] [IsSeparated c']
    (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    [SmoothOfRelativeDimension 1 (pullback.snd c t)] [SmoothOfRelativeDimension 1 (pullback.snd c' t)]
    (π : C' ⟶ C) (hπ : π ≫ c = c') [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ y : C, π.finrank y = d)
    (y : Spec (CommRingCat.of K) ⟶ C') (hy : y ≫ c' = t) (x : Spec (CommRingCat.of K) ⟶ C) (hx : x ≫ c = t)
    (hyx : y ≫ π = x) :
    Nonempty (Scheme.Modules.normModule (curveChange π hπ t) d
        (RelEffCartierDiv.ofPoint c' y hy).lineBundle ≅
      (RelEffCartierDiv.ofPoint c x hx).lineBundle) := by
  haveI : IsSeparated (pullback.snd c t) := MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  haveI : IsSeparated (pullback.snd c' t) := MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  haveI := isFinite_curveChange π hπ t
  haveI := flat_curveChange π hπ t
  haveI := locallyOfFinitePresentation_curveChange π hπ t
  obtain ⟨e⟩ := Scheme.Modules.nonempty_normModule_invModule_ker_iso (pullback.snd c t)
    (pullback.snd c' t) (curveChange π hπ t) (curveChange_snd π hπ t) d
    (finrank_curveChange π hπ hd t) ⟨graphOver c' y hy, graphOver_snd c' y hy⟩
  have hg : graphOver c' y hy ≫ curveChange π hπ t = graphOver c x hx := by
    apply pullback.hom_ext
    · simp only [curveChange, Category.assoc, pullback.lift_fst, graphOver_fst_assoc, hyx, graphOver_fst]
    · simp only [curveChange, Category.assoc, pullback.lift_snd, Category.comp_id, graphOver_snd]
  exact ⟨e ≪≫ eqToIso (congrArg (fun f : Spec (CommRingCat.of K) ⟶ pullback c t => f.ker.invModule) hg)⟩

theorem isInvertible_I_ofPoint_field {R : Type u} [CommRing R] {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    [SmoothOfRelativeDimension 1 (pullback.snd c t)] (x : Spec (CommRingCat.of K) ⟶ C) (hx : x ≫ c = t) :
    (RelEffCartierDiv.ofPoint c x hx).I.IsInvertible := by
  haveI : IsSeparated (pullback.snd c t) := MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  haveI : SmoothOfRelativeDimension 1 ((⊤ : (pullback c t).Opens).ι ≫ pullback.snd c t) := by
    have : SmoothOfRelativeDimension (0 + 1) ((⊤ : (pullback c t).Opens).ι ≫ pullback.snd c t) := inferInstance
    simpa using this
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens (pullback.snd c t) ⊤ (graphOver c x hx)
    (graphOver_snd c x hx) trivial

end P3aNormAJ

end

open P3aNormAJ in
set_option maxHeartbeats 6400000 in

theorem solution
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)} [IsSeparated c] [IsSeparated c']
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    (π : C' ⟶ C) (hπ : π ≫ c = c') [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ x : C, π.finrank x = d)

    (N : SchemeHomOver D'.toBase D.toBase)
    (hN : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D'.toBase),
      Nonempty ((h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a N)).L ≅
        Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
          (Scheme.Modules.normModule (curveChange π hπ t) d (h'.poincare.pullbackAlong a).L)))

    {K : Type u} [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    [SmoothOfRelativeDimension 1 (pullback.snd c t)] [SmoothOfRelativeDimension 1 (pullback.snd c' t)]

    (y : SchemeHomOver t c') (xb xg : SchemeHomOver t c) (hxb : xb.1 = (t ≫ ε'.1) ≫ π) (hxg : xg.1 = y.1 ≫ π)

    (a : SchemeHomOver t D'.toBase)
    (ha : Nonempty ((h'.poincare.pullbackAlong a).L ≅
      (RelEffCartierDiv.ofPoint c' y.1 y.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint c' (t ≫ ε'.1)
          ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε'.2).trans (Category.comp_id t)))).idealModule))
    (b g : SchemeHomOver t D.toBase)
    (hb : Nonempty ((h.poincare.pullbackAlong b).L ≅
      (RelEffCartierDiv.ofPoint c xb.1 xb.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
          ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    (hg : Nonempty ((h.poincare.pullbackAlong g).L ≅
      (RelEffCartierDiv.ofPoint c xg.1 xg.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
          ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule)) :
    (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t
      (NeronModelInfra.schemeHomOverComp a N) b = g := by
  haveI := isFinite_curveChange π hπ t
  haveI := flat_curveChange π hπ t
  haveI := locallyOfFinitePresentation_curveChange π hπ t
  have hd₁ := finrank_curveChange π hπ hd t
  have pε : (t ≫ ε.1) ≫ c = t := (Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t))
  have pε' : (t ≫ ε'.1) ≫ c' = t := (Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε'.2).trans (Category.comp_id t))

  let M : RigidifiedLineBundle c' ε' t := h'.poincare.pullbackAlong a
  have hinvM : Scheme.Modules.IsInvertible (Scheme.Modules.normModule (curveChange π hπ t) d M.L) :=
    Scheme.Modules.IsInvertible.normModule _ d hd₁ M.isInvertible
  obtain ⟨e1⟩ : Nonempty ((h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a N)).L ≅
      (RigidifiedLineBundle.ofInvertible (ε := ε) (Scheme.Modules.normModule (curveChange π hπ t) d M.L) hinvM).L) := hN t a

  have hOy : Scheme.Modules.IsInvertible (RelEffCartierDiv.ofPoint c' y.1 y.2).lineBundle :=
    (isInvertible_I_ofPoint_field c' t y.1 y.2).isInvertible_invModule
  have hIε' : Scheme.Modules.IsInvertible (RelEffCartierDiv.ofPoint c' (t ≫ ε'.1) pε').idealModule :=
    (isInvertible_I_ofPoint_field c' t (t ≫ ε'.1) pε').isInvertible_module
  have hOε' : Scheme.Modules.IsInvertible (RelEffCartierDiv.ofPoint c' (t ≫ ε'.1) pε').lineBundle :=
    (isInvertible_I_ofPoint_field c' t (t ≫ ε'.1) pε').isInvertible_invModule

  obtain ⟨iM⟩ := ha
  obtain ⟨ib⟩ := hb
  obtain ⟨ig⟩ := hg

  obtain ⟨n1⟩ := norm_ofPoint_lineBundle c c' t π hπ d hd y.1 y.2 xg.1 xg.2 hxg.symm
  obtain ⟨n2⟩ := norm_ofPoint_lineBundle c c' t π hπ d hd (t ≫ ε'.1) pε' xb.1 xb.2 hxb.symm
  obtain ⟨u⟩ := Scheme.Modules.nonempty_normModule_unit_iso (curveChange π hπ t) d hd₁
  obtain ⟨t1⟩ := Scheme.Modules.nonempty_normModule_tensor_iso (curveChange π hπ t) d hd₁ _ _ hOy hIε'
  obtain ⟨t2⟩ := Scheme.Modules.nonempty_normModule_tensor_iso (curveChange π hπ t) d hd₁ _ _ hIε' hOε'
  obtain ⟨dd⟩ := hIε'.dual.2

  have raw : Scheme.Modules.normModule (curveChange π hπ t) d M.L ⊗ (h.poincare.pullbackAlong b).L ≅
      (h.poincare.pullbackAlong g).L :=
    (Scheme.Modules.normModuleMapIso _ d iM ⊗ᵢ ib) ≪≫
    (t1 ⊗ᵢ Iso.refl _) ≪≫
    ((n1 ⊗ᵢ Iso.refl _) ⊗ᵢ (n2.symm ⊗ᵢ Iso.refl _)) ≪≫
    α_ _ _ _ ≪≫
    (Iso.refl _ ⊗ᵢ ((α_ _ _ _).symm ≪≫ (t2.symm ⊗ᵢ Iso.refl _) ≪≫
      (Scheme.Modules.normModuleMapIso _ d dd ⊗ᵢ Iso.refl _) ≪≫ (u ⊗ᵢ Iso.refl _) ≪≫ λ_ _)) ≪≫
    ig.symm

  obtain ⟨r1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified (h.poincare.pullbackAlong b)
  obtain ⟨r2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_tensor_iso (ε := ε) hinvM
    (h.poincare.pullbackAlong b).isInvertible
  obtain ⟨r3⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    (hinvM.tensor (h.poincare.pullbackAlong b).isInvertible) (h.poincare.pullbackAlong g).isInvertible raw
  obtain ⟨r4⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified (h.poincare.pullbackAlong g)
  have key : (RigidifiedLineBundle.ofInvertible (ε := ε) (Scheme.Modules.normModule (curveChange π hπ t) d M.L) hinvM).L ⊗
      (h.poincare.pullbackAlong b).L ≅ (h.poincare.pullbackAlong g).L :=
    (Iso.refl _ ⊗ᵢ r1.symm) ≪≫ r2.symm ≪≫ r3 ≪≫ r4

  obtain ⟨emul⟩ := poincare_mul (P := algEquivZeroGroupCut c ε) h t (NeronModelInfra.schemeHomOverComp a N) b
  exact h.ext_of_iso t _ _ ⟨emul ≪≫ (e1 ⊗ᵢ Iso.refl _) ≪≫ key⟩

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_mul_comp_eq_of_classifies_rigidify_normModule_of_ofPoint
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_mul_comp_eq_of_classifies_rigidify_normModule_of_ofPoint (solution)
