-- Prove2me | solution 1 for AlgebraicCurve.Pic0.exists_schemeHomOver_pushforwardAlong_of_representsRelSubPic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/4623abbd-e85e-5776-b29c-16163351da9b

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_finite_flat_hom_of_algHom
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_normHom_abelJacobi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_exists_schemeHomOver_pushforwardAlong_of_representsRelSubPic
p2m_attr_erase "instance" "PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.Scheme.Modules.normModuleFunctor_obj AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicCurve"

universe u v w

namespace P2mAlbanesePushforward

theorem finiteAlong_of_curveModel {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
    {F' : Type w} [Field F'] [Algebra K F'] (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) : FiniteAlong K φ := by
  letI : Algebra K M'.C.functionField := M'.functionFieldAlgebra
  have hess : Algebra.EssFiniteType K M'.C.functionField :=
    AlgebraicCurve.essFiniteType_functionField M'.toBase
  have hessF' : Algebra.EssFiniteType K F' :=
    (Algebra.EssFiniteType.iff_of_algEquiv M'.ffAlgEquiv).mpr hess
  unfold FiniteAlong
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : Algebra.EssFiniteType F F' := Algebra.EssFiniteType.of_comp K F F'
  haveI : Algebra.IsAlgebraic F F' := Algebra.IsIntegral.isAlgebraic
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

section Places

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] {F' : Type w} [Field F'] [Algebra K F']

theorem inertiaDegAlong_eq_one [IsCurveOver K F] [IsCurveOver K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    w.inertiaDegAlong φ hφ = 1 := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  have h := w.deg_restrict_mul_inertiaDeg (F := F)
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed, one_mul] at h
  exact h

theorem pushforwardAlong_single_one [IsCurveOver K F] [IsCurveOver K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    Divisor.pushforwardAlong φ hφ (Finsupp.single w 1) = Finsupp.single (w.restrictAlong φ hφ) 1 := by
  rw [Divisor.pushforwardAlong_single, inertiaDegAlong_eq_one, Nat.cast_one, one_mul]

theorem pointEquivPlace_comp_eq (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (π : M'.C ⟶ M.C)
    (hcl : ∀ y : closedPoints M'.C, ∃ h : π.base y.1 ∈ closedPoints M.C,
        M.placeOfPoint ⟨π.base y.1, h⟩ = (M'.placeOfPoint y).restrictAlong φ hφ)
    (y : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _})
    (hy : (y.1 ≫ π) ≫ M.toBase = 𝟙 _) :
    M.pointEquivPlace ⟨y.1 ≫ π, hy⟩ = (M'.pointEquivPlace y).restrictAlong φ hφ := by
  obtain ⟨hmem, heq⟩ := hcl (pointEquivClosedPoint M'.toBase y)
  rw [CurveModel.pointEquivPlace_apply, CurveModel.pointEquivPlace_apply, ← heq]
  congr 1

noncomputable def retract [IsCurveOver K F'] (v₀ : Place K F') :
    Divisor K F' →+ Divisor.degZero (K := K) (F := F') :=
  AddMonoidHom.mk'
    (fun D => ⟨D - Divisor.degree D • Finsupp.single v₀ 1, by
      rw [Divisor.mem_degZero, map_sub, map_zsmul, Divisor.degree_single,
        IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one, smul_eq_mul, mul_one, sub_self]⟩)
    (fun a b => by
      apply Subtype.ext
      simp only [map_add, AddSubgroup.coe_add, add_smul]
      abel)

theorem retract_coe [IsCurveOver K F'] (v₀ : Place K F') (D : Divisor K F') :
    (retract v₀ D : Divisor K F') = D - Divisor.degree D • Finsupp.single v₀ 1 := rfl

theorem retract_single_one_coe [IsCurveOver K F'] (v₀ w : Place K F') :
    (retract v₀ (Finsupp.single w 1) : Divisor K F') = Finsupp.single w 1 - Finsupp.single v₀ 1 := by
  rw [retract_coe, Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one,
    one_smul]

theorem retract_of_mem [IsCurveOver K F'] (v₀ : Place K F') {D : Divisor K F'}
    (hD : D ∈ Divisor.degZero (K := K) (F := F')) : retract v₀ D = ⟨D, hD⟩ := by
  apply Subtype.ext
  rw [retract_coe, Divisor.mem_degZero.mp hD, zero_smul, sub_zero]

theorem degZero_addMonoidHom_ext [IsCurveOver K F'] {A : Type*} [AddGroup A] (v₀ : Place K F')
    {f g : Divisor.degZero (K := K) (F := F') →+ A}
    (hfg : ∀ w : Place K F', f (retract v₀ (Finsupp.single w 1)) = g (retract v₀ (Finsupp.single w 1))) :
    f = g := by
  have key : f.comp (retract v₀) = g.comp (retract v₀) := by
    apply Finsupp.addHom_ext'
    intro w
    apply AddMonoidHom.ext_int
    simpa using hfg w
  ext ⟨D, hD⟩
  have h := DFunLike.congr_fun key D
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, retract_of_mem v₀ hD] at h
  exact h

end Places

end P2mAlbanesePushforward

open P2mAlbanesePushforward

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K]
    (F : Type v) [Field F] [Algebra K F] [IsCurveOver K F] (M : CurveModel K F)
    (s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _})
    (D : RelativePic0Designation K M.toBase)
    (h : RepresentsRelSubPic M.toBase s (algEquivZeroCut M.toBase s) D)
    (aj : SchemeHomOver M.toBase D.toBase) (hajs : s.1 ≫ aj.1 = D.zeroSection)
    (haj : ∀ (K' : Type u) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K))
        (x : SchemeHomOver t M.toBase),
      Nonempty ((h.poincare.pullbackAlong
          ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint M.toBase x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint M.toBase (t ≫ s.1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) s.2).trans (Category.comp_id t)))).idealModule))
    (F' : Type w) [Field F'] [Algebra K F'] [IsCurveOver K F'] (M' : CurveModel K F')
    (s' : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _})
    (D' : RelativePic0Designation K M'.toBase)
    (h' : RepresentsRelSubPic M'.toBase s' (algEquivZeroCut M'.toBase s') D')
    (aj' : SchemeHomOver M'.toBase D'.toBase) (hajs' : s'.1 ≫ aj'.1 = D'.zeroSection)
    (haj' : ∀ (K' : Type u) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K))
        (x : SchemeHomOver t M'.toBase),
      Nonempty ((h'.poincare.pullbackAlong
          ⟨x.1 ≫ aj'.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj'.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint M'.toBase x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint M'.toBase (t ≫ s'.1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) s'.2).trans (Category.comp_id t)))).idealModule))
    (φ : F →ₐ[K] F') (hφi : φ.toRingHom.IsIntegral) :
    ∃ N : SchemeHomOver D'.toBase D.toBase,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t D'.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut M'.toBase s') h').mul t x y) N =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut M.toBase s) h).mul t
            (NeronModelInfra.schemeHomOverComp x N) (NeronModelInfra.schemeHomOverComp y N)) ∧
      ∀ (pts : Pic0 K F ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase)
        (pts' : Pic0 K F' ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D'.toBase),
        (∀ x y : Pic0 K F, pts (x + y) =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut M.toBase s) h).mul _
            (pts x) (pts y)) →
        (∀ x : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
          ∃ Dv : Divisor.degZero (K := K) (F := F),
            (Dv : Divisor K F) =
              Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace s) 1 ∧
            (pts (Pic0.mk Dv)).1 = x.1 ≫ aj.1) →
        (∀ x y : Pic0 K F', pts' (x + y) =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut M'.toBase s') h').mul _
            (pts' x) (pts' y)) →
        (∀ x : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _},
          ∃ Dv : Divisor.degZero (K := K) (F := F'),
            (Dv : Divisor K F') =
              Finsupp.single (M'.pointEquivPlace x) 1 - Finsupp.single (M'.pointEquivPlace s') 1 ∧
            (pts' (Pic0.mk Dv)).1 = x.1 ≫ aj'.1) →
        ∀ Dv : Divisor.degZero (K := K) (F := F'),
          (pts (Pic0.mk ⟨Divisor.pushforwardAlong φ hφi Dv,
              Divisor.pushforwardAlong_mem_degZero φ hφi Dv.2⟩)).1 =
            (pts' (Pic0.mk Dv)).1 ≫ N.1 := by
  classical

  have hfin : FiniteAlong K φ := finiteAlong_of_curveModel M' φ hφi
  obtain ⟨π, hπ, hfinπ, hflat, hlfp, hrank, -, hcl, -⟩ :=
    AlgebraicCurve.CurveModel.exists_finite_flat_hom_of_algHom M M' φ hφi hfin
  haveI := hfinπ
  haveI := hflat
  haveI := hlfp

  obtain ⟨N, hNhom, -, hNaj⟩ :=
    AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_normHom_abelJacobi M.toBase s D h aj
      (fun x => haj K (𝟙 _) x) M'.toBase s' D' h' aj' (fun x => haj' K (𝟙 _) x) π hπ
      (finrankAlong K φ) hrank
  refine ⟨N, fun t x y => hNhom t x y, ?_⟩
  intro pts pts' hadd hnorm hadd' hnorm' Dv

  letI G := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut M.toBase s) h).pointGroup
    (𝟙 (Spec (CommRingCat.of K)))
  letI G' := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut M'.toBase s') h').pointGroup
    (𝟙 (Spec (CommRingCat.of K)))

  let ptsA : Pic0 K F →+ Additive (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase) :=
    AddMonoidHom.mk' (fun x => Additive.ofMul (pts x)) (fun x y => congrArg Additive.ofMul (hadd x y))
  let ptsA' : Pic0 K F' →+ Additive (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D'.toBase) :=
    AddMonoidHom.mk' (fun x => Additive.ofMul (pts' x)) (fun x y => congrArg Additive.ofMul (hadd' x y))
  let NA : Additive (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D'.toBase) →+
      Additive (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase) :=
    AddMonoidHom.mk' (fun z => Additive.ofMul (NeronModelInfra.schemeHomOverComp (Additive.toMul z) N))
      (fun z z' => congrArg Additive.ofMul (hNhom (𝟙 _) (Additive.toMul z) (Additive.toMul z')))
  let pf : Divisor.degZero (K := K) (F := F') →+ Divisor.degZero (K := K) (F := F) :=
    AddMonoidHom.mk'
      (fun E => ⟨Divisor.pushforwardAlong φ hφi E, Divisor.pushforwardAlong_mem_degZero φ hφi E.2⟩)
      (fun a b => Subtype.ext (map_add _ _ _))
  let mkF : Divisor.degZero (K := K) (F := F) →+ Pic0 K F := QuotientAddGroup.mk' _
  let mkF' : Divisor.degZero (K := K) (F := F') →+ Pic0 K F' := QuotientAddGroup.mk' _

  let Ψ₁ : Divisor.degZero (K := K) (F := F') →+ Additive (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase) :=
    ptsA.comp (mkF.comp pf)
  let Ψ₂ : Divisor.degZero (K := K) (F := F') →+ Additive (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase) :=
    NA.comp (ptsA'.comp mkF')
  suffices hΨ : Ψ₁ = Ψ₂ by
    have hD := DFunLike.congr_fun hΨ Dv
    exact congrArg (fun z => (Additive.toMul z).1) hD

  let A : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _} →
      SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase :=
    fun x => ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩
  have hA : ∀ x : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
      pts (Pic0.mk (retract (M.pointEquivPlace s) (Finsupp.single (M.pointEquivPlace x) 1))) = A x := by
    intro x
    obtain ⟨Dx, hDx, hpt⟩ := hnorm x
    have hre : retract (M.pointEquivPlace s) (Finsupp.single (M.pointEquivPlace x) 1) = Dx :=
      Subtype.ext ((retract_single_one_coe _ _).trans hDx.symm)
    rw [hre]
    exact Subtype.ext hpt
  have hA' : ∀ y : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _},
      (pts' (Pic0.mk (retract (M'.pointEquivPlace s') (Finsupp.single (M'.pointEquivPlace y) 1)))).1 =
        y.1 ≫ aj'.1 := by
    intro y
    obtain ⟨Dy, hDy, hpt⟩ := hnorm' y
    have hre : retract (M'.pointEquivPlace s') (Finsupp.single (M'.pointEquivPlace y) 1) = Dy :=
      Subtype.ext ((retract_single_one_coe _ _).trans hDy.symm)
    rw [hre]
    exact hpt

  have hover : ∀ y : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _},
      (y.1 ≫ π) ≫ M.toBase = 𝟙 _ := fun y => by rw [Category.assoc, hπ]; exact y.2
  let img : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _} →
      {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _} := fun y => ⟨y.1 ≫ π, hover y⟩

  apply degZero_addMonoidHom_ext (M'.pointEquivPlace s')
  intro w
  obtain ⟨y, rfl⟩ := M'.pointEquivPlace.surjective w

  have hpf : pf (retract (M'.pointEquivPlace s') (Finsupp.single (M'.pointEquivPlace y) 1)) =
      retract (M.pointEquivPlace s) (Finsupp.single (M.pointEquivPlace (img y)) 1) -
        retract (M.pointEquivPlace s) (Finsupp.single (M.pointEquivPlace (img s')) 1) := by
    apply Subtype.ext
    change Divisor.pushforwardAlong φ hφi
        (retract (M'.pointEquivPlace s') (Finsupp.single (M'.pointEquivPlace y) 1) : Divisor K F') = _
    rw [AddSubgroup.coe_sub, retract_single_one_coe, retract_single_one_coe, retract_single_one_coe,
      map_sub, pushforwardAlong_single_one, pushforwardAlong_single_one,
      ← pointEquivPlace_comp_eq M M' φ hφi π hcl y (hover y),
      ← pointEquivPlace_comp_eq M M' φ hφi π hcl s' (hover s')]
    abel

  have h1 : Additive.toMul (Ψ₁ (retract (M'.pointEquivPlace s') (Finsupp.single (M'.pointEquivPlace y) 1))) =
      A (img y) * (A (img s'))⁻¹ := by
    change Additive.toMul (ptsA (mkF (pf _))) = _
    rw [hpf, map_sub, map_sub, toMul_sub]
    change pts (Pic0.mk _) * (pts (Pic0.mk _))⁻¹ = _
    rw [hA, hA]

  have h2 : Additive.toMul (Ψ₂ (retract (M'.pointEquivPlace s') (Finsupp.single (M'.pointEquivPlace y) 1))) =
      ⟨(y.1 ≫ aj'.1) ≫ N.1,
        (Category.assoc _ _ _).trans ((congrArg ((y.1 ≫ aj'.1) ≫ ·) N.2).trans
          ((Category.assoc _ _ _).trans ((congrArg (y.1 ≫ ·) aj'.2).trans y.2)))⟩ := by
    apply Subtype.ext
    change (pts' (Pic0.mk _)).1 ≫ N.1 = _
    rw [hA']

  have h3 := hNaj y
  apply Additive.toMul.injective
  rw [h1, h2]
  exact (eq_mul_inv_of_mul_eq h3).symm

end S_AlgebraicCurve_Pic0_exists_schemeHomOver_pushforwardAlong_of_representsRelSubPic
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_exists_schemeHomOver_pushforwardAlong_of_representsRelSubPic (solution)
