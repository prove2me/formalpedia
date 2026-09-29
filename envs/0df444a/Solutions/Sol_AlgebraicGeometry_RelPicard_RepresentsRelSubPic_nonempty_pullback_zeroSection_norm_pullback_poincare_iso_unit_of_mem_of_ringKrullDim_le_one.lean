-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_pullback_zeroSection_norm_pullback_poincare_iso_unit_of_mem_of_ringKrullDim_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/589e21d6-ee22-5a7e-8e4d-00f769d45bd6

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_pullback_map_eq_of_isIntegrallyClosed_stalk
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_normModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_unit_iso
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullback_zeroSection_norm_pullback_poincare_iso_unit_of_mem_of_ringKrullDim_le_one
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I"
p2m_attr_erase "simp" "AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullback_zeroSection_norm_pullback_poincare_iso_unit_of_mem_of_ringKrullDim_le_one.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.resLE_comp_ι IsLocallyNoetherian Surjective Scheme.Modules.pullback Scheme.Hom stalkwise IsFinite isPullback_morphismRestrict LocallyOfFiniteType Spec IsIntegral Scheme Flat Scheme.Hom.finrank_of_isPullback Scheme.Modules.pullbackCongr Scheme.isBasis_affineOpens IsAffineOpen Scheme.Modules Scheme.Hom.resLE_comp_ι_assoc Scheme.Hom.resLE_eq_morphismRestrict LocallyOfFinitePresentation Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible.existsUnique_pullback_map_eq_of_isIntegrallyClosed_stalk Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.isInvertible_unit Scheme.Modules.nonempty_pullback_normModule_iso Scheme.Modules.normModule Scheme.Modules.normModuleFunctor Scheme.Modules.nonempty_normModule_unit_iso"
namespace ZeroSectionTriv
p2m_open "AlgebraicGeometry"

section Squares

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {c' : C' ⟶ Spec (CommRingCat.of R)} (f : C' ⟶ C) (hf : f ≫ c = c')

theorem isPullback_curveChange_fst {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    IsPullback (curveChange f hf t) (pullback.fst c' t) (pullback.fst c t) f := by
  have big : IsPullback (curveChange f hf t ≫ pullback.snd c t) (pullback.fst c' t) t (f ≫ c) := by
    rw [curveChange_snd, hf]
    exact (IsPullback.of_hasPullback c' t).flip
  have hcomm : curveChange f hf t ≫ pullback.fst c t = pullback.fst c' t ≫ f := by
    simp only [curveChange, pullback.lift_fst]
  exact IsPullback.of_right big hcomm (IsPullback.of_hasPullback c t).flip

noncomputable def sliceAt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (σ : Spec (CommRingCat.of R) ⟶ T) (hσ : σ ≫ t = 𝟙 _) :
    C ⟶ pullback c t :=
  pullback.lift (𝟙 C) (c ≫ σ) (by rw [Category.id_comp, Category.assoc, hσ, Category.comp_id])

@[scoped simp] theorem sliceAt_fst {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (σ : Spec (CommRingCat.of R) ⟶ T)
    (hσ : σ ≫ t = 𝟙 _) : sliceAt (c := c) t σ hσ ≫ pullback.fst c t = 𝟙 C :=
  pullback.lift_fst _ _ _

@[scoped simp] theorem sliceAt_snd {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (σ : Spec (CommRingCat.of R) ⟶ T)
    (hσ : σ ≫ t = 𝟙 _) : sliceAt (c := c) t σ hσ ≫ pullback.snd c t = c ≫ σ :=
  pullback.lift_snd _ _ _

theorem sliceAt_curveChange {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (σ : Spec (CommRingCat.of R) ⟶ T)
    (hσ : σ ≫ t = 𝟙 _) : sliceAt (c := c') t σ hσ ≫ curveChange f hf t = f ≫ sliceAt (c := c) t σ hσ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, sliceAt_fst, Category.comp_id]
    rw [show curveChange f hf t ≫ pullback.fst c t = pullback.fst c' t ≫ f by simp only [curveChange, pullback.lift_fst],
      ← Category.assoc, sliceAt_fst, Category.id_comp]
  · rw [Category.assoc, Category.assoc, curveChange_snd, sliceAt_snd, sliceAt_snd, ← Category.assoc, hf]

theorem isPullback_sliceAt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (σ : Spec (CommRingCat.of R) ⟶ T)
    (hσ : σ ≫ t = 𝟙 _) :
    IsPullback (sliceAt (c := c') t σ hσ) f (curveChange f hf t) (sliceAt (c := c) t σ hσ) := by
  refine IsPullback.of_right ?_ (sliceAt_curveChange f hf t σ hσ) (isPullback_curveChange_fst f hf t).flip
  rw [sliceAt_fst, sliceAt_fst]
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

end Squares

section Restrict

variable {X Y X' Y' : Scheme.{u}} (π : X ⟶ Y) (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X)
  (sq : IsPullback g' π' π g)

include sq in
theorem preimage_le (V : Y.Opens) (V' : Y'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V) : π' ⁻¹ᵁ V' ≤ g' ⁻¹ᵁ (π ⁻¹ᵁ V) := by
  intro x hx
  show (g' ≫ π).base x ∈ V
  rw [sq.w]
  exact hV' hx

include sq in

theorem isPullback_resLE (V : Y.Opens) (V' : Y'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V) :
    IsPullback (g'.resLE (π ⁻¹ᵁ V) (π' ⁻¹ᵁ V') (preimage_le π g π' g' sq V V' hV'))
      (π'.resLE V' (π' ⁻¹ᵁ V') le_rfl) (π.resLE V (π ⁻¹ᵁ V) le_rfl) (g.resLE V V' hV') := by
  have big : IsPullback ((π' ⁻¹ᵁ V').ι ≫ g') (π' ∣_ V') π (V'.ι ≫ g) :=
    (isPullback_morphismRestrict π' V').flip.paste_horiz sq
  rw [← Scheme.Hom.resLE_comp_ι g' (preimage_le π g π' g' sq V V' hV'), ← Scheme.Hom.resLE_comp_ι g hV',
    ← Scheme.Hom.resLE_eq_morphismRestrict] at big
  have right : IsPullback (π ⁻¹ᵁ V).ι (π.resLE V (π ⁻¹ᵁ V) le_rfl) π V.ι := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact (isPullback_morphismRestrict π V).flip
  refine IsPullback.of_right big ?_ right
  rw [← cancel_mono V.ι]
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
  rw [Scheme.Hom.resLE_comp_ι_assoc, Scheme.Hom.resLE_comp_ι_assoc, sq.w]

end Restrict

theorem isDomain_and_isIntegrallyClosed_stalk {X : Scheme.{u}} [IsIntegral X]
    (hnorm : ∀ U : X.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(X, U)) (x : X) :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X)) (show x ∈ (⊤ : X.Opens) from trivial)
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  haveI : IsIntegrallyClosed Γ(X, U) := hnorm U hU
  obtain ⟨y, rfl⟩ : ∃ y : U, (y : X) = x := ⟨⟨x, hxU⟩, rfl⟩
  haveI := hU.isLocalization_stalk y
  have hle : (hU.primeIdealOf y).asIdeal.primeCompl ≤ nonZeroDivisors Γ(X, U) :=
    Ideal.primeCompl_le_nonZeroDivisors _
  have h1 : IsDomain (X.presheaf.stalk (y : X)) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := (hU.primeIdealOf y).asIdeal.primeCompl) _ hle
  have h2 : IsIntegrallyClosed (X.presheaf.stalk (y : X)) :=
    isIntegrallyClosed_of_isLocalization (X.presheaf.stalk (y : X)) _ hle
  exact ⟨h1, h2⟩

end AlgebraicGeometry.ZeroSectionTriv
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullback_zeroSection_norm_pullback_poincare_iso_unit_of_mem_of_ringKrullDim_le_one.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullback_zeroSection_norm_pullback_poincare_iso_unit_of_mem_of_ringKrullDim_le_one.AlgebraicGeometry.ZeroSectionTriv"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullback_zeroSection_norm_pullback_poincare_iso_unit_of_mem_of_ringKrullDim_le_one.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.resLE_comp_ι IsLocallyNoetherian Surjective Scheme.Modules.pullback Scheme.Hom stalkwise IsFinite isPullback_morphismRestrict LocallyOfFiniteType Spec IsIntegral Scheme Flat Scheme.Hom.finrank_of_isPullback Scheme.Modules.pullbackCongr Scheme.isBasis_affineOpens IsAffineOpen Scheme.Modules Scheme.Hom.resLE_comp_ι_assoc Scheme.Hom.resLE_eq_morphismRestrict LocallyOfFinitePresentation Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible.existsUnique_pullback_map_eq_of_isIntegrallyClosed_stalk Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.isInvertible_unit Scheme.Modules.nonempty_pullback_normModule_iso Scheme.Modules.normModule Scheme.Modules.normModuleFunctor Scheme.Modules.nonempty_normModule_unit_iso"
namespace ZeroSectionTriv
p2m_open "AlgebraicGeometry"

open AlgebraicGeometry.RelPicard

noncomputable def pbComp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : Z.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N) ≅ (Scheme.Modules.pullback (f ≫ g)).obj N :=
  (Scheme.Modules.pullbackComp f g).app N

noncomputable def pbCongr {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (N : Y.Modules) :
    (Scheme.Modules.pullback f).obj N ≅ (Scheme.Modules.pullback g).obj N :=
  (Scheme.Modules.pullbackCongr h).app N

set_option maxHeartbeats 3200000 in

theorem nonempty_iso_unit_of_slice
    (R : Type) [CommRing R] [IsLocalRing R]
    {C C' : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of R)) (c' : C' ⟶ Spec (CommRingCat.of R))
    [IsIntegral C] [IsLocallyNoetherian C] (hCnorm : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (π₁ π₂ : SchemeHomOver c' c) [IsFinite π₂.1] [Surjective π₂.1]
    (D : RelativePic0Designation R c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (Nm : ∀ ⦃X Y : Scheme.{0}⦄, (X ⟶ Y) → X.Modules → Y.Modules)
    (h0 : ∀ L : (pullback c' D.toBase).Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible (Nm (curveChange π₂.1 π₂.2 D.toBase) L))
    (he : ∀ (W : (pullback c D.toBase).Opens) (d : ℕ), Flat ((curveChange π₂.1 π₂.2 D.toBase) ∣_ W) → LocallyOfFinitePresentation ((curveChange π₂.1 π₂.2 D.toBase) ∣_ W) →
          (∀ y : W, ((curveChange π₂.1 π₂.2 D.toBase) ∣_ W).finrank y = d) →
          ∀ L : (pullback c' D.toBase).Modules, Scheme.Modules.IsInvertible L →
            Nonempty ((Scheme.Modules.pullback W.ι).obj (Nm (curveChange π₂.1 π₂.2 D.toBase) L) ≅
              Scheme.Modules.normModule ((curveChange π₂.1 π₂.2 D.toBase) ∣_ W) d ((Scheme.Modules.pullback ((curveChange π₂.1 π₂.2 D.toBase) ⁻¹ᵁ W).ι).obj L)))
    (V : C.Opens) (d : ℕ) [Flat (π₂.1 ∣_ V)] [LocallyOfFinitePresentation (π₂.1 ∣_ V)]
    (hrk : ∀ y : V, (π₂.1 ∣_ V).finrank y = d)
    (hVcodim : ∀ x : C, ringKrullDim (C.presheaf.stalk x) ≤ 1 → x ∈ V) :
    Nonempty ((Scheme.Modules.pullback (ZeroSectionTriv.sliceAt (c := c) D.toBase D.zeroSection D.zeroSection_toBase)).obj (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) ≅ 𝟙_ C.Modules) := by
  have hP : Scheme.Modules.IsInvertible hD.poincare.L := hD.poincare.isInvertible
  have hL : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L) := hP.pullback _
  have hM : Scheme.Modules.IsInvertible (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) := h0 _ hL

  have hPz : Nonempty ((Scheme.Modules.pullback (ZeroSectionTriv.sliceAt (c := c) D.toBase D.zeroSection D.zeroSection_toBase)).obj hD.poincare.L ≅ 𝟙_ C.Modules) := by
    let j : C ⟶ pullback c (𝟙 (Spec (CommRingCat.of R))) := pullback.lift (𝟙 _) c (by simp)
    have hj : j ≫ baseChangeSnd c (⟨D.zeroSection, D.zeroSection_toBase⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) D.toBase) = (ZeroSectionTriv.sliceAt (c := c) D.toBase D.zeroSection D.zeroSection_toBase) := by
      apply pullback.hom_ext
      · rw [Category.assoc, sliceAt_fst, baseChangeSnd, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
          Category.id_comp]
      · rw [Category.assoc, sliceAt_snd, baseChangeSnd, pullback.lift_snd, ← Category.assoc, pullback.lift_snd]
    exact ⟨pbCongr hj.symm _ ≪≫ (pbComp j _ _).symm ≪≫ (Scheme.Modules.pullback j).mapIso hD.zero.some ≪≫
      Scheme.Modules.pullbackUnitIso j⟩

  have sqF : IsPullback (pullback.fst c' D.toBase) (curveChange π₂.1 π₂.2 D.toBase) π₂.1 (pullback.fst c D.toBase) := (isPullback_curveChange_fst π₂.1 π₂.2 D.toBase).flip
  have sqZ : IsPullback (ZeroSectionTriv.sliceAt (c := c') D.toBase D.zeroSection D.zeroSection_toBase) π₂.1 (curveChange π₂.1 π₂.2 D.toBase) (ZeroSectionTriv.sliceAt (c := c) D.toBase D.zeroSection D.zeroSection_toBase) := isPullback_sliceAt π₂.1 π₂.2 D.toBase D.zeroSection D.zeroSection_toBase
  haveI : IsFinite (curveChange π₂.1 π₂.2 D.toBase) := MorphismProperty.of_isPullback (P := @IsFinite) sqF inferInstance

  have sqFV := isPullback_resLE π₂.1 (pullback.fst c D.toBase) (curveChange π₂.1 π₂.2 D.toBase) (pullback.fst c' D.toBase) sqF V ((pullback.fst c D.toBase) ⁻¹ᵁ V) le_rfl
  rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_eq_morphismRestrict] at sqFV
  haveI : Flat ((curveChange π₂.1 π₂.2 D.toBase) ∣_ ((pullback.fst c D.toBase) ⁻¹ᵁ V)) := MorphismProperty.of_isPullback (P := @Flat) sqFV inferInstance
  haveI : LocallyOfFinitePresentation ((curveChange π₂.1 π₂.2 D.toBase) ∣_ ((pullback.fst c D.toBase) ⁻¹ᵁ V)) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) sqFV inferInstance
  haveI : IsFinite (π₂.1 ∣_ V) := MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_morphismRestrict π₂.1 V).flip inferInstance
  haveI : IsFinite ((curveChange π₂.1 π₂.2 D.toBase) ∣_ ((pullback.fst c D.toBase) ⁻¹ᵁ V)) := MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_morphismRestrict (curveChange π₂.1 π₂.2 D.toBase) ((pullback.fst c D.toBase) ⁻¹ᵁ V)).flip inferInstance
  have hrkD : ∀ y : ((pullback.fst c D.toBase) ⁻¹ᵁ V), ((curveChange π₂.1 π₂.2 D.toBase) ∣_ ((pullback.fst c D.toBase) ⁻¹ᵁ V)).finrank y = d := fun y => by
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sqFV y]
    exact hrk _

  obtain ⟨e₁⟩ := he ((pullback.fst c D.toBase) ⁻¹ᵁ V) d inferInstance inferInstance hrkD _ hL

  have hVz : V ≤ (ZeroSectionTriv.sliceAt (c := c) D.toBase D.zeroSection D.zeroSection_toBase) ⁻¹ᵁ ((pullback.fst c D.toBase) ⁻¹ᵁ V) := by
    intro x hx
    show ((ZeroSectionTriv.sliceAt (c := c) D.toBase D.zeroSection D.zeroSection_toBase) ≫ (pullback.fst c D.toBase)).base x ∈ V
    rw [sliceAt_fst]
    exact hx
  have sqZV := isPullback_resLE (curveChange π₂.1 π₂.2 D.toBase) (ZeroSectionTriv.sliceAt (c := c) D.toBase D.zeroSection D.zeroSection_toBase) π₂.1 (ZeroSectionTriv.sliceAt (c := c') D.toBase D.zeroSection D.zeroSection_toBase) sqZ ((pullback.fst c D.toBase) ⁻¹ᵁ V) V hVz
  rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_eq_morphismRestrict] at sqZV

  obtain ⟨e₂⟩ := Scheme.Modules.nonempty_pullback_normModule_iso ((curveChange π₂.1 π₂.2 D.toBase) ∣_ ((pullback.fst c D.toBase) ⁻¹ᵁ V)) d hrkD
    ((ZeroSectionTriv.sliceAt (c := c) D.toBase D.zeroSection D.zeroSection_toBase).resLE ((pullback.fst c D.toBase) ⁻¹ᵁ V) V hVz) (π₂.1 ∣_ V)
    ((ZeroSectionTriv.sliceAt (c := c') D.toBase D.zeroSection D.zeroSection_toBase).resLE ((curveChange π₂.1 π₂.2 D.toBase) ⁻¹ᵁ ((pullback.fst c D.toBase) ⁻¹ᵁ V)) (π₂.1 ⁻¹ᵁ V) (preimage_le (curveChange π₂.1 π₂.2 D.toBase) (ZeroSectionTriv.sliceAt (c := c) D.toBase D.zeroSection D.zeroSection_toBase) π₂.1 (ZeroSectionTriv.sliceAt (c := c') D.toBase D.zeroSection D.zeroSection_toBase) sqZ ((pullback.fst c D.toBase) ⁻¹ᵁ V) V hVz))
    sqZV (hL.pullback _)

  have hcomm : (ZeroSectionTriv.sliceAt (c := c') D.toBase D.zeroSection D.zeroSection_toBase).resLE ((curveChange π₂.1 π₂.2 D.toBase) ⁻¹ᵁ ((pullback.fst c D.toBase) ⁻¹ᵁ V)) (π₂.1 ⁻¹ᵁ V)
      (preimage_le (curveChange π₂.1 π₂.2 D.toBase) (ZeroSectionTriv.sliceAt (c := c) D.toBase D.zeroSection D.zeroSection_toBase) π₂.1 (ZeroSectionTriv.sliceAt (c := c') D.toBase D.zeroSection D.zeroSection_toBase) sqZ ((pullback.fst c D.toBase) ⁻¹ᵁ V) V hVz) ≫ ((curveChange π₂.1 π₂.2 D.toBase) ⁻¹ᵁ ((pullback.fst c D.toBase) ⁻¹ᵁ V)).ι ≫ (curveChange π₁.1 π₁.2 D.toBase) =
      ((π₂.1 ⁻¹ᵁ V).ι ≫ π₁.1) ≫ (ZeroSectionTriv.sliceAt (c := c) D.toBase D.zeroSection D.zeroSection_toBase) := by
    rw [Scheme.Hom.resLE_comp_ι_assoc, Category.assoc, sliceAt_curveChange π₁.1 π₁.2]
  obtain ⟨u⟩ := hPz
  let e₃ : (Scheme.Modules.pullback ((ZeroSectionTriv.sliceAt (c := c') D.toBase D.zeroSection D.zeroSection_toBase).resLE ((curveChange π₂.1 π₂.2 D.toBase) ⁻¹ᵁ ((pullback.fst c D.toBase) ⁻¹ᵁ V)) (π₂.1 ⁻¹ᵁ V)
      (preimage_le (curveChange π₂.1 π₂.2 D.toBase) (ZeroSectionTriv.sliceAt (c := c) D.toBase D.zeroSection D.zeroSection_toBase) π₂.1 (ZeroSectionTriv.sliceAt (c := c') D.toBase D.zeroSection D.zeroSection_toBase) sqZ ((pullback.fst c D.toBase) ⁻¹ᵁ V) V hVz))).obj
      ((Scheme.Modules.pullback ((curveChange π₂.1 π₂.2 D.toBase) ⁻¹ᵁ ((pullback.fst c D.toBase) ⁻¹ᵁ V)).ι).obj ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) ≅
      𝟙_ _ :=
    (Scheme.Modules.pullback _).mapIso (pbComp _ _ _) ≪≫ pbComp _ _ _ ≪≫ pbCongr hcomm _ ≪≫ (pbComp _ _ _).symm ≪≫
      (Scheme.Modules.pullback _).mapIso u ≪≫ Scheme.Modules.pullbackUnitIso _

  obtain ⟨e₄⟩ := Scheme.Modules.nonempty_normModule_unit_iso (π₂.1 ∣_ V) d hrk
  let e₅ := (Scheme.Modules.normModuleFunctor (π₂.1 ∣_ V) d).mapIso e₃ ≪≫ e₄

  have hcomm' : (ZeroSectionTriv.sliceAt (c := c) D.toBase D.zeroSection D.zeroSection_toBase).resLE ((pullback.fst c D.toBase) ⁻¹ᵁ V) V hVz ≫ (((pullback.fst c D.toBase) ⁻¹ᵁ V)).ι = V.ι ≫ (ZeroSectionTriv.sliceAt (c := c) D.toBase D.zeroSection D.zeroSection_toBase) := Scheme.Hom.resLE_comp_ι _ _
  have φV : Nonempty ((Scheme.Modules.pullback V.ι).obj ((Scheme.Modules.pullback (ZeroSectionTriv.sliceAt (c := c) D.toBase D.zeroSection D.zeroSection_toBase)).obj (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L))) ≅
      (Scheme.Modules.pullback V.ι).obj (𝟙_ C.Modules)) :=
    ⟨pbComp _ _ _ ≪≫ pbCongr hcomm'.symm _ ≪≫ (pbComp _ _ _).symm ≪≫ (Scheme.Modules.pullback _).mapIso e₁ ≪≫ e₂ ≪≫
      (by exact e₅) ≪≫ (Scheme.Modules.pullbackUnitIso V.ι).symm⟩

  have hst : ∀ x : C, IsDomain (C.presheaf.stalk x) ∧ IsIntegrallyClosed (C.presheaf.stalk x) :=
    fun x => ⟨inferInstance, hCnorm x⟩
  obtain ⟨φ⟩ := φV
  obtain ⟨⟨ψ, hψ, -⟩, hiso⟩ :=
    Scheme.Modules.IsInvertible.existsUnique_pullback_map_eq_of_isIntegrallyClosed_stalk hst V hVcodim
      (hM.pullback _) (Scheme.Modules.isInvertible_unit _) φ.hom
  exact ⟨@asIso _ _ _ _ ψ (hiso ψ hψ inferInstance)⟩

end AlgebraicGeometry.ZeroSectionTriv
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullback_zeroSection_norm_pullback_poincare_iso_unit_of_mem_of_ringKrullDim_le_one.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullback_zeroSection_norm_pullback_poincare_iso_unit_of_mem_of_ringKrullDim_le_one.AlgebraicGeometry.ZeroSectionTriv"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullback_zeroSection_norm_pullback_poincare_iso_unit_of_mem_of_ringKrullDim_le_one.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullback_zeroSection_norm_pullback_poincare_iso_unit_of_mem_of_ringKrullDim_le_one.AlgebraicGeometry.ZeroSectionTriv"

set_option maxHeartbeats 3200000 in
open AlgebraicGeometry.ZeroSectionTriv in

theorem solution

    (R : Type) [CommRing R] [IsLocalRing R]
    {C C' : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of R)) (c' : C' ⟶ Spec (CommRingCat.of R))
    [IsIntegral C] [IsLocallyNoetherian C] (hCnorm : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

    (π₁ π₂ : SchemeHomOver c' c) [IsFinite π₂.1] [Surjective π₂.1]

    (D : RelativePic0Designation R c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)

    [IsIntegral ↑(pullback c' D.toBase)] [IsIntegral ↑(pullback c D.toBase)]
    (hnorm : ∀ U : (pullback c D.toBase).Opens, IsAffineOpen U →
      IsIntegrallyClosed Γ(pullback c D.toBase, U))
    [LocallyOfFiniteType D.toBase]

    (Nm : ∀ ⦃X Y : Scheme.{0}⦄, (X ⟶ Y) → X.Modules → Y.Modules)
    (hNm :
      ∀ ⦃X Y : Scheme.{0}⦄ (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsIntegral X] [IsIntegral Y],
        (∀ U : Y.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y, U)) →

        (∀ L : X.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible (Nm π L)) ∧

        (∀ L L' : X.Modules, Scheme.Modules.IsInvertible L → Nonempty (L ≅ L') →
          Nonempty (Nm π L ≅ Nm π L')) ∧

        (∀ L L' : X.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible L' →
          Nonempty (Nm π (L ⊗ L') ≅ Nm π L ⊗ Nm π L')) ∧

        Nonempty (Nm π (𝟙_ X.Modules) ≅ 𝟙_ Y.Modules) ∧

        (∀ ⦃X' Y' : Scheme.{0}⦄ (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X), IsPullback g' π' π g →
          ∀ [Flat g] [IsIntegral X'] [IsIntegral Y'],
          (∀ U : Y'.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y', U)) →
          ∀ L : X.Modules, Scheme.Modules.IsInvertible L →
            Nonempty ((Scheme.Modules.pullback g).obj (Nm π L) ≅
              Nm π' ((Scheme.Modules.pullback g').obj L))) ∧

        (∀ (V : Y.Opens) (d : ℕ), Flat (π ∣_ V) → LocallyOfFinitePresentation (π ∣_ V) →
          (∀ y : V, (π ∣_ V).finrank y = d) →
          ∀ L : X.Modules, Scheme.Modules.IsInvertible L →
            Nonempty ((Scheme.Modules.pullback V.ι).obj (Nm π L) ≅
              Scheme.Modules.normModule (π ∣_ V) d ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L))))
    (hinv : Scheme.Modules.IsInvertible
      (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)))

    (V : C.Opens) (d : ℕ) [Flat (π₂.1 ∣_ V)] [LocallyOfFinitePresentation (π₂.1 ∣_ V)]
    (hrk : ∀ y : V, (π₂.1 ∣_ V).finrank y = d)
    (hVcodim : ∀ x : C, ringKrullDim (C.presheaf.stalk x) ≤ 1 → x ∈ V) :

    Nonempty ((Scheme.Modules.pullback (baseChangeSnd c
        (⟨D.zeroSection, D.zeroSection_toBase⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) D.toBase))).obj
      (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) ≅
      SheafOfModules.unit (pullback c (𝟙 (Spec (CommRingCat.of R)))).ringCatSheaf) ∧

    Nonempty (((RigidifiedLineBundle.ofInvertible (ε := ε)
        (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) hinv).pullbackAlong
        ⟨D.zeroSection, D.zeroSection_toBase⟩).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) (𝟙 _)).L) := by

  have sqF : IsPullback (pullback.fst c' D.toBase) (curveChange π₂.1 π₂.2 D.toBase) π₂.1 (pullback.fst c D.toBase) := (isPullback_curveChange_fst π₂.1 π₂.2 D.toBase).flip
  haveI : IsFinite (curveChange π₂.1 π₂.2 D.toBase) := MorphismProperty.of_isPullback (P := @IsFinite) sqF inferInstance
  haveI : Surjective (curveChange π₂.1 π₂.2 D.toBase) := MorphismProperty.of_isPullback (P := @Surjective) sqF inferInstance
  obtain ⟨h0, -, -, -, -, he⟩ := hNm (curveChange π₂.1 π₂.2 D.toBase) hnorm

  obtain ⟨u⟩ := nonempty_iso_unit_of_slice R c c' hCnorm ε π₁ π₂ D hD Nm h0 he V d hrk hVcodim

  have hs : (pullback.fst c (𝟙 (Spec (CommRingCat.of R)))) ≫ (ZeroSectionTriv.sliceAt (c := c) D.toBase D.zeroSection D.zeroSection_toBase) = (baseChangeSnd c (⟨D.zeroSection, D.zeroSection_toBase⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) D.toBase)) := by
    apply pullback.hom_ext
    · rw [Category.assoc, sliceAt_fst, Category.comp_id, baseChangeSnd, pullback.lift_fst, Category.comp_id]
    · rw [Category.assoc, sliceAt_snd, baseChangeSnd, pullback.lift_snd, ← Category.assoc, pullback.condition,
        Category.comp_id]
  have h1 : Nonempty ((Scheme.Modules.pullback (baseChangeSnd c (⟨D.zeroSection, D.zeroSection_toBase⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) D.toBase))).obj (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) ≅
      SheafOfModules.unit (pullback c (𝟙 (Spec (CommRingCat.of R)))).ringCatSheaf) :=
    ⟨pbCongr hs.symm _ ≪≫ (pbComp _ _ _).symm ≪≫ (Scheme.Modules.pullback _).mapIso u ≪≫ Scheme.Modules.pullbackUnitIso _⟩
  refine ⟨h1, ?_⟩

  obtain ⟨α⟩ := RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso (ε := ε) (⟨D.zeroSection, D.zeroSection_toBase⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) D.toBase) hinv
  obtain ⟨β⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε) (hinv.pullback _)
    (Scheme.Modules.isInvertible_unit _) h1.some
  obtain ⟨γ⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified
    (RigidifiedLineBundle.unit (c := c) (ε := ε) (𝟙 (Spec (CommRingCat.of R))))
  exact ⟨α ≪≫ β ≪≫ γ⟩

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullback_zeroSection_norm_pullback_poincare_iso_unit_of_mem_of_ringKrullDim_le_one
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullback_zeroSection_norm_pullback_poincare_iso_unit_of_mem_of_ringKrullDim_le_one (solution)
