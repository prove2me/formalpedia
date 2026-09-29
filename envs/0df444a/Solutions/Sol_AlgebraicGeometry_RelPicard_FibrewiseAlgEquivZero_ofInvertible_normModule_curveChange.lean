-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.FibrewiseAlgEquivZero.ofInvertible_normModule_curveChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/b4fd2f97-bffb-59c6-b7be-f019c3710ed8

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_normModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_unit_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_normModule
import Theorems.Thm_CategoryTheory_IsPullback_fst_pullbackMap_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_pullbackMap_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_FibrewiseAlgEquivZero_ofInvertible_normModule_curveChange
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd"
p2m_attr_erase "simp" "AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_FibrewiseAlgEquivZero_ofInvertible_normModule_curveChange.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_FibrewiseAlgEquivZero_ofInvertible_normModule_curveChange.AlgebraicGeometry.RelPicard"

universe u

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme.Hom IsFinite Spec Scheme Flat Scheme.Modules.pullbackCongr Scheme.Modules LocallyOfFinitePresentation Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.Modules.normModule Scheme.Modules.normModuleMapIso Scheme.Modules.nonempty_pullback_normModule_iso Scheme.Modules.nonempty_normModule_unit_iso Scheme.Modules.IsInvertible.normModule Scheme.Hom.finrank_pullbackMap_of_comp_eq Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd RigidifiedLineBundle fibreAt IsAlgEquivZero FibrewiseAlgEquivZero curveChange rigCorrection RigidifiedLineBundle.ofInvertible RigidifiedLineBundle.ofInvertible_L_eq_tensor"
namespace CutAux
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

abbrev mapT {X X' S T : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S) (t : T ⟶ S) (π : X' ⟶ X) (hπ : π ≫ f = f') :
    pullback f' t ⟶ pullback f t :=
  pullback.map f' t f t π (𝟙 T) (𝟙 S) (by rw [Category.comp_id, hπ]) (by rw [Category.comp_id, Category.id_comp])

section
variable {X X' S T : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S) (t : T ⟶ S) (π : X' ⟶ X) (hπ : π ≫ f = f')

theorem isFinite_mapT [IsFinite π] : IsFinite (mapT f f' t π hπ) :=
  MorphismProperty.of_isPullback (P := @IsFinite) (CategoryTheory.IsPullback.fst_pullbackMap_of_comp_eq f f' t π hπ)
    inferInstance
theorem flat_mapT [Flat π] : Flat (mapT f f' t π hπ) :=
  MorphismProperty.of_isPullback (P := @Flat) (CategoryTheory.IsPullback.fst_pullbackMap_of_comp_eq f f' t π hπ)
    inferInstance
theorem locallyOfFinitePresentation_mapT [LocallyOfFinitePresentation π] :
    LocallyOfFinitePresentation (mapT f f' t π hπ) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
    (CategoryTheory.IsPullback.fst_pullbackMap_of_comp_eq f f' t π hπ) inferInstance
theorem finrank_mapT [Flat π] [IsFinite π] {d : ℕ} (hd : ∀ x : X, π.finrank x = d) (y : ↑(pullback f t)) :
    (mapT f f' t π hπ).finrank y = d :=
  (AlgebraicGeometry.Scheme.Hom.finrank_pullbackMap_of_comp_eq f f' t π hπ y).trans (hd _)

theorem mapT_snd : mapT f f' t π hπ ≫ pullback.snd f t = pullback.snd f' t := by
  rw [pullback.lift_snd, Category.comp_id]
end

theorem isPullback_baseChange_mapT {X X' S T' T'' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S) (t' : T' ⟶ S) (t'' : T'' ⟶ S)
    (ψ : T'' ⟶ T') (hψ : ψ ≫ t' = t'') (π : X' ⟶ X) (hπ : π ≫ f = f') :
    IsPullback
      (pullback.map f' t'' f' t' (𝟙 X') ψ (𝟙 S) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hψ]))
      (mapT f f' t'' π hπ) (mapT f f' t' π hπ)
      (pullback.map f t'' f t' (𝟙 X) ψ (𝟙 S) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hψ])) := by
  have right := CategoryTheory.IsPullback.fst_pullbackMap_of_comp_eq f f' t' π hπ
  have big := CategoryTheory.IsPullback.fst_pullbackMap_of_comp_eq f f' t'' π hπ
  refine IsPullback.of_right (h₁₂ := pullback.fst f' t') (h₂₂ := pullback.fst f t') ?_ ?_ right
  · have h1 : pullback.map f' t'' f' t' (𝟙 X') ψ (𝟙 S) (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id, hψ]) ≫ pullback.fst f' t' = pullback.fst f' t'' := by
      rw [pullback.lift_fst, Category.comp_id]
    have h2 : pullback.map f t'' f t' (𝟙 X) ψ (𝟙 S) (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id, hψ]) ≫ pullback.fst f t' = pullback.fst f t'' := by
      rw [pullback.lift_fst, Category.comp_id]
    rw [h1, h2]
    exact big
  · apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]

namespace IsAlgEquivZero

private theorem _root_.AlgebraicGeometry.RelPicard.CutAux.IsAlgEquivZero.normModule {k : Type u} [Field k] {A A' : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    {a' : A' ⟶ Spec (CommRingCat.of k)} (ϖ : A' ⟶ A) (hϖ : ϖ ≫ a = a')
    [IsFinite ϖ] [Flat ϖ] [LocallyOfFinitePresentation ϖ] (d : ℕ) (hd : ∀ y : A, ϖ.finrank y = d)
    {L' : A'.Modules} (hL' : Scheme.Modules.IsInvertible L') (h : IsAlgEquivZero a' L') :
    IsAlgEquivZero a (Scheme.Modules.normModule ϖ d L') := by
  obtain ⟨T', hT, hft, hgi, M, hM, t₀, t₁, ⟨e₀⟩, ⟨e₁⟩⟩ := h

  let ϖT := mapT a a' hT ϖ hϖ
  haveI := isFinite_mapT a a' hT ϖ hϖ
  haveI := flat_mapT a a' hT ϖ hϖ
  haveI := locallyOfFinitePresentation_mapT a a' hT ϖ hϖ
  have hdT := finrank_mapT a a' hT ϖ hϖ hd

  let ϖ1 := mapT a a' (𝟙 (Spec (CommRingCat.of k))) ϖ hϖ
  haveI := isFinite_mapT a a' (𝟙 (Spec (CommRingCat.of k))) ϖ hϖ
  haveI := flat_mapT a a' (𝟙 (Spec (CommRingCat.of k))) ϖ hϖ
  haveI := locallyOfFinitePresentation_mapT a a' (𝟙 (Spec (CommRingCat.of k))) ϖ hϖ
  have hd1 := finrank_mapT a a' (𝟙 (Spec (CommRingCat.of k))) ϖ hϖ hd

  have face : ∀ tt : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) hT,
      IsPullback (baseChangeSnd a' tt) ϖ1 ϖT (baseChangeSnd a tt) := fun tt =>
    isPullback_baseChange_mapT a a' hT (𝟙 _) tt.1 tt.2 ϖ hϖ
  have front : IsPullback (pullback.fst a' (𝟙 _)) ϖ1 ϖ (pullback.fst a (𝟙 _)) :=
    CategoryTheory.IsPullback.fst_pullbackMap_of_comp_eq a a' (𝟙 _) ϖ hϖ
  refine ⟨T', hT, hft, hgi, Scheme.Modules.normModule ϖT d M,
    Scheme.Modules.IsInvertible.normModule ϖT d hdT hM, t₀, t₁, ⟨?_⟩, ⟨?_⟩⟩
  ·
    exact (Scheme.Modules.nonempty_pullback_normModule_iso ϖT d hdT _ ϖ1 _ (face t₀) hM).some ≪≫
      Scheme.Modules.normModuleMapIso ϖ1 d e₀ ≪≫
      (Scheme.Modules.nonempty_normModule_unit_iso ϖ1 d hd1).some
  ·
    exact (Scheme.Modules.nonempty_pullback_normModule_iso ϖT d hdT _ ϖ1 _ (face t₁) hM).some ≪≫
      Scheme.Modules.normModuleMapIso ϖ1 d e₁ ≪≫
      (Scheme.Modules.nonempty_pullback_normModule_iso ϖ d hd _ ϖ1 _ front hL').some.symm

end IsAlgEquivZero
p2m_export "AlgebraicGeometry.RelPicard.CutAux" "IsAlgEquivZero.normModule"

theorem nonempty_pullback_fst_ofInvertible_iso {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (L : (pullback c t).Modules)
    (hL : Scheme.Modules.IsInvertible L) {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj (RigidifiedLineBundle.ofInvertible (ε := ε) L hL).L ≅
      (Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj L) := by
  rw [RigidifiedLineBundle.ofInvertible_L_eq_tensor]

  have hD : Scheme.Modules.IsInvertible (rigCorrection ε t L) := ((hL.pullback _).dual).1
  obtain ⟨u⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k _ (hD.pullback s)
  refine ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (Iso.refl _ ⊗ᵢ ?_) ≪≫ ρ_ _⟩
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (pullback.condition (f := pullback.snd c t) (g := s))).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso u ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _

end AlgebraicGeometry.RelPicard.CutAux

open AlgebraicGeometry.RelPicard.CutAux in
theorem solution
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    (π : C' ⟶ C) (hπ : π ≫ c = c') [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ y : C, π.finrank y = d)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (L' : (Limits.pullback c' t).Modules)
    (hL' : Scheme.Modules.IsInvertible L')
    (hfae : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      IsAlgEquivZero (fibreAt c' t s)
        ((Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd c' t) s)).obj L'))
    (hinv : Scheme.Modules.IsInvertible (Scheme.Modules.normModule (curveChange π hπ t) d L')) :
    FibrewiseAlgEquivZero (RigidifiedLineBundle.ofInvertible (ε := ε) _ hinv) := by
  intro k _ _ s

  haveI : IsFinite (curveChange π hπ t) := isFinite_mapT c c' t π hπ
  haveI : Flat (curveChange π hπ t) := flat_mapT c c' t π hπ
  haveI : LocallyOfFinitePresentation (curveChange π hπ t) := locallyOfFinitePresentation_mapT c c' t π hπ
  have hdT : ∀ y, (curveChange π hπ t).finrank y = d := finrank_mapT c c' t π hπ hd

  have hcs : curveChange π hπ t ≫ Limits.pullback.snd c t = Limits.pullback.snd c' t := mapT_snd c c' t π hπ
  let πs := mapT (Limits.pullback.snd c t) (Limits.pullback.snd c' t) s (curveChange π hπ t) hcs
  haveI : IsFinite πs := isFinite_mapT _ _ s _ hcs
  haveI : Flat πs := flat_mapT _ _ s _ hcs
  haveI : LocallyOfFinitePresentation πs := locallyOfFinitePresentation_mapT _ _ s _ hcs
  have hds : ∀ y, πs.finrank y = d := finrank_mapT _ _ s _ hcs hdT
  have hπs : πs ≫ fibreAt c t s = fibreAt c' t s := by
    change πs ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _
    exact mapT_snd _ _ s _ hcs
  have sq : IsPullback (Limits.pullback.fst (Limits.pullback.snd c' t) s) πs (curveChange π hπ t)
      (Limits.pullback.fst (Limits.pullback.snd c t) s) :=
    CategoryTheory.IsPullback.fst_pullbackMap_of_comp_eq _ _ s _ hcs

  have h1 := IsAlgEquivZero.normModule πs hπs d hds (hL'.pullback _) (hfae k s)
  obtain ⟨e1⟩ := Scheme.Modules.nonempty_pullback_normModule_iso (curveChange π hπ t) d hdT _ πs _ sq hL'
  obtain ⟨e2⟩ := nonempty_pullback_fst_ofInvertible_iso (ε := ε) _ hinv s
  exact (h1.of_iso e1.symm).of_iso e2.symm

end
end S_AlgebraicGeometry_RelPicard_FibrewiseAlgEquivZero_ofInvertible_normModule_curveChange
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_FibrewiseAlgEquivZero_ofInvertible_normModule_curveChange (solution)
