-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_fibrewise_zeroScheme
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/ad2be826-ce9c-5f0f-8e92-c803395947ea

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_sectionIdeal_of_range_subset
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso_of_range_subset
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_twistModule_pullbackAlong_iso_pullback_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_twistModule_and_nonempty_pullback_iso_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_I_eq_mul_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_supportedIn_twistModule_iso_of_subsingleton_H1_of_zeroScheme
import Theorems.Thm_AlgebraicGeometry_RelPicard_relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso_of_supportedIn_of_zeroScheme
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_opens_range_subset_iff_forall_subsingleton_H1_fibre_of_twoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_mul_left_cancel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_fibrewise_zeroScheme
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 3200000

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsLocallyNoetherian IsOpenImmersion.lift SmoothOfRelativeDimension IsProper Scheme.Modules.pullback LocallyOfFiniteType.isLocallyNoetherian Scheme.Opens.range_ι Scheme.Hom LocallyOfFiniteType Spec Spec.map Scheme IsOpenImmersion Flat IsSeparated Scheme.Modules.pullbackCongr Scheme.fromSpecResidueField_apply Scheme.Modules.pullbackId Scheme.Opens.ι_apply Scheme.Modules IsNoetherian Scheme.Opens IsOpenImmersion.lift_fac Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.IdealSheafData.module RelEffCartierDiv RelEffCartierDiv.ext mapOnProdOver PullsBackOver pullsBackOver_pullbackAlong PullsBackOver.eq_pullbackAlong RelEffCartierDiv.pullbackAlong_comp Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom RelEffCartierDiv.twistModule Scheme.Modules.zeroSchemeIdeal Scheme.Modules.pullbackTensorObjIso RelPicard.isInvertible_sectionIdeal_of_range_subset Scheme.IdealSheafData.IsInvertible RelEffCartierDiv.isInvertible_I_of_supportedIn RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback_of_supportedIn RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn RelPicard.exists_relEffCartierDiv_supportedIn_twistModule_iso_of_subsingleton_H1_of_zeroScheme RelPicard.exists_opens_range_subset_iff_forall_subsingleton_H1_fibre_of_twoAffineOpenCover Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Scheme.IdealSheafData.comap_mul"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection postComp RigidifiedLineBundle fibreAt IsAlgEquivZero FibrewiseAlgEquivZero IsAlgEquivZero.of_iso IsAlgEquivZero.pullback algEquivZeroCut RigidifiedLineBundle.pullbackAlongPullbackAlongIso relSubPicPresheaf sectionIdeal sectionTwist fibreModule isInvertible_sectionIdeal_of_range_subset nonempty_pullback_sectionTwist_iso_of_range_subset exists_relEffCartierDiv_supportedIn_twistModule_iso_of_subsingleton_H1_of_zeroScheme relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso_of_supportedIn_of_zeroScheme exists_opens_range_subset_iff_forall_subsingleton_H1_fibre_of_twoAffineOpenCover"
namespace ChartOneSS
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_fibrewise_zeroScheme.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard NeronModelInfra"

theorem pullbackAlong_congr_hom {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {n : ℕ} {T T' : Scheme.{u}} {g : T ⟶ S}
    {g' : T' ⟶ S} (D : RelEffCartierDiv f n g') {φ₁ φ₂ : T ⟶ T'} (h : φ₁ = φ₂) (h₁ : φ₁ ≫ g' = g)
    (h₂ : φ₂ ≫ g' = g) : D.pullbackAlong φ₁ h₁ = D.pullbackAlong φ₂ h₂ := by
  subst h; rfl

theorem pullbackAlong_I_eq_mul {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {n m l : ℕ}
    {T' : Scheme.{u}} {g' : T' ⟶ S} (D : RelEffCartierDiv f n g') (D₀ : RelEffCartierDiv f m g')
    (E : RelEffCartierDiv f l g') (hD : D.I = D₀.I * E.I) {T : Scheme.{u}} {g : T ⟶ S} (φ : T ⟶ T')
    (hφ : φ ≫ g' = g) :
    (D.pullbackAlong φ hφ).I = (D₀.pullbackAlong φ hφ).I * (E.pullbackAlong φ hφ).I := by
  change D.I.comap _ = D₀.I.comap _ * E.I.comap _
  rw [hD, Scheme.IdealSheafData.comap_mul]

theorem OverTotal_snd_eq_of_eq {Cat : Type*} [Category Cat] {S : Cat} {G : (Over S)ᵒᵖ ⥤ Type*} {T : Cat}
    {a b : G.OverTotal T} (h : a = b) :
    b.2 = G.map (Over.homMk (𝟙 T) (by simp [h]) : Over.mk b.1 ⟶ Over.mk a.1).op a.2 := by
  subst h
  exact (Functor.map_op_apply_eq_self _ (by simp) _).symm

theorem RigidifiedLineBundle_pullbackAlong_L_eq {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) {ψ ψ' : SchemeHomOver t' t} (h : ψ.1 = ψ'.1) :
    (M.pullbackAlong ψ).L = (M.pullbackAlong ψ').L := by
  rw [Subtype.ext h]

variable (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hεU : Set.range ε.1 ⊆ (U : Set C))

omit [IsSeparated c] [SmoothOfRelativeDimension 1 (U.ι ≫ c)] in
@[reassoc (attr := simp)]
theorem rigSection_snd' {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) :
    rigSection c u ε ≫ pullback.snd c u = 𝟙 V :=
  pullback.lift_snd _ _ _

include hεU in
theorem isInvertible_sectionIdeal {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) :
    (sectionIdeal c ε u).IsInvertible :=
  AlgebraicGeometry.RelPicard.isInvertible_sectionIdeal_of_range_subset c ε U hεU u

include hεU in
theorem isInvertible_sectionTwist {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    Scheme.Modules.IsInvertible (sectionTwist c ε u n) :=
  ((isInvertible_sectionIdeal R c ε U hεU u).pow n).isInvertible_invModule

noncomputable abbrev Mγ {e : ℕ} (n : ℕ) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) {V : Scheme.{u}}
    (u : V ⟶ Spec (CommRingCat.of R)) (LV : RigidifiedLineBundle c ε u) : (pullback c u).Modules :=
  LV.L ⊗ (sectionTwist c ε u n ⊗ (Dγ.pullbackAlong u (Category.comp_id u)).idealModule)

theorem isInvertible_Dγ {e : ℕ} (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγ : Dγ.SupportedIn U)
    {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) :
    (Dγ.pullbackAlong u (Category.comp_id u)).I.IsInvertible :=
  RelEffCartierDiv.isInvertible_I_of_supportedIn U _ (hDγ.pullbackAlong u (Category.comp_id u))

include hεU in
theorem isInvertible_Mγ {e : ℕ} (n : ℕ) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγ : Dγ.SupportedIn U)
    {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) (LV : RigidifiedLineBundle c ε u) :
    Scheme.Modules.IsInvertible (Mγ R c ε n Dγ u LV) :=
  LV.isInvertible.tensor ((isInvertible_sectionTwist R c ε U hεU u n).tensor
    (isInvertible_Dγ R c U Dγ hDγ u).isInvertible_module)

section Transport

variable {e : ℕ} (n : ℕ) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγ : Dγ.SupportedIn U)
  {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
  (ψ : SchemeHomOver t' t) (L : RigidifiedLineBundle c ε t)
  {k : Type u} [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')

noncomputable def fibreIso : pullback (pullback.snd c t) (s' ≫ ψ.1) ≅ pullback (pullback.snd c t') s' :=
  pullbackLeftPullbackSndIso c t (s' ≫ ψ.1) ≪≫
    pullback.congrHom rfl (by rw [Category.assoc, ψ.2]) ≪≫ (pullbackLeftPullbackSndIso c t' s').symm

theorem fibreIso_hom_fibreAt :
    (fibreIso R c t t' ψ s').hom ≫ fibreAt c t' s' = fibreAt c t (s' ≫ ψ.1) := by
  simp only [fibreIso, fibreAt, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackLeftPullbackSndIso_inv_snd_snd, pullback.congrHom_hom, pullback.lift_snd,
    Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]

theorem fibreIso_hom_fst_baseChangeSnd :
    (fibreIso R c t t' ψ s').hom ≫ pullback.fst (pullback.snd c t') s' ≫ baseChangeSnd c ψ =
      pullback.fst (pullback.snd c t) (s' ≫ ψ.1) := by
  have hβ : baseChangeSnd c ψ =
      pullback.lift (pullback.fst c t' ≫ 𝟙 C) (pullback.snd c t' ≫ ψ.1)
        (by simp [ψ.2, pullback.condition]) := rfl
  rw [hβ]
  apply pullback.hom_ext
  · simp only [fibreIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.lift_fst, Category.comp_id,
      pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_hom, pullbackLeftPullbackSndIso_hom_fst]
  · simp only [fibreIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
      pullbackLeftPullbackSndIso_inv_fst_snd_assoc, pullback.congrHom_hom,
      Category.comp_id, pullbackLeftPullbackSndIso_hom_snd_assoc, pullback.condition]

include hεU hDγ in

theorem nonempty_Mγ_iso_pullback :
    Nonempty (Mγ R c ε n Dγ t' (L.pullbackAlong ψ) ≅
      (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (Mγ R c ε n Dγ t L)) := by
  have hcomp : (Dγ.pullbackAlong t (Category.comp_id t)).pullbackAlong ψ.1 ψ.2 =
      Dγ.pullbackAlong t' (Category.comp_id _) :=
    (RelEffCartierDiv.pullbackAlong_comp _ _ _ _ _).trans
      (pullbackAlong_congr_hom Dγ ψ.2 _ _)
  have hI : (Dγ.pullbackAlong t' (Category.comp_id _)).I =
      (Dγ.pullbackAlong t (Category.comp_id t)).I.comap (baseChangeSnd c ψ) := by
    rw [← hcomp]; rfl
  have iγ : (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (Dγ.pullbackAlong t (Category.comp_id t)).idealModule ≅
      (Dγ.pullbackAlong t' (Category.comp_id _)).idealModule := by
    haveI := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison (baseChangeSnd c ψ)
      (isInvertible_Dγ R c U Dγ hDγ t)
      (hI ▸ isInvertible_Dγ R c U Dγ hDγ t')
    exact asIso ((Dγ.pullbackAlong t (Category.comp_id t)).I.pullbackModuleComparison (baseChangeSnd c ψ)) ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.module hI).symm
  exact ⟨(Iso.refl _ ⊗ᵢ ((nonempty_pullback_sectionTwist_iso_of_range_subset R c ε U hεU ψ n).some.symm ⊗ᵢ iγ.symm)) ≪≫
      (Iso.refl _ ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ) _ _).symm) ≪≫
      (Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ) _ _).symm⟩

include hεU hDγ in

theorem nonempty_fibreModule_iso :
    Nonempty (fibreModule c t (s' ≫ ψ.1) (Mγ R c ε n Dγ t L) ≅
      (Scheme.Modules.pullback (fibreIso R c t t' ψ s').hom).obj
        (fibreModule c t' s' (Mγ R c ε n Dγ t' (L.pullbackAlong ψ)))) := by
  obtain ⟨iM⟩ := nonempty_Mγ_iso_pullback R c ε U hεU n Dγ hDγ t t' ψ L
  exact ⟨((Scheme.Modules.pullbackCongr (fibreIso_hom_fst_baseChangeSnd R c t t' ψ s')).app _).symm ≪≫
    ((Scheme.Modules.pullbackComp (fibreIso R c t t' ψ s').hom
      (pullback.fst (pullback.snd c t') s' ≫ baseChangeSnd c ψ)).app _).symm ≪≫
    (Scheme.Modules.pullback (fibreIso R c t t' ψ s').hom).mapIso
      (((Scheme.Modules.pullbackComp (pullback.fst (pullback.snd c t') s') (baseChangeSnd c ψ)).app _).symm ≪≫
        (Scheme.Modules.pullback _).mapIso iM.symm)⟩

include hεU hDγ in

theorem fibre_transport_to_t (𝒲 : (pullback (pullback.snd c t') s').TwoAffineOpenCover) :
    ∃ 𝒱 : (pullback (pullback.snd c t) (s' ≫ ψ.1)).TwoAffineOpenCover,
      Nonempty ((𝒱.sectionsOf (fibreAt c t (s' ≫ ψ.1)) (fibreModule c t (s' ≫ ψ.1) (Mγ R c ε n Dγ t L))).H1 ≃ₗ[k]
        (𝒲.sectionsOf (fibreAt c t' s') (fibreModule c t' s' (Mγ R c ε n Dγ t' (L.pullbackAlong ψ)))).H1) := by
  obtain ⟨eφ⟩ := nonempty_fibreModule_iso R c ε U hεU n Dγ hDγ t t' ψ L s'
  obtain ⟨𝒱, -, -, -, h1⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t (s' ≫ ψ.1)) (fibreAt c t' s') (fibreIso R c t t' ψ s') (fibreIso_hom_fibreAt R c t t' ψ s') 𝒲 _ _ eφ
  exact ⟨𝒱, h1⟩

include hεU hDγ in

theorem fibre_transport_to_t' (𝒲 : (pullback (pullback.snd c t) (s' ≫ ψ.1)).TwoAffineOpenCover) :
    ∃ 𝒱 : (pullback (pullback.snd c t') s').TwoAffineOpenCover,
      Nonempty ((𝒱.sectionsOf (fibreAt c t' s') (fibreModule c t' s' (Mγ R c ε n Dγ t' (L.pullbackAlong ψ)))).H1 ≃ₗ[k]
        (𝒲.sectionsOf (fibreAt c t (s' ≫ ψ.1)) (fibreModule c t (s' ≫ ψ.1) (Mγ R c ε n Dγ t L))).H1) := by
  obtain ⟨eφ⟩ := nonempty_fibreModule_iso R c ε U hεU n Dγ hDγ t t' ψ L s'
  let φ := fibreIso R c t t' ψ s'
  have hφ' : φ.symm.hom ≫ fibreAt c t (s' ≫ ψ.1) = fibreAt c t' s' := by
    rw [Iso.symm_hom, Iso.inv_comp_eq, fibreIso_hom_fibreAt]
  have e' := ((Scheme.Modules.pullbackId _).app _).symm ≪≫
    ((Scheme.Modules.pullbackCongr φ.inv_hom_id).app _).symm ≪≫
    ((Scheme.Modules.pullbackComp φ.inv φ.hom).app _).symm ≪≫
    (Scheme.Modules.pullback φ.inv).mapIso eφ.symm
  obtain ⟨𝒱, -, -, -, h1⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t' s') (fibreAt c t (s' ≫ ψ.1)) φ.symm hφ' 𝒲 _ _ e'
  exact ⟨𝒱, h1⟩

include hεU hDγ in

theorem forall_subsingleton_H1_pullbackAlong
    (h : ∀ 𝒲 : (pullback (pullback.snd c t) (s' ≫ ψ.1)).TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c t (s' ≫ ψ.1)) (fibreModule c t (s' ≫ ψ.1) (Mγ R c ε n Dγ t L))).H1)
    (𝒲 : (pullback (pullback.snd c t') s').TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c t' s') (fibreModule c t' s' (Mγ R c ε n Dγ t' (L.pullbackAlong ψ)))).H1 := by
  obtain ⟨𝒱, ⟨e1⟩⟩ := fibre_transport_to_t R c ε U hεU n Dγ hDγ t t' ψ L s' 𝒲
  haveI := h 𝒱
  exact e1.symm.toEquiv.subsingleton

include hεU hDγ in

theorem forall_subsingleton_H1_of_pullbackAlong
    (h : ∀ 𝒲 : (pullback (pullback.snd c t') s').TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c t' s') (fibreModule c t' s' (Mγ R c ε n Dγ t' (L.pullbackAlong ψ)))).H1)
    (𝒲 : (pullback (pullback.snd c t) (s' ≫ ψ.1)).TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c t (s' ≫ ψ.1)) (fibreModule c t (s' ≫ ψ.1) (Mγ R c ε n Dγ t L))).H1 := by
  obtain ⟨𝒱, ⟨e1⟩⟩ := fibre_transport_to_t' R c ε U hεU n Dγ hDγ t t' ψ L s' 𝒲
  haveI := h 𝒱
  exact e1.symm.toEquiv.subsingleton

end Transport

theorem forall_subsingleton_H1_of_iso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {F F' : (pullback c t).Modules} (i : F ≅ F') {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (h : ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1)
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F')).H1 := by
  have e : fibreModule c t s F ≅ (Scheme.Modules.pullback (Iso.refl (pullback (pullback.snd c t) s)).hom).obj
      (fibreModule c t s F') :=
    (Scheme.Modules.pullback _).mapIso i ≪≫ ((Scheme.Modules.pullbackId _).app _).symm
  obtain ⟨𝒱, -, -, -, ⟨h1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t s) (fibreAt c t s) (Iso.refl _) (Category.id_comp _) 𝒲 _ _ e
  haveI := h 𝒱
  exact h1.symm.toEquiv.subsingleton

section Chart

set_option linter.unusedSectionVars false

section Generic
omit [IsSeparated c] [SmoothOfRelativeDimension 1 (U.ι ≫ c)]

theorem uliftYonedaEquiv_uliftYoneda_map_comp {F : Scheme.{u}ᵒᵖ ⥤ Type (u + 1)} {T T' : Scheme.{u}} (ψ : T' ⟶ T)
    (f : uliftYoneda.{u + 1}.obj T ⟶ F) :
    uliftYonedaEquiv.{u + 1, u, u + 1} (uliftYoneda.{u + 1}.map ψ ≫ f) =
      F.map ψ.op (uliftYonedaEquiv.{u + 1, u, u + 1} f) :=
  (uliftYonedaEquiv_naturality f ψ.op).symm

noncomputable def pointElem {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t)
    (hL : FibrewiseAlgEquivZero L) :
    (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal.obj (op T) :=
  ⟨t, ⟨Quotient.mk _ L, hL⟩⟩

@[scoped simp] theorem pointElem_fst {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t)
    (hL : FibrewiseAlgEquivZero L) : (pointElem R c ε t L hL).1 = t := rfl

end Generic

variable [IsNoetherianRing R] [IsProper c]
  (g e : ℕ) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγ : Dγ.SupportedIn U)
  (hχ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) (g + e) ⊗ Dγ.idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) (g + e) ⊗ Dγ.idealModule))).H1 = 1)
  (hsect : ∀ ⦃V : Scheme.{u}⦄ (u : V ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType u] (M : (pullback c u).Modules),
      Scheme.Modules.IsInvertible M →
      (∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ V) (𝒲 : (pullback (pullback.snd c u) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c u s) (fibreModule c u s M)).H1 ∧
          Module.finrank k (𝒲.sectionsOf (fibreAt c u s) (fibreModule c u s M)).H0 = 1) →
      (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ V)
        (σ : 𝟙_ (pullback c (x ≫ u)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M), σ ≠ 0 →
        ∃ Dx : RelEffCartierDiv c g (x ≫ u), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U) →
      ∃ (D₀ : RelEffCartierDiv c g u) (N : V.Modules), Scheme.Modules.IsInvertible N ∧
        Nonempty (D₀.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N) ∧
        ∀ (d' : ℕ) (D' : RelEffCartierDiv c d' u) (N' : V.Modules), Scheme.Modules.IsInvertible N' → D'.SupportedIn U →
          Nonempty (D'.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N') → D'.I = D₀.I)
  (hZfibγ : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
        (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
          (L.L ⊗ (sectionTwist c ε t (g + e) ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))), σ ≠ 0 →
        ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U)
  (hH0one : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t (g + e) ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1 →
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t (g + e) ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H0 = 1)
  {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType y] (𝒟 : RelEffCartierDiv c g y) (h𝒟U : 𝒟.SupportedIn U)
  (huniv : ∀ ⦃T : Scheme.{u}⦄ (g' : T ⟶ Spec (CommRingCat.of R)) (D : RelEffCartierDiv c g g'), D.SupportedIn U →
    ∃! φ : {φ : T ⟶ Y // φ ≫ y = g'}, PullsBackOver 𝒟 φ.1 φ.2 D)
  (DY : RelEffCartierDiv c (g + e) y) (hDY : DY.I = 𝒟.I * (Dγ.pullbackAlong y (Category.comp_id y)).I) (hDYU : DY.SupportedIn U)

noncomputable def LY : RigidifiedLineBundle c ε y :=
  ⟨DY.twistModule c ε, (DY.isInvertible_twistModule_and_nonempty_pullback_iso_of_supportedIn c ε U hεU hDYU).1,
    (DY.isInvertible_twistModule_and_nonempty_pullback_iso_of_supportedIn c ε U hεU hDYU).2⟩

omit [IsNoetherianRing R] [IsProper c] in
@[scoped simp] theorem LY_L : (LY R c ε U hεU g e y DY hDYU).L = DY.twistModule c ε := rfl

section HunivAPI
omit [IsSeparated c] [SmoothOfRelativeDimension 1 (U.ι ≫ c)] [IsNoetherianRing R] [IsProper c] [LocallyOfFiniteType y]

variable {T₁ : Scheme.{u}} {g₁ : T₁ ⟶ Spec (CommRingCat.of R)} (D₁ : RelEffCartierDiv c g g₁) (hD₁ : D₁.SupportedIn U)

noncomputable def hulift : T₁ ⟶ Y := ((huniv g₁ D₁ hD₁).exists.choose).1

theorem hulift_comp : hulift R c U g y 𝒟 huniv D₁ hD₁ ≫ y = g₁ := ((huniv g₁ D₁ hD₁).exists.choose).2

theorem pullsBackOver_hulift : PullsBackOver 𝒟 (hulift R c U g y 𝒟 huniv D₁ hD₁) (hulift_comp R c U g y 𝒟 huniv D₁ hD₁) D₁ :=
  (huniv g₁ D₁ hD₁).exists.choose_spec

theorem pullbackAlong_hulift :
    𝒟.pullbackAlong (hulift R c U g y 𝒟 huniv D₁ hD₁) (hulift_comp R c U g y 𝒟 huniv D₁ hD₁) = D₁ :=
  (PullsBackOver.eq_pullbackAlong (pullsBackOver_hulift R c U g y 𝒟 huniv D₁ hD₁)).symm

theorem eq_hulift {φ : T₁ ⟶ Y} (hφ : φ ≫ y = g₁) (h : PullsBackOver 𝒟 φ hφ D₁) :
    φ = hulift R c U g y 𝒟 huniv D₁ hD₁ := by
  have := (huniv g₁ D₁ hD₁).unique (y₁ := ⟨φ, hφ⟩) (y₂ := (huniv g₁ D₁ hD₁).exists.choose) h
    (huniv g₁ D₁ hD₁).exists.choose_spec
  exact congrArg Subtype.val this

end HunivAPI

variable (UY : Y.Opens)
  (hUY : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ Y),
    Set.range ⇑s ⊆ (UY : Set Y) ↔
      ∀ (𝒲 : (pullback (pullback.snd c y) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c y s) (fibreModule c y s (Mγ R c ε (g + e) Dγ y (LY R c ε U hεU g e y DY hDYU)))).H1)

  (WY : Y.Opens)
  (hWY : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Y),
    Set.range ⇑s ⊆ (WY : Set Y) ↔
      IsAlgEquivZero (fibreAt c y s) ((Scheme.Modules.pullback (pullback.fst (pullback.snd c y) s)).obj (DY.twistModule c ε)))

include hεU hDγ hsect hZfibγ hH0one h𝒟U huniv hDY hDYU hUY hWY

theorem fibrewiseAlgEquivZero_LY_X :
    FibrewiseAlgEquivZero ((LY R c ε U hεU g e y DY hDYU).pullbackAlong
      (⟨(UY ⊓ WY).ι, rfl⟩ : SchemeHomOver ((UY ⊓ WY).ι ≫ y) y)) := by
  intro k _ _ s'

  set ψ : SchemeHomOver ((UY ⊓ WY).ι ≫ y) y := ⟨(UY ⊓ WY).ι, rfl⟩ with hψ
  let φ := fibreIso R c y ((UY ⊓ WY).ι ≫ y) ψ s'
  have hrange : Set.range ⇑(s' ≫ ψ.1) ⊆ (WY : Set Y) := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
    exact (s' z).2.2
  have h0 : IsAlgEquivZero (fibreAt c y (s' ≫ ψ.1))
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd c y) (s' ≫ ψ.1))).obj (DY.twistModule c ε)) :=
    (hWY k (s' ≫ ψ.1)).1 hrange
  have he : φ.inv ≫ fibreAt c y (s' ≫ ψ.1) = fibreAt c ((UY ⊓ WY).ι ≫ y) s' := by
    rw [Iso.inv_comp_eq]
    exact (fibreIso_hom_fibreAt R c y ((UY ⊓ WY).ι ≫ y) ψ s').symm
  have h1 := h0.pullback φ.inv he

  have hfst : φ.inv ≫ pullback.fst (pullback.snd c y) (s' ≫ ψ.1) =
      pullback.fst (pullback.snd c ((UY ⊓ WY).ι ≫ y)) s' ≫ baseChangeSnd c ψ := by
    rw [Iso.inv_comp_eq]
    exact (fibreIso_hom_fst_baseChangeSnd R c y ((UY ⊓ WY).ι ≫ y) ψ s').symm
  refine IsAlgEquivZero.of_iso ?_ h1
  exact (Scheme.Modules.pullbackComp φ.inv (pullback.fst (pullback.snd c y) (s' ≫ ψ.1))).app _ ≪≫
    (Scheme.Modules.pullbackCongr hfst).app _ ≪≫
    ((Scheme.Modules.pullbackComp (pullback.fst (pullback.snd c ((UY ⊓ WY).ι ≫ y)) s') (baseChangeSnd c ψ)).app _).symm

noncomputable def chartElem :
    (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal.obj (op ((UY ⊓ WY : Y.Opens) : Scheme.{u})) :=
  ⟨(UY ⊓ WY).ι ≫ y, ⟨Quotient.mk _ ((LY R c ε U hεU g e y DY hDYU).pullbackAlong (⟨(UY ⊓ WY).ι, rfl⟩ : SchemeHomOver ((UY ⊓ WY).ι ≫ y) y)),
    fibrewiseAlgEquivZero_LY_X R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU UY hUY WY hWY⟩⟩

@[scoped simp] theorem chartElem_fst : (chartElem R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU UY hUY WY hWY).1 = (UY ⊓ WY).ι ≫ y := rfl

noncomputable def chartMap :
    uliftYoneda.{u + 1}.obj ((UY ⊓ WY : Y.Opens) : Scheme.{u}) ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal :=
  uliftYonedaEquiv.{u + 1, u, u + 1}.symm (chartElem R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU UY hUY WY hWY)

@[scoped simp] theorem uliftYonedaEquiv_chartMap :
    uliftYonedaEquiv.{u + 1, u, u + 1} (chartMap R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU UY hUY WY hWY) = chartElem R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU UY hUY WY hWY :=
  Equiv.apply_symm_apply _ _

theorem uliftYonedaEquiv_map_comp_chartMap {T : Scheme.{u}} (φ' : T ⟶ ((UY ⊓ WY : Y.Opens) : Scheme.{u})) :
    uliftYonedaEquiv.{u + 1, u, u + 1} (uliftYoneda.{u + 1}.map φ' ≫ chartMap R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU UY hUY WY hWY) =
      (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal.map φ'.op (chartElem R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU UY hUY WY hWY) := by
  rw [uliftYonedaEquiv_uliftYoneda_map_comp, uliftYonedaEquiv_chartMap]

variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t] (L : RigidifiedLineBundle c ε t)
  (hL : FibrewiseAlgEquivZero L) (W : T.Opens)
  (hWiff : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
    Set.range ⇑s ⊆ (W : Set T) ↔
      ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (Mγ R c ε (g + e) Dγ t L))).H1)
  (D : RelEffCartierDiv c (g + e) (W.ι ≫ t)) (D₀ : RelEffCartierDiv c g (W.ι ≫ t))
  (hD : D.I = D₀.I * (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).I)
  (hDL : Nonempty (D.twistModule c ε ≅ (L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t)).L))
  (hD₀U : D₀.SupportedIn U)

include hL hWiff hD hDL hD₀U

theorem D_eq_pullbackAlong_lift : D = DY.pullbackAlong (hulift R c U g y 𝒟 huniv D₀ hD₀U) (hulift_comp R c U g y 𝒟 huniv D₀ hD₀U) := by
  refine RelEffCartierDiv.ext ?_
  rw [pullbackAlong_I_eq_mul DY 𝒟 _ hDY, pullbackAlong_hulift R c U g y 𝒟 huniv D₀ hD₀U, RelEffCartierDiv.pullbackAlong_comp,
    pullbackAlong_congr_hom Dγ (hulift_comp R c U g y 𝒟 huniv D₀ hD₀U) _ (Category.comp_id _)]
  exact hD

theorem nonempty_LY_pullbackAlong_lift_iso :
    Nonempty (((LY R c ε U hεU g e y DY hDYU).pullbackAlong (⟨hulift R c U g y 𝒟 huniv D₀ hD₀U, hulift_comp R c U g y 𝒟 huniv D₀ hD₀U⟩ : SchemeHomOver (W.ι ≫ t) y)).L ≅
      (L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t)).L) := by
  obtain ⟨i⟩ := RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback_of_supportedIn c ε U hεU
    (⟨hulift R c U g y 𝒟 huniv D₀ hD₀U, hulift_comp R c U g y 𝒟 huniv D₀ hD₀U⟩ : SchemeHomOver (W.ι ≫ t) y) DY hDYU
  exact ⟨i.symm ≪≫ eqToIso (congrArg (fun D' => RelEffCartierDiv.twistModule c ε D')
    (D_eq_pullbackAlong_lift R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU UY hUY WY hWY t L hL W hWiff D D₀ hD hDL hD₀U).symm) ≪≫ hDL.some⟩

theorem subsingleton_H1_W (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ (W : Scheme.{u}))
    (𝒲 : (pullback (pullback.snd c (W.ι ≫ t)) s).TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c (W.ι ≫ t) s) (fibreModule c (W.ι ≫ t) s
      (Mγ R c ε (g + e) Dγ (W.ι ≫ t) (L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t))))).H1 := by
  have hrange : Set.range ⇑(s ≫ W.ι) ⊆ (W : Set T) := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
    exact (s x).2
  exact forall_subsingleton_H1_pullbackAlong R c ε U hεU (g + e) Dγ hDγ t (W.ι ≫ t) ⟨W.ι, rfl⟩ L s
    ((hWiff k (s ≫ W.ι)).1 hrange) 𝒲

theorem subsingleton_H1_W' (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ (W : Scheme.{u}))
    (𝒲 : (pullback (pullback.snd c (W.ι ≫ t)) s).TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c (W.ι ≫ t) s) (fibreModule c (W.ι ≫ t) s
      (Mγ R c ε (g + e) Dγ (W.ι ≫ t)
        ((LY R c ε U hεU g e y DY hDYU).pullbackAlong (⟨hulift R c U g y 𝒟 huniv D₀ hD₀U, hulift_comp R c U g y 𝒟 huniv D₀ hD₀U⟩ : SchemeHomOver (W.ι ≫ t) y))))).H1 := by
  obtain ⟨i⟩ := nonempty_LY_pullbackAlong_lift_iso R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU UY hUY WY hWY t L hL W hWiff D D₀ hD hDL hD₀U
  exact forall_subsingleton_H1_of_iso R c (W.ι ≫ t) (i.symm ⊗ᵢ Iso.refl _) s
    (subsingleton_H1_W R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU UY hUY WY hWY t L hL W hWiff D D₀ hD hDL hD₀U k s) 𝒲

theorem range_lift_subset_UY : Set.range ⇑(hulift R c U g y 𝒟 huniv D₀ hD₀U) ⊆ (UY : Set Y) := by
  rintro _ ⟨p, rfl⟩
  have key := (hUY ((W : Scheme.{u}).residueField p) ((W : Scheme.{u}).fromSpecResidueField p ≫ hulift R c U g y 𝒟 huniv D₀ hD₀U)).2
    (fun 𝒲 => forall_subsingleton_H1_of_pullbackAlong R c ε U hεU (g + e) Dγ hDγ y (W.ι ≫ t)
      ⟨hulift R c U g y 𝒟 huniv D₀ hD₀U, hulift_comp R c U g y 𝒟 huniv D₀ hD₀U⟩ (LY R c ε U hεU g e y DY hDYU) ((W : Scheme.{u}).fromSpecResidueField p)
      (subsingleton_H1_W' R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU UY hUY WY hWY t L hL W hWiff D D₀ hD hDL hD₀U _ ((W : Scheme.{u}).fromSpecResidueField p)) 𝒲)
  refine key ⟨IsLocalRing.closedPoint _, ?_⟩
  rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

theorem range_lift_subset_WY : Set.range ⇑(hulift R c U g y 𝒟 huniv D₀ hD₀U) ⊆ (WY : Set Y) := by
  rintro _ ⟨p, rfl⟩
  classical

  let κ := (W : Scheme.{u}).residueField p
  let kb : Type u := AlgebraicClosure κ
  set sb : Spec (CommRingCat.of kb) ⟶ (W : Scheme.{u}) :=
    Spec.map (CommRingCat.ofHom (algebraMap κ kb)) ≫ (W : Scheme.{u}).fromSpecResidueField p with hsbdef
  have hsb : sb (IsLocalRing.closedPoint kb) = p := by
    change ((W : Scheme.{u}).fromSpecResidueField p) (Spec.map (CommRingCat.ofHom (algebraMap κ kb)) (IsLocalRing.closedPoint kb)) = p
    rw [show (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) (IsLocalRing.closedPoint kb) = IsLocalRing.closedPoint κ from
      Subsingleton.elim _ _, Scheme.fromSpecResidueField_apply]

  set φ₀ : SchemeHomOver (W.ι ≫ t) y := ⟨hulift R c U g y 𝒟 huniv D₀ hD₀U, hulift_comp R c U g y 𝒟 huniv D₀ hD₀U⟩ with hφ₀
  have hLW : FibrewiseAlgEquivZero (L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t)) := hL.pullback _
  have hLY : FibrewiseAlgEquivZero ((LY R c ε U hεU g e y DY hDYU).pullbackAlong φ₀) :=
    hLW.congr ⟨(nonempty_LY_pullbackAlong_lift_iso R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU UY hUY WY hWY t L hL W hWiff D D₀ hD hDL hD₀U).some.symm⟩
  have h1 := hLY kb sb

  have key : IsAlgEquivZero (fibreAt c y (sb ≫ φ₀.1))
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd c y) (sb ≫ φ₀.1))).obj (DY.twistModule c ε)) := by

    have hψ' : pullback.snd c (W.ι ≫ t) ≫ φ₀.1 = baseChangeSnd c φ₀ ≫ pullback.snd c y := by
      simp only [baseChangeSnd, pullback.lift_snd]
    have hbC : baseChangeSnd c φ₀ ≫ pullback.fst c y = pullback.fst c (W.ι ≫ t) := by
      simp only [baseChangeSnd, pullback.lift_fst, Category.comp_id]
    have H₁ : IsPullback (pullback.fst (pullback.snd c (W.ι ≫ t)) sb ≫ pullback.fst c (W.ι ≫ t))
        (pullback.snd (pullback.snd c (W.ι ≫ t)) sb) c (sb ≫ W.ι ≫ t) :=
      (IsPullback.of_hasPullback (pullback.snd c (W.ι ≫ t)) sb).paste_horiz (IsPullback.of_hasPullback c (W.ι ≫ t))
    have H₂ : IsPullback (pullback.fst (pullback.snd c y) (sb ≫ φ₀.1) ≫ pullback.fst c y)
        (pullback.snd (pullback.snd c y) (sb ≫ φ₀.1)) c (sb ≫ W.ι ≫ t) := by
      have := (IsPullback.of_hasPullback (pullback.snd c y) (sb ≫ φ₀.1)).paste_horiz (IsPullback.of_hasPullback c y)
      simpa only [Category.assoc, φ₀.2] using this
    let eI := H₁.isoIsPullback _ _ H₂
    have he : eI.hom ≫ fibreAt c y (sb ≫ φ₀.1) = fibreAt c (W.ι ≫ t) sb := IsPullback.isoIsPullback_hom_snd _ _ H₁ H₂
    have hfst : eI.hom ≫ pullback.fst (pullback.snd c y) (sb ≫ φ₀.1) =
        pullback.fst (pullback.snd c (W.ι ≫ t)) sb ≫ baseChangeSnd c φ₀ := by
      apply pullback.hom_ext
      · simp only [Category.assoc, hbC]
        exact IsPullback.isoIsPullback_hom_fst _ _ H₁ H₂
      · have h2 := IsPullback.isoIsPullback_hom_snd _ _ H₁ H₂
        simp only [Category.assoc]
        rw [← hψ', pullback.condition_assoc, pullback.condition, ← Category.assoc, h2]
    have he' : eI.inv ≫ fibreAt c (W.ι ≫ t) sb = fibreAt c y (sb ≫ φ₀.1) := by rw [← he, eI.inv_hom_id_assoc]
    have h2 : IsAlgEquivZero (fibreAt c (W.ι ≫ t) sb) ((Scheme.Modules.pullback eI.hom).obj
        ((Scheme.Modules.pullback (pullback.fst (pullback.snd c y) (sb ≫ φ₀.1))).obj (DY.twistModule c ε))) := by
      refine IsAlgEquivZero.of_iso ?_ h1
      exact ((Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr hfst).app _ ≪≫
        ((Scheme.Modules.pullbackComp _ _).app _).symm).symm
    refine IsAlgEquivZero.of_iso ?_ (h2.pullback eI.inv he')
    exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr eI.inv_hom_id).app _ ≪≫
      (Scheme.Modules.pullbackId _).app _
  have hrange := (hWY kb (sb ≫ φ₀.1)).2 key
  exact hrange ⟨IsLocalRing.closedPoint kb, by rw [Scheme.Hom.comp_apply, hsb]⟩

theorem range_lift_subset : Set.range ⇑(hulift R c U g y 𝒟 huniv D₀ hD₀U) ⊆ ((UY ⊓ WY : Y.Opens) : Set Y) := fun z hz =>
  ⟨range_lift_subset_UY R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU UY hUY WY hWY t L hL W hWiff D D₀ hD hDL hD₀U hz, range_lift_subset_WY R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU UY hUY WY hWY t L hL W hWiff D D₀ hD hDL hD₀U hz⟩

noncomputable def φ : (W : Scheme.{u}) ⟶ ((UY ⊓ WY : Y.Opens) : Scheme.{u}) :=
  IsOpenImmersion.lift (UY ⊓ WY).ι (hulift R c U g y 𝒟 huniv D₀ hD₀U)
    (by rw [Scheme.Opens.range_ι]; exact range_lift_subset R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU UY hUY WY hWY t L hL W hWiff D D₀ hD hDL hD₀U)

@[reassoc (attr := simp)]
theorem φ_ι : φ R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU UY hUY WY hWY t L hL W hWiff D D₀ hD hDL hD₀U ≫ (UY ⊓ WY).ι = hulift R c U g y 𝒟 huniv D₀ hD₀U :=
  IsOpenImmersion.lift_fac _ _ _

theorem clause_i (L' : RigidifiedLineBundle c ε t) (hL' : Nonempty (L'.L ≅ L.L))
    (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) :
    Set.range ⇑s ⊆ (W : Set T) ↔
      ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (Mγ R c ε (g + e) Dγ t L'))).H1 := by
  refine (hWiff k s).trans ⟨fun h 𝒲 => ?_, fun h 𝒲 => ?_⟩
  · exact forall_subsingleton_H1_of_iso R c t (hL'.some.symm ⊗ᵢ Iso.refl _) s h 𝒲
  · exact forall_subsingleton_H1_of_iso R c t (hL'.some ⊗ᵢ Iso.refl _) s h 𝒲

theorem clause_ii :
    uliftYoneda.{u + 1}.map (φ R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU UY hUY WY hWY t L hL W hWiff D D₀ hD hDL hD₀U) ≫
        chartMap R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU UY hUY WY hWY =
      uliftYoneda.{u + 1}.map W.ι ≫ uliftYonedaEquiv.{u + 1, u, u + 1}.symm (pointElem R c ε t L hL) := by
  apply uliftYonedaEquiv.{u + 1, u, u + 1}.injective
  rw [uliftYonedaEquiv_map_comp_chartMap, uliftYonedaEquiv_uliftYoneda_map_comp, Equiv.apply_symm_apply]
  refine Functor.OverTotal.ext' ?_ ?_
  · change φ R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU UY hUY WY hWY t L hL W hWiff D D₀ hD hDL hD₀U ≫ (UY ⊓ WY).ι ≫ y = W.ι ≫ t
    rw [φ_ι_assoc, hulift_comp R c U g y 𝒟 huniv D₀ hD₀U]
  · apply Subtype.ext
    refine Quotient.sound ⟨?_⟩
    refine RigidifiedLineBundle.pullbackAlongPullbackAlongIso _ _ _ ≪≫
      RigidifiedLineBundle.pullbackAlongPullbackAlongIso _ _ _ ≪≫
      eqToIso (RigidifiedLineBundle_pullbackAlong_L_eq _ ?_) ≪≫
      (nonempty_LY_pullbackAlong_lift_iso R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU UY hUY WY hWY t L hL W hWiff D D₀ hD hDL hD₀U).some
    simp [postComp]

theorem clause_iii {T' : Scheme.{u}} (ψ : T' ⟶ T) (φ' : T' ⟶ ((UY ⊓ WY : Y.Opens) : Scheme.{u}))
    [LocallyOfFiniteType (ψ ≫ t)]
    (hφ' : uliftYoneda.{u + 1}.map φ' ≫ chartMap R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU UY hUY WY hWY =
      uliftYoneda.{u + 1}.map ψ ≫ uliftYonedaEquiv.{u + 1, u, u + 1}.symm (pointElem R c ε t L hL)) :
    ∃ χ : T' ⟶ (W : Scheme.{u}), χ ≫ W.ι = ψ ∧
      χ ≫ φ R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y 𝒟 h𝒟U huniv DY hDY hDYU UY hUY WY hWY t L hL W hWiff D D₀ hD hDL hD₀U = φ' := by

  have E := congrArg uliftYonedaEquiv.{u + 1, u, u + 1} hφ'
  rw [uliftYonedaEquiv_map_comp_chartMap, uliftYonedaEquiv_uliftYoneda_map_comp, Equiv.apply_symm_apply] at E
  have h1 : (φ' ≫ (UY ⊓ WY).ι) ≫ y = ψ ≫ t := by
    have := congrArg Sigma.fst E
    simpa [Functor.overTotal_map_fst] using this
  let Ψ : SchemeHomOver (ψ ≫ t) t := ⟨ψ, rfl⟩
  let Φ : SchemeHomOver (ψ ≫ t) y := ⟨φ' ≫ (UY ⊓ WY).ι, h1⟩

  have eL : Nonempty ((L.pullbackAlong Ψ).L ≅ ((LY R c ε U hεU g e y DY hDYU).pullbackAlong Φ).L) := by
    have h2 := OverTotal_snd_eq_of_eq E
    obtain ⟨i⟩ := Quotient.exact (congrArg Subtype.val h2)
    exact ⟨i ≪≫ RigidifiedLineBundle.pullbackAlongPullbackAlongIso _ _ _ ≪≫
      RigidifiedLineBundle.pullbackAlongPullbackAlongIso _ _ _ ≪≫
      eqToIso (RigidifiedLineBundle_pullbackAlong_L_eq _ (by simp [postComp, Φ]))⟩

  have hD' : (DY.pullbackAlong (φ' ≫ (UY ⊓ WY).ι) h1).I =
      (𝒟.pullbackAlong (φ' ≫ (UY ⊓ WY).ι) h1).I * (Dγ.pullbackAlong (ψ ≫ t) (Category.comp_id _)).I := by
    rw [pullbackAlong_I_eq_mul DY 𝒟 _ hDY, RelEffCartierDiv.pullbackAlong_comp,
      pullbackAlong_congr_hom Dγ h1 _ (Category.comp_id _)]
  have hD'L : Nonempty ((DY.pullbackAlong (φ' ≫ (UY ⊓ WY).ι) h1).twistModule c ε ≅ (L.pullbackAlong Ψ).L) := by
    obtain ⟨i⟩ := RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback_of_supportedIn c ε U hεU Φ DY hDYU
    exact ⟨i ≪≫ eL.some.symm⟩

  have h1' : ∀ (k : Type u) [Field k] (s' : Spec (CommRingCat.of k) ⟶ T')
      (𝒲 : (pullback (pullback.snd c (ψ ≫ t)) s').TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c (ψ ≫ t) s') (fibreModule c (ψ ≫ t) s'
        (Mγ R c ε (g + e) Dγ (ψ ≫ t) (L.pullbackAlong Ψ)))).H1 := by
    intro k _ s' 𝒲
    have hrange : Set.range ⇑(s' ≫ φ' ≫ (UY ⊓ WY).ι) ⊆ (UY : Set Y) := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
      exact (φ' (s' z)).2.1
    have hY := (hUY k (s' ≫ φ' ≫ (UY ⊓ WY).ι)).1 hrange
    have hT' := forall_subsingleton_H1_pullbackAlong R c ε U hεU (g + e) Dγ hDγ y (ψ ≫ t) Φ (LY R c ε U hεU g e y DY hDYU) s' hY
    exact forall_subsingleton_H1_of_iso R c (ψ ≫ t) (eL.some.symm ⊗ᵢ Iso.refl _) s' hT' 𝒲

  obtain ⟨hrangeW, huniq⟩ := relEffCartierDiv_eq_pullbackAlong_of_twistModule_iso_of_supportedIn_of_zeroScheme R c ε U hεU g e (g + e) rfl Dγ hDγ
    hsect hZfibγ hH0one t L hL W (fun k _ s h => (hWiff k s).2 h) D D₀ hD hD₀U hDL (ψ ≫ t) Ψ
    (DY.pullbackAlong (φ' ≫ (UY ⊓ WY).ι) h1) (𝒟.pullbackAlong (φ' ≫ (UY ⊓ WY).ι) h1) hD' (h𝒟U.pullbackAlong _ h1) hD'L h1'

  have hrangeW' : Set.range ⇑ψ ⊆ Set.range ⇑W.ι := by rw [Scheme.Opens.range_ι]; exact hrangeW
  refine ⟨IsOpenImmersion.lift W.ι ψ hrangeW', IsOpenImmersion.lift_fac _ _ _, ?_⟩
  have hχt : IsOpenImmersion.lift W.ι ψ hrangeW' ≫ W.ι ≫ t = ψ ≫ t := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]

  have hDD := huniq (IsOpenImmersion.lift W.ι ψ hrangeW') (IsOpenImmersion.lift_fac _ _ _)
  have hI : (𝒟.pullbackAlong (φ' ≫ (UY ⊓ WY).ι) h1).I * (Dγ.pullbackAlong (ψ ≫ t) (Category.comp_id _)).I =
      (D₀.pullbackAlong (IsOpenImmersion.lift W.ι ψ hrangeW') hχt).I *
        (Dγ.pullbackAlong (ψ ≫ t) (Category.comp_id _)).I := by
    rw [← hD', hDD, pullbackAlong_I_eq_mul D D₀ _ hD _ hχt, RelEffCartierDiv.pullbackAlong_comp,
      pullbackAlong_congr_hom Dγ hχt _ (Category.comp_id _)]
  have hI' : (𝒟.pullbackAlong (φ' ≫ (UY ⊓ WY).ι) h1).I = (D₀.pullbackAlong (IsOpenImmersion.lift W.ι ψ hrangeW') hχt).I := by
    rw [mul_comm, mul_comm (D₀.pullbackAlong _ hχt).I] at hI
    exact (isInvertible_Dγ R c U Dγ hDγ (ψ ≫ t)).mul_left_cancel hI

  have e1 : φ' ≫ (UY ⊓ WY).ι = hulift R c U g y 𝒟 huniv (𝒟.pullbackAlong (φ' ≫ (UY ⊓ WY).ι) h1) (h𝒟U.pullbackAlong _ h1) :=
    eq_hulift R c U g y 𝒟 huniv _ (h𝒟U.pullbackAlong _ h1) h1 (pullsBackOver_pullbackAlong 𝒟 (φ' ≫ (UY ⊓ WY).ι) h1)
  have e2 : IsOpenImmersion.lift W.ι ψ hrangeW' ≫ hulift R c U g y 𝒟 huniv D₀ hD₀U = hulift R c U g y 𝒟 huniv (𝒟.pullbackAlong (φ' ≫ (UY ⊓ WY).ι) h1) (h𝒟U.pullbackAlong _ h1) := by
    refine eq_hulift R c U g y 𝒟 huniv _ (h𝒟U.pullbackAlong _ h1) (by rw [Category.assoc, hulift_comp R c U g y 𝒟 huniv D₀ hD₀U, hχt]) ?_
    change (𝒟.pullbackAlong (IsOpenImmersion.lift W.ι ψ hrangeW' ≫ hulift R c U g y 𝒟 huniv D₀ hD₀U) _).I = (𝒟.pullbackAlong (φ' ≫ (UY ⊓ WY).ι) h1).I
    rw [hI', ← RelEffCartierDiv.pullbackAlong_comp 𝒟 (hulift R c U g y 𝒟 huniv D₀ hD₀U) (hulift_comp R c U g y 𝒟 huniv D₀ hD₀U) _ hχt, pullbackAlong_hulift R c U g y 𝒟 huniv D₀ hD₀U]
  rw [← cancel_mono (UY ⊓ WY).ι, Category.assoc, φ_ι, e2, ← e1]

end Chart
end AlgebraicGeometry.RelPicard.ChartOneSS
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_fibrewise_zeroScheme.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard.ChartOneSS"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_fibrewise_zeroScheme.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_fibrewise_zeroScheme.AlgebraicGeometry"

open CategoryTheory CategoryTheory.Limits Opposite _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_fibrewise_zeroScheme.AlgebraicGeometry _root_.AlgebraicGeometry.RelPicard _root_.P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_fibrewise_zeroScheme.AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.RelPicard.ChartOneSS in

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c]
    (𝒱 : C.TwoAffineOpenCover)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (hεU : Set.range ε.1 ⊆ (U : Set C))

    (g e r : ℕ) (hr : g + e = r)

    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (𝟙_ (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).Modules)).H1 = g)

    (Y : Scheme.{u}) (y : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType y] [CompactSpace Y]
    (Duniv : RelEffCartierDiv c g y) (hDunivU : Duniv.SupportedIn U)
    (huniv : ∀ ⦃T : Scheme.{u}⦄ (g' : T ⟶ Spec (CommRingCat.of R)) (D : RelEffCartierDiv c g g'), D.SupportedIn U →
        ∃! φ : {φ : T ⟶ Y // φ ≫ y = g'}, PullsBackOver Duniv φ.1 φ.2 D)
    (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
    (hDγ : Dγ.SupportedIn U)
    (hχ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H1 = 1)

    (hsect : ∀ ⦃V : Scheme.{u}⦄ (u : V ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType u] (M : (pullback c u).Modules),
      Scheme.Modules.IsInvertible M →
      (∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ V) (𝒲 : (pullback (pullback.snd c u) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c u s) (fibreModule c u s M)).H1 ∧
          Module.finrank k (𝒲.sectionsOf (fibreAt c u s) (fibreModule c u s M)).H0 = 1) →
      (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ V)
        (σ : 𝟙_ (pullback c (x ≫ u)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M), σ ≠ 0 →
        ∃ Dx : RelEffCartierDiv c g (x ≫ u), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U) →
      ∃ (D₀ : RelEffCartierDiv c g u) (N : V.Modules), Scheme.Modules.IsInvertible N ∧
        Nonempty (D₀.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N) ∧
        ∀ (d' : ℕ) (D' : RelEffCartierDiv c d' u) (N' : V.Modules), Scheme.Modules.IsInvertible N' → D'.SupportedIn U →
          Nonempty (D'.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N') → D'.I = D₀.I)

    (hZfibγ : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
        (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))), σ ≠ 0 →
        ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U)

    (hH0one : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1 →
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H0 = 1)

    (havoid : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (D₀ : RelEffCartierDiv c g t) (N : T.Modules), Scheme.Modules.IsInvertible N →
        Nonempty (D₀.lineBundle ≅
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)) ⊗
            (Scheme.Modules.pullback (pullback.snd c t)).obj N) →
        D₀.SupportedIn U)

    (hcut : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (D : RelEffCartierDiv c r t) (D₀ : RelEffCartierDiv c g t), D₀.SupportedIn U →
      D.I = D₀.I * (Dγ.pullbackAlong t (Category.comp_id t)).I →
      ∃ W : T.Opens, ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
        Set.range ⇑s ⊆ (W : Set T) ↔
          IsAlgEquivZero (fibreAt c t s)
            ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj (D.twistModule c ε))) :
    ∃ (X : Scheme.{u}) (f : uliftYoneda.{u + 1}.obj X ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal),
      LocallyOfFiniteType (uliftYonedaEquiv f).1 ∧ CompactSpace X ∧
      (∃ j : X ⟶ Y, IsOpenImmersion j ∧ j ≫ y = (uliftYonedaEquiv f).1) ∧
      ∀ ⦃T : Scheme.{u}⦄ (x : uliftYoneda.{u + 1}.obj T ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal),
        LocallyOfFiniteType (uliftYonedaEquiv x).1 →
        ∃ (U' : T.Opens) (φ : (↑U' : Scheme.{u}) ⟶ X),
          (∀ (L : RigidifiedLineBundle c ε (uliftYonedaEquiv x).1), Quotient.mk _ L = (uliftYonedaEquiv x).2.1 →
            ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
              Set.range ⇑s ⊆ (U' : Set T) ↔
                ∀ (𝒲 : (pullback (pullback.snd c (uliftYonedaEquiv x).1) s).TwoAffineOpenCover),
                  Subsingleton (𝒲.sectionsOf (fibreAt c (uliftYonedaEquiv x).1 s) (fibreModule c (uliftYonedaEquiv x).1 s
                    (L.L ⊗ (sectionTwist c ε (uliftYonedaEquiv x).1 r ⊗
                      (Dγ.pullbackAlong (uliftYonedaEquiv x).1 (Category.comp_id _)).idealModule)))).H1) ∧
          uliftYoneda.{u + 1}.map φ ≫ f = uliftYoneda.{u + 1}.map U'.ι ≫ x ∧
          ∀ ⦃T' : Scheme.{u}⦄ (ψ : T' ⟶ T) (φ' : T' ⟶ X),
            LocallyOfFiniteType (ψ ≫ (uliftYonedaEquiv x).1) →
            uliftYoneda.{u + 1}.map φ' ≫ f = uliftYoneda.{u + 1}.map ψ ≫ x →
            ∃ χ : T' ⟶ ↑U', χ ≫ U'.ι = ψ ∧ χ ≫ φ = φ' := by
  subst hr

  obtain ⟨DY, hDY, hDYU⟩ := RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn U Duniv
    (Dγ.pullbackAlong y (Category.comp_id y)) hDunivU (hDγ.pullbackAlong y (Category.comp_id y))

  obtain ⟨UY, hUY⟩ := AlgebraicGeometry.RelPicard.exists_opens_range_subset_iff_forall_subsingleton_H1_fibre_of_twoAffineOpenCover R c 𝒱 y
    (Mγ R c ε (g + e) Dγ y (LY R c ε U hεU g e y DY hDYU)) (isInvertible_Mγ R c ε U hεU (g + e) Dγ hDγ y _)
  obtain ⟨WY, hWY⟩ := hcut y DY Duniv hDunivU hDY
  refine ⟨((UY ⊓ WY : Y.Opens) : Scheme.{u}),
    chartMap R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y Duniv hDunivU huniv DY hDY hDYU UY hUY WY hWY, ?_, ?_, ?_, ?_⟩
  ·
    rw [uliftYonedaEquiv_chartMap]
    change LocallyOfFiniteType ((UY ⊓ WY).ι ≫ y)
    infer_instance
  ·
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian y
    haveI : IsNoetherian Y := {}
    change CompactSpace ((UY ⊓ WY : Y.Opens) : Set Y)
    exact isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  ·
    refine ⟨(UY ⊓ WY).ι, inferInstance, ?_⟩
    rw [uliftYonedaEquiv_chartMap]; rfl
  intro T x hx

  generalize hxa : uliftYonedaEquiv x = a at hx ⊢
  obtain rfl : x = uliftYonedaEquiv.symm a := by rw [← hxa, Equiv.symm_apply_apply]
  clear hxa
  change (relSubPicPresheaf c ε (algEquivZeroCut c ε)).OverTotal T at a
  obtain ⟨t, ⟨ξ, hξ⟩⟩ := a
  obtain ⟨L, rfl⟩ := Quotient.exists_rep ξ
  change FibrewiseAlgEquivZero L at hξ
  haveI : LocallyOfFiniteType t := hx
  change ∃ (W : T.Opens) (φ : (W : Scheme.{u}) ⟶ ((UY ⊓ WY : Y.Opens) : Scheme.{u})), _ ∧
    uliftYoneda.{u + 1}.map φ ≫ _ = uliftYoneda.{u + 1}.map W.ι ≫ uliftYonedaEquiv.symm (pointElem R c ε t L hξ) ∧ _

  obtain ⟨W, hWiff⟩ := AlgebraicGeometry.RelPicard.exists_opens_range_subset_iff_forall_subsingleton_H1_fibre_of_twoAffineOpenCover R c 𝒱 t
    (Mγ R c ε (g + e) Dγ t L) (isInvertible_Mγ R c ε U hεU (g + e) Dγ hDγ t L)
  obtain ⟨D, D₀, hD, hDL, hD₀U⟩ :=
    AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_supportedIn_twistModule_iso_of_subsingleton_H1_of_zeroScheme R c ε U hεU g e (g + e) rfl
      Dγ hDγ hsect hZfibγ hH0one havoid t L hξ W (fun k _ s hs => (hWiff k s).1 hs)
  refine ⟨W, φ R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y Duniv hDunivU huniv DY hDY hDYU UY hUY WY hWY t L hξ W hWiff D D₀ hD hDL hD₀U,
    ?_, ?_, ?_⟩
  · intro L' hL' k _ s
    exact clause_i R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y Duniv hDunivU huniv DY hDY hDYU UY hUY WY hWY t L hξ W hWiff D D₀ hD hDL hD₀U
      L' (Quotient.exact hL') k s
  · exact clause_ii R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y Duniv hDunivU huniv DY hDY hDYU UY hUY WY hWY t L hξ W hWiff D D₀ hD hDL hD₀U
  · intro T' ψ φ' hlft hφ'
    haveI := hlft
    exact clause_iii R c ε U hεU g e Dγ hDγ hsect hZfibγ hH0one y Duniv hDunivU huniv DY hDY hDYU UY hUY WY hWY t L hξ W hWiff D D₀ hD hDL hD₀U ψ φ' hφ'

end S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_fibrewise_zeroScheme
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_openChart_openImmersion_relSubPicPresheaf_algEquivZeroCut_of_fibrewise_zeroScheme (solution)
