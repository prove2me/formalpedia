-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one_of_supportedIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a8ea3f64-f1f6-533b-92d7-5d876ff253ad

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso_of_range_subset
import Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_sectionIdeal_of_range_subset
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_I_eq_mul_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_supportedIn_ofPoint
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_invModule_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one_of_supportedIn
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π"
p2m_attr_erase "instance" "AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one_of_supportedIn.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one_of_supportedIn.AlgebraicGeometry.RelPicard NeronModelInfra"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper Scheme.Modules.pullback IsFinite Spec Scheme IsSeparated Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit RelEffCartierDiv Scheme.TwoAffineOpenCover Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.IdealSheafData.IsInvertible RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn RelEffCartierDiv.supportedIn_ofPoint RelEffCartierDiv.ofPoint Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd fibreAt sectionIdeal sectionTwist fibreModule nonempty_pullback_sectionTwist_iso_of_range_subset isInvertible_sectionIdeal_of_range_subset Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso"
namespace ChartHypotheses
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {R : Type u} [CommRing R]

theorem cover_ext {X : Scheme.{u}} {𝒱 𝒱' : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) : 𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

theorem nonempty_linearEquiv_of_iso {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of R))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    Nonempty ((𝒱.sectionsOf x M).H0 ≃ₗ[R] (𝒱.sectionsOf x M').H0) ∧
      Nonempty ((𝒱.sectionsOf x M).H1 ≃ₗ[R] (𝒱.sectionsOf x M').H1) := by
  obtain ⟨𝒱₂, h0, h1, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X) (Category.id_comp x)
      𝒱 M' M (e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm)
  obtain rfl : 𝒱₂ = 𝒱 := cover_ext h0 h1
  exact ⟨⟨e0⟩, ⟨e1⟩⟩

theorem eulerChar_congr {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    (Module.finrank k (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x M).H1 =
      (Module.finrank k (𝒱.sectionsOf x M').H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x M').H1 := by
  obtain ⟨⟨e0⟩, ⟨e1⟩⟩ := nonempty_linearEquiv_of_iso x 𝒱 e
  rw [e0.finrank_eq, e1.finrank_eq]

theorem finrank_H1_congr {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    Module.finrank k (𝒱.sectionsOf x M).H1 = Module.finrank k (𝒱.sectionsOf x M').H1 := by
  obtain ⟨-, ⟨e1⟩⟩ := nonempty_linearEquiv_of_iso x 𝒱 e
  exact e1.finrank_eq

def isoPullbackInvOfIso {X Y : Scheme.{u}} (φ : X ≅ Y) {M : X.Modules} {N : Y.Modules}
    (e : M ≅ (Scheme.Modules.pullback φ.hom).obj N) : N ≅ (Scheme.Modules.pullback φ.inv).obj M :=
  ((Scheme.Modules.pullbackId Y).app N).symm ≪≫
    (Scheme.Modules.pullbackCongr φ.inv_hom_id.symm).app N ≪≫
    ((Scheme.Modules.pullbackComp φ.inv φ.hom).app N).symm ≪≫
    (Scheme.Modules.pullback φ.inv).mapIso e.symm

section FibreIso

variable {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
  {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
  (hx : s ≫ t = x)

def fibreIso : pullback (pullback.snd c t) s ≅ pullback c x :=
  pullbackLeftPullbackSndIso c t s ≪≫ pullback.congrHom rfl hx

@[reassoc]
theorem fibreIso_hom_snd : (fibreIso c t s x hx).hom ≫ pullback.snd c x = fibreAt c t s := by
  subst hx
  simp [fibreIso, fibreAt, pullback.congrHom_hom]

@[reassoc]
theorem fibreIso_hom_fst :
    (fibreIso c t s x hx).hom ≫ pullback.fst c x = pullback.fst (pullback.snd c t) s ≫ pullback.fst c t := by
  subst hx
  simp [fibreIso, pullback.congrHom_hom]

theorem fibreIso_inv_fibreAt : (fibreIso c t s x hx).inv ≫ fibreAt c t s = pullback.snd c x := by
  rw [← fibreIso_hom_snd c t s x hx, Iso.inv_hom_id_assoc]

theorem fibreIso_hom_baseChangeSnd :
    (fibreIso c t s x hx).hom ≫ baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t)
      = pullback.fst (pullback.snd c t) s := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    unfold baseChangeSnd
    rw [pullback.lift_fst, ← Category.assoc, fibreIso_hom_fst, Category.assoc, Category.comp_id]
  · rw [Category.assoc]
    unfold baseChangeSnd
    rw [pullback.lift_snd, ← Category.assoc, fibreIso_hom_snd, pullback.condition]
    rfl

def fibreModuleIso (F : (pullback c t).Modules) :
    fibreModule c t s F ≅ (Scheme.Modules.pullback (fibreIso c t s x hx).hom).obj
      ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).obj F) :=
  (Scheme.Modules.pullbackCongr (fibreIso_hom_baseChangeSnd c t s x hx).symm).app F ≪≫
    ((Scheme.Modules.pullbackComp (fibreIso c t s x hx).hom
      (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).app F).symm

def fibreUnitIso :
    (𝟙_ (pullback (pullback.snd c t) s).Modules) ≅
      (Scheme.Modules.pullback (fibreIso c t s x hx).hom).obj (𝟙_ (pullback c x).Modules) :=
  (Scheme.Modules.pullbackTensorUnitObjIso (fibreIso c t s x hx).hom).symm

variable [IsSeparated c] (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hεU : Set.range ε.1 ⊆ (U : Set C))

include hεU in

theorem nonempty_chartModule_iso (r : ℕ) {e : ℕ} (D : RelEffCartierDiv c e t) (hDU : D.SupportedIn U) :
    Nonempty (fibreModule c t s (sectionTwist c ε t r ⊗ D.idealModule) ≅
      (Scheme.Modules.pullback (fibreIso c t s x hx).hom).obj
        (sectionTwist c ε x r ⊗ (D.pullbackAlong s hx).idealModule)) := by
  obtain ⟨eT⟩ := nonempty_pullback_sectionTwist_iso_of_range_subset R c ε U hεU (⟨s, hx⟩ : SchemeHomOver x t) r
  have hI : D.I.IsInvertible := D.isInvertible_I_of_supportedIn U hDU
  have hI' : (D.I.comap (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).IsInvertible :=
    (D.pullbackAlong s hx).isInvertible_I_of_supportedIn U (hDU.pullbackAlong s hx)
  let eI : (Scheme.Modules.pullback (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).obj D.idealModule ≅
      (D.pullbackAlong s hx).idealModule :=
    @asIso _ _ _ _ (D.I.pullbackModuleComparison (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t)))
      (Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison
        (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t)) hI hI')
  exact ⟨fibreModuleIso c t s x hx _ ≪≫ (Scheme.Modules.pullback (fibreIso c t s x hx).hom).mapIso
    (Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (eT ⊗ᵢ eI))⟩

include hεU in

theorem exists_cover_chart_of_cover (r : ℕ) {e : ℕ} (D : RelEffCartierDiv c e t) (hDU : D.SupportedIn U)
    (𝒱 : (pullback c x).TwoAffineOpenCover) :
    ∃ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (sectionTwist c ε t r ⊗ D.idealModule))).H0 ≃ₗ[k]
        (𝒱.sectionsOf (pullback.snd c x) (sectionTwist c ε x r ⊗ (D.pullbackAlong s hx).idealModule)).H0) ∧
      Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (sectionTwist c ε t r ⊗ D.idealModule))).H1 ≃ₗ[k]
        (𝒱.sectionsOf (pullback.snd c x) (sectionTwist c ε x r ⊗ (D.pullbackAlong s hx).idealModule)).H1) := by
  obtain ⟨eM⟩ := nonempty_chartModule_iso c t s x hx U ε hεU r D hDU
  obtain ⟨𝒲, -, -, h0, h1⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t s) (pullback.snd c x) (fibreIso c t s x hx) (fibreIso_hom_snd c t s x hx) 𝒱 _ _ eM
  exact ⟨𝒲, h0, h1⟩

include hεU in

theorem exists_cover_of_cover_chart (r : ℕ) {e : ℕ} (D : RelEffCartierDiv c e t) (hDU : D.SupportedIn U)
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) :
    ∃ 𝒱 : (pullback c x).TwoAffineOpenCover,
      Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (sectionTwist c ε t r ⊗ D.idealModule))).H0 ≃ₗ[k]
        (𝒱.sectionsOf (pullback.snd c x) (sectionTwist c ε x r ⊗ (D.pullbackAlong s hx).idealModule)).H0) ∧
      Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (sectionTwist c ε t r ⊗ D.idealModule))).H1 ≃ₗ[k]
        (𝒱.sectionsOf (pullback.snd c x) (sectionTwist c ε x r ⊗ (D.pullbackAlong s hx).idealModule)).H1) := by
  obtain ⟨eM⟩ := nonempty_chartModule_iso c t s x hx U ε hεU r D hDU
  obtain ⟨𝒱, -, -, ⟨h0⟩, ⟨h1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (pullback.snd c x) (fibreAt c t s) (fibreIso c t s x hx).symm (fibreIso_inv_fibreAt c t s x hx) 𝒲 _ _
    (isoPullbackInvOfIso (fibreIso c t s x hx) eM)
  exact ⟨𝒱, ⟨h0.symm⟩, ⟨h1.symm⟩⟩

omit [IsSeparated c] [SmoothOfRelativeDimension 1 (U.ι ≫ c)] in
include hx in

theorem exists_cover_of_cover_unit (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) :
    ∃ 𝒱 : (pullback c x).TwoAffineOpenCover,
      Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (𝟙_ _)).H0
          = Module.finrank k (𝒱.sectionsOf (pullback.snd c x) (𝟙_ _)).H0 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (𝟙_ _)).H1
          = Module.finrank k (𝒱.sectionsOf (pullback.snd c x) (𝟙_ _)).H1 := by
  obtain ⟨𝒱, -, -, ⟨e0⟩, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (pullback.snd c x) (fibreAt c t s) (fibreIso c t s x hx).symm (fibreIso_inv_fibreAt c t s x hx) 𝒲 _ _
    (isoPullbackInvOfIso (fibreIso c t s x hx) (fibreUnitIso c t s x hx))
  exact ⟨𝒱, e0.finrank_eq.symm, e1.finrank_eq.symm⟩

omit [IsSeparated c] [SmoothOfRelativeDimension 1 (U.ι ≫ c)] in
include hx in

theorem exists_cover_unit_of_cover (𝒱 : (pullback c x).TwoAffineOpenCover) :
    ∃ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (𝟙_ _)).H0
          = Module.finrank k (𝒱.sectionsOf (pullback.snd c x) (𝟙_ _)).H0 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (𝟙_ _)).H1
          = Module.finrank k (𝒱.sectionsOf (pullback.snd c x) (𝟙_ _)).H1 := by
  obtain ⟨𝒲, -, -, ⟨e0⟩, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t s) (pullback.snd c x) (fibreIso c t s x hx) (fibreIso_hom_snd c t s x hx) 𝒱 _ _
    (fibreUnitIso c t s x hx)
  exact ⟨𝒲, e0.finrank_eq, e1.finrank_eq⟩

end FibreIso

end AlgebraicGeometry.RelPicard.ChartHypotheses

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper Scheme.Modules.pullback IsFinite Spec Scheme IsSeparated Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit RelEffCartierDiv Scheme.TwoAffineOpenCover Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.IdealSheafData.IsInvertible RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn RelEffCartierDiv.supportedIn_ofPoint RelEffCartierDiv.ofPoint Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd fibreAt sectionIdeal sectionTwist fibreModule nonempty_pullback_sectionTwist_iso_of_range_subset isInvertible_sectionIdeal_of_range_subset Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso"
namespace ChartHypotheses
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

theorem exists_relEffCartierDiv_I_eq_sectionIdeal_pow
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hεU : Set.range ε.1 ⊆ (U : Set C))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (r : ℕ) (hr : 1 ≤ r) :
    ∃ E : RelEffCartierDiv c r t, E.I = (sectionIdeal c ε t) ^ r ∧ E.SupportedIn U := by

  have ha : (t ≫ ε.1) ≫ c = t := by rw [Category.assoc, ε.2, Category.comp_id]
  let E₁ : RelEffCartierDiv c 1 t := RelEffCartierDiv.ofPoint c (t ≫ ε.1) ha
  have hE₁I : E₁.I = sectionIdeal c ε t := rfl
  have hE₁U : E₁.SupportedIn U :=
    RelEffCartierDiv.supportedIn_ofPoint (t ≫ ε.1) ha U (fun z => hεU ⟨t.base z, rfl⟩)

  induction r, hr using Nat.le_induction with
  | base => exact ⟨E₁, by rw [hE₁I, pow_one], hE₁U⟩
  | succ n hn ih =>
    obtain ⟨E, hEI, hEU⟩ := ih
    obtain ⟨F, hFI, hFU⟩ := RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn U E E₁ hEU hE₁U
    exact ⟨F, by rw [hFI, hEI, hE₁I, pow_succ], hFU⟩

end AlgebraicGeometry.RelPicard.ChartHypotheses

end

open CategoryTheory CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_RelPicard_eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one_of_supportedIn.AlgebraicGeometry _root_.AlgebraicGeometry.RelPicard _root_.P2MW.S_AlgebraicGeometry_RelPicard_eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one_of_supportedIn.AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.RelPicard.ChartHypotheses in

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hεU : Set.range ε.1 ⊆ (U : Set C))
    (g e r : ℕ) (hr : g + e = r)
    (D : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDU : D.SupportedIn U)
    (k : Type u) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))

    (hH0 : ∀ 𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover,
      Module.finrank k ↥(𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H0 = 1)
    (hg : ∀ 𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover,
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H1 = g)
    (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover) :
    (Module.finrank k ↥(𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ D.idealModule))).H0 : ℤ) -
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ D.idealModule))).H1 = 1 := by
  have hx : x ≫ 𝟙 (Spec (CommRingCat.of R)) = x := Category.comp_id x

  obtain ⟨𝒱, ⟨e0⟩, ⟨e1⟩⟩ := exists_cover_of_cover_chart c (𝟙 _) x x hx U ε hεU r D hDU 𝒲
  rw [e0.finrank_eq, e1.finrank_eq]

  have hIsec : (sectionIdeal c ε x).IsInvertible := isInvertible_sectionIdeal_of_range_subset c ε U hεU x
  have hIr : ((sectionIdeal c ε x) ^ r).IsInvertible := hIsec.pow r
  have hP : Scheme.Modules.IsInvertible (sectionTwist c ε x r) := hIr.isInvertible_invModule
  have hEI : (D.pullbackAlong x hx).I.IsInvertible :=
    (D.pullbackAlong x hx).isInvertible_I_of_supportedIn U (hDU.pullbackAlong x hx)
  have hPE : Scheme.Modules.IsInvertible (sectionTwist c ε x r ⊗ (D.pullbackAlong x hx).idealModule) :=
    hP.tensor hEI.isInvertible_module

  have h2b := Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq
    (pullback.snd c x) hEI (D.pullbackAlong x hx).isFinite (D.pullbackAlong x hx).finrank_eq
    (sectionTwist c ε x r ⊗ (D.pullbackAlong x hx).idealModule) hPE 𝒱

  have h2c := eulerChar_congr (pullback.snd c x) 𝒱
    (α_ (sectionTwist c ε x r) (D.pullbackAlong x hx).idealModule (D.pullbackAlong x hx).I.invModule ≪≫
      whiskerLeftIso (sectionTwist c ε x r)
        (β_ _ _ ≪≫ (Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso hEI).some) ≪≫
      ρ_ (sectionTwist c ε x r))

  have h2d : (Module.finrank k ↥(𝒱.sectionsOf (pullback.snd c x) (𝟙_ _ ⊗ ((sectionIdeal c ε x) ^ r).invModule)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd c x) (𝟙_ _ ⊗ ((sectionIdeal c ε x) ^ r).invModule)).H1
      = (Module.finrank k ↥(𝒱.sectionsOf (pullback.snd c x) (𝟙_ _)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd c x) (𝟙_ _)).H1 + r := by

    obtain ⟨E', hE'I, -⟩ := exists_relEffCartierDiv_I_eq_sectionIdeal_pow c U ε hεU x (r + 1) (by omega)
    have hZ' : IsFinite (((sectionIdeal c ε x) ^ (r + 1)).subschemeι ≫ pullback.snd c x) := by rw [← hE'I]; exact E'.isFinite
    have hdeg' : ∀ t, (((sectionIdeal c ε x) ^ (r + 1)).subschemeι ≫ pullback.snd c x).finrank t = r + 1 := by
      rw [← hE'I]; exact E'.finrank_eq
    obtain ⟨E₁, hE₁I, -⟩ := exists_relEffCartierDiv_I_eq_sectionIdeal_pow c U ε hεU x 1 le_rfl
    rw [pow_one] at hE₁I
    have hZ₁ : IsFinite ((sectionIdeal c ε x).subschemeι ≫ pullback.snd c x) := by rw [← hE₁I]; exact E₁.isFinite
    have hdeg₁ : ∀ t, ((sectionIdeal c ε x).subschemeι ≫ pullback.snd c x).finrank t = 1 := by
      rw [← hE₁I]; exact E₁.finrank_eq

    have hA := Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq
      (pullback.snd c x) (hIsec.pow (r + 1)) hZ' hdeg' (𝟙_ _) (Scheme.Modules.isInvertible_unit _) 𝒱

    have hB := Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq
      (pullback.snd c x) hIsec hZ₁ hdeg₁ (𝟙_ _ ⊗ ((sectionIdeal c ε x) ^ r).invModule)
      ((Scheme.Modules.isInvertible_unit _).tensor hIr.isInvertible_invModule) 𝒱

    have hpow : ((sectionIdeal c ε x) ^ r * sectionIdeal c ε x).invModule = ((sectionIdeal c ε x) ^ (r + 1)).invModule := by
      rw [← pow_succ]
    have hC := eulerChar_congr (pullback.snd c x) 𝒱
      (α_ (𝟙_ _) ((sectionIdeal c ε x) ^ r).invModule (sectionIdeal c ε x).invModule ≪≫
        whiskerLeftIso (𝟙_ _)
          ((Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor hIr hIsec).some.symm ≪≫ eqToIso hpow))
    omega
  have h2d' := eulerChar_congr (M := 𝟙_ _ ⊗ ((sectionIdeal c ε x) ^ r).invModule)
    (M' := sectionTwist c ε x r) (pullback.snd c x) 𝒱 (λ_ (sectionTwist c ε x r))

  obtain ⟨𝒲', hW0, hW1⟩ := exists_cover_unit_of_cover c (𝟙 _) x x hx 𝒱
  have hG0 : Module.finrank k (𝒱.sectionsOf (pullback.snd c x) (𝟙_ _)).H0 = 1 := by rw [← hW0]; exact hH0 𝒲'
  have hG1 : Module.finrank k (𝒱.sectionsOf (pullback.snd c x) (𝟙_ _)).H1 = g := by rw [← hW1]; exact hg 𝒲'

  omega

end S_AlgebraicGeometry_RelPicard_eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one_of_supportedIn
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one_of_supportedIn (solution)
