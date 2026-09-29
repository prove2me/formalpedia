-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_tensorPow_foldr_module_eq_sub_and_invModule_eq_add_of_finrank_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/041db10c-f1cd-5340-ab67-23361432c7ca

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_pullback_pow_module_tensor_eq_sub_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_pullback_pow_invModule_tensor_eq_add_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensorPow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_tensorPow_foldr_module_eq_sub_and_invModule_eq_add_of_finrank_eq_one
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module"
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

universe u

namespace TwPtsKit

variable {k : Type u} [Field k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k)) (𝒲 : Y.TwoAffineOpenCover)

noncomputable def chi (M : Y.Modules) : ℤ :=
  (Module.finrank k (𝒲.sectionsOf y M).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf y M).H1

theorem chi_congr {M M' : Y.Modules} (e : M ≅ M') : chi y 𝒲 M = chi y 𝒲 M' := by
  have hφ : (Iso.refl Y).hom ≫ y = y := Category.id_comp y
  let e' : M ≅ (Scheme.Modules.pullback (Iso.refl Y).hom).obj M' := e ≪≫ ((Scheme.Modules.pullbackId Y).app M').symm
  obtain ⟨𝒱, h0, h1, ⟨f0⟩, ⟨f1⟩⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso y y (Iso.refl Y) hφ 𝒲 M' M e'
  have hVW : 𝒱 = 𝒲 := by
    cases 𝒱; cases 𝒲
    simp only [Iso.refl_hom] at h0 h1
    congr
  subst hVW
  unfold chi
  rw [f0.finrank_eq, f1.finrank_eq]

noncomputable def tensorFoldrIso {ι : Type*} (A : ι → Y.Modules) (N : Y.Modules) :
    (l : List ι) → N ⊗ l.foldr (fun i M => A i ⊗ M) (𝟙_ Y.Modules) ≅ l.foldr (fun i M => A i ⊗ M) N
  | [] => ρ_ N
  | (a :: l) => (α_ N (A a) _).symm ≪≫ (whiskerRightIso (β_ N (A a)) _) ≪≫ α_ (A a) N _ ≪≫
      whiskerLeftIso (A a) (tensorFoldrIso A N l)

theorem isInvertible_unit {L : Y.Modules} (hL : Scheme.Modules.IsInvertible L) : Scheme.Modules.IsInvertible (𝟙_ Y.Modules) :=
  hL.tensorPow 0

theorem isInvertible_foldr {ι : Type*} (A : ι → Y.Modules) (hA : ∀ i, Scheme.Modules.IsInvertible (A i))
    {N : Y.Modules} (hN : Scheme.Modules.IsInvertible N) :
    ∀ l : List ι, Scheme.Modules.IsInvertible (l.foldr (fun i M => A i ⊗ M) N)
  | [] => hN
  | (a :: l) => (hA a).tensor (isInvertible_foldr A hA hN l)

theorem chi_module_tensor [IsProper y] (𝔭 : Y.IdealSheafData) (h𝔭 : 𝔭.IsInvertible) (hfin : IsFinite (𝔭.subschemeι ≫ y))
    (hdeg : ∀ t : Spec (CommRingCat.of k), (𝔭.subschemeι ≫ y).finrank t = 1)
    (M : Y.Modules) (hM : Scheme.Modules.IsInvertible M) :
    chi y 𝒲 (𝔭.module ⊗ M) = chi y 𝒲 M - 1 ∧ chi y 𝒲 (𝔭.invModule ⊗ M) = chi y 𝒲 M + 1 := by
  have hIY : (𝔭.comap (𝟙 Y)).IsInvertible := by rw [Scheme.IdealSheafData.comap_id]; exact h𝔭
  have hZ : IsFinite ((𝔭.comap (𝟙 Y)).subschemeι ≫ y) := by rw [Scheme.IdealSheafData.comap_id]; exact hfin
  have hdeg' : ∀ t : Spec (CommRingCat.of k), ((𝔭.comap (𝟙 Y)).subschemeι ≫ y).finrank t = 1 := by
    rw [Scheme.IdealSheafData.comap_id]; exact hdeg
  have h1 := AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_pullback_pow_module_tensor_eq_sub_mul
    (𝟙 Y) y h𝔭 hIY hZ hdeg' M hM 1 𝒲
  have h2 := AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_pullback_pow_invModule_tensor_eq_add_mul
    (𝟙 Y) y h𝔭 hIY hZ hdeg' M hM 1 𝒲
  have hp1 : 𝔭 ^ 1 = 𝔭 := pow_one 𝔭
  rw [hp1] at h1 h2
  simp only [Nat.cast_one, one_mul, mul_one] at h1 h2
  have eM : (Scheme.Modules.pullback (𝟙 Y)).obj M ≅ M := (Scheme.Modules.pullbackId Y).app M
  have e1 : (Scheme.Modules.pullback (𝟙 Y)).obj (𝔭.module ⊗ M) ≅ 𝔭.module ⊗ M := (Scheme.Modules.pullbackId Y).app _
  have e2 : (Scheme.Modules.pullback (𝟙 Y)).obj (𝔭.invModule ⊗ M) ≅ 𝔭.invModule ⊗ M := (Scheme.Modules.pullbackId Y).app _
  have c0 := chi_congr y 𝒲 eM
  have c1 := chi_congr y 𝒲 e1
  have c2 := chi_congr y 𝒲 e2
  unfold chi at c0 c1 c2 ⊢
  constructor <;> linarith

theorem chi_foldr [IsProper y] {n : ℕ} (𝔭 : Fin n → Y.IdealSheafData) (h𝔭 : ∀ i, (𝔭 i).IsInvertible)
    (hfin : ∀ i, IsFinite ((𝔭 i).subschemeι ≫ y))
    (hdeg : ∀ (i) (t : Spec (CommRingCat.of k)), ((𝔭 i).subschemeι ≫ y).finrank t = 1)
    {N : Y.Modules} (hN : Scheme.Modules.IsInvertible N) :
    ∀ l : List (Fin n),
      chi y 𝒲 (l.foldr (fun i M => (𝔭 i).module ⊗ M) N) = chi y 𝒲 N - l.length ∧
      chi y 𝒲 (l.foldr (fun i M => (𝔭 i).invModule ⊗ M) N) = chi y 𝒲 N + l.length
  | [] => by simp
  | (a :: l) => by
    obtain ⟨ih1, ih2⟩ := chi_foldr 𝔭 h𝔭 hfin hdeg hN l
    have hinv1 := isInvertible_foldr (fun i => (𝔭 i).module) (fun i => (h𝔭 i).isInvertible_module) hN l
    have hinv2 := isInvertible_foldr (fun i => (𝔭 i).invModule) (fun i => (h𝔭 i).isInvertible_invModule) hN l
    obtain ⟨s1, -⟩ := chi_module_tensor y 𝒲 (𝔭 a) (h𝔭 a) (hfin a) (hdeg a) _ hinv1
    obtain ⟨-, s2⟩ := chi_module_tensor y 𝒲 (𝔭 a) (h𝔭 a) (hfin a) (hdeg a) _ hinv2
    simp only [List.foldr_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    constructor
    · rw [s1, ih1]; ring
    · rw [s2, ih2]; ring

end TwPtsKit

theorem solution
    {k : Type u} [Field k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k)) [IsProper y] (𝒲 : Y.TwoAffineOpenCover)
    {n : ℕ} (𝔭 : Fin n → Y.IdealSheafData) (h𝔭 : ∀ i, (𝔭 i).IsInvertible)
    (hfin : ∀ i, IsFinite ((𝔭 i).subschemeι ≫ y))
    (hdeg : ∀ (i) (t : Spec (CommRingCat.of k)), ((𝔭 i).subschemeι ≫ y).finrank t = 1)
    (L : Y.Modules) (hL : Scheme.Modules.IsInvertible L) (d : ℕ) :
    ((Module.finrank k (𝒲.sectionsOf y (L ⊗ (((List.finRange n).foldr (fun i M => (𝔭 i).module ⊗ M) (𝟙_ Y.Modules)).tensorPow d))).H0 : ℤ)
        - Module.finrank k (𝒲.sectionsOf y (L ⊗ (((List.finRange n).foldr (fun i M => (𝔭 i).module ⊗ M) (𝟙_ Y.Modules)).tensorPow d))).H1
      = (Module.finrank k (𝒲.sectionsOf y L).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf y L).H1 - d * n) ∧
    ((Module.finrank k (𝒲.sectionsOf y (L ⊗ (((List.finRange n).foldr (fun i M => (𝔭 i).invModule ⊗ M) (𝟙_ Y.Modules)).tensorPow d))).H0 : ℤ)
        - Module.finrank k (𝒲.sectionsOf y (L ⊗ (((List.finRange n).foldr (fun i M => (𝔭 i).invModule ⊗ M) (𝟙_ Y.Modules)).tensorPow d))).H1
      = (Module.finrank k (𝒲.sectionsOf y L).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf y L).H1 + d * n) := by
  classical

  set Fm := (List.finRange n).foldr (fun i M => (𝔭 i).module ⊗ M) (𝟙_ Y.Modules) with hFm
  set Fi := (List.finRange n).foldr (fun i M => (𝔭 i).invModule ⊗ M) (𝟙_ Y.Modules) with hFi
  have hU : Scheme.Modules.IsInvertible (𝟙_ Y.Modules) := TwPtsKit.isInvertible_unit hL
  have hFm_inv : Scheme.Modules.IsInvertible Fm :=
    TwPtsKit.isInvertible_foldr (fun i => (𝔭 i).module) (fun i => (h𝔭 i).isInvertible_module) hU _
  have hFi_inv : Scheme.Modules.IsInvertible Fi :=
    TwPtsKit.isInvertible_foldr (fun i => (𝔭 i).invModule) (fun i => (h𝔭 i).isInvertible_invModule) hU _

  have stepm : ∀ N, Scheme.Modules.IsInvertible N → TwPtsKit.chi y 𝒲 (N ⊗ Fm) = TwPtsKit.chi y 𝒲 N - n := by
    intro N hN
    rw [TwPtsKit.chi_congr y 𝒲 (TwPtsKit.tensorFoldrIso (fun i => (𝔭 i).module) N (List.finRange n)),
      (TwPtsKit.chi_foldr y 𝒲 𝔭 h𝔭 hfin hdeg hN (List.finRange n)).1, List.length_finRange]
  have stepi : ∀ N, Scheme.Modules.IsInvertible N → TwPtsKit.chi y 𝒲 (N ⊗ Fi) = TwPtsKit.chi y 𝒲 N + n := by
    intro N hN
    rw [TwPtsKit.chi_congr y 𝒲 (TwPtsKit.tensorFoldrIso (fun i => (𝔭 i).invModule) N (List.finRange n)),
      (TwPtsKit.chi_foldr y 𝒲 𝔭 h𝔭 hfin hdeg hN (List.finRange n)).2, List.length_finRange]

  have main : ∀ d : ℕ, TwPtsKit.chi y 𝒲 (L ⊗ Fm.tensorPow d) = TwPtsKit.chi y 𝒲 L - d * n ∧
      TwPtsKit.chi y 𝒲 (L ⊗ Fi.tensorPow d) = TwPtsKit.chi y 𝒲 L + d * n := by
    intro d
    induction d with
    | zero =>
      simp only [Scheme.Modules.tensorPow_zero, Nat.cast_zero, zero_mul, sub_zero, add_zero]
      exact ⟨TwPtsKit.chi_congr y 𝒲 (ρ_ L), TwPtsKit.chi_congr y 𝒲 (ρ_ L)⟩
    | succ d ih =>
      obtain ⟨ihm, ihi⟩ := ih
      have hNm : Scheme.Modules.IsInvertible (L ⊗ Fm.tensorPow d) := hL.tensor (hFm_inv.tensorPow d)
      have hNi : Scheme.Modules.IsInvertible (L ⊗ Fi.tensorPow d) := hL.tensor (hFi_inv.tensorPow d)
      simp only [Scheme.Modules.tensorPow_succ, Nat.cast_add, Nat.cast_one]
      constructor
      · rw [TwPtsKit.chi_congr y 𝒲 (α_ L (Fm.tensorPow d) Fm).symm, stepm _ hNm, ihm]; ring
      · rw [TwPtsKit.chi_congr y 𝒲 (α_ L (Fi.tensorPow d) Fi).symm, stepi _ hNi, ihi]; ring
  exact main d

end S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_tensorPow_foldr_module_eq_sub_and_invModule_eq_add_of_finrank_eq_one
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_tensorPow_foldr_module_eq_sub_and_invModule_eq_add_of_finrank_eq_one (solution)
