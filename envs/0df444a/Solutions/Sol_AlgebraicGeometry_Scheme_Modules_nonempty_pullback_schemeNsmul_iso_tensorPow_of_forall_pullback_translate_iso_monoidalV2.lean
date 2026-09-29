-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.nonempty_pullback_schemeNsmul_iso_tensorPow_of_forall_pullback_translate_iso_monoidalV2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/8a8a5266-36ca-5fbf-a48a-01f6ecae6432

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Theorems.Thm_AlgebraicGeometry_Polarisation_inPicZero_iff_nonempty_mumfordBundle_iso_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_schemeNsmul_iso_tensorPow_of_forall_pullback_translate_iso_monoidalV2
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace PicZeroNsmul

variable {X : Scheme.{0}}

def isoOfTensorInv {Xm P Q : X.Modules} (e : Xm ⊗ P ≅ 𝟙_ X.Modules) (e' : P ⊗ Q ≅ 𝟙_ X.Modules) : Xm ≅ Q :=
  calc Xm ≅ Xm ⊗ 𝟙_ X.Modules := (ρ_ _).symm
    _ ≅ Xm ⊗ (P ⊗ Q) := whiskerLeftIso _ e'.symm
    _ ≅ (Xm ⊗ P) ⊗ Q := (α_ _ _ _).symm
    _ ≅ 𝟙_ X.Modules ⊗ Q := whiskerRightIso e _
    _ ≅ Q := λ_ _

def dualPairIso {A' B' Am Bm : X.Modules} (eA : Am ⊗ A' ≅ 𝟙_ X.Modules) (eB : Bm ⊗ B' ≅ 𝟙_ X.Modules) :
    (A' ⊗ B') ⊗ (Am ⊗ Bm) ≅ 𝟙_ X.Modules :=
  calc (A' ⊗ B') ⊗ (Am ⊗ Bm) ≅ (Am ⊗ Bm) ⊗ (A' ⊗ B') := β_ _ _
    _ ≅ Am ⊗ (Bm ⊗ (A' ⊗ B')) := α_ _ _ _
    _ ≅ Am ⊗ ((Bm ⊗ A') ⊗ B') := whiskerLeftIso _ (α_ _ _ _).symm
    _ ≅ Am ⊗ ((A' ⊗ Bm) ⊗ B') := whiskerLeftIso _ (whiskerRightIso (β_ _ _) _)
    _ ≅ Am ⊗ (A' ⊗ (Bm ⊗ B')) := whiskerLeftIso _ (α_ _ _ _)
    _ ≅ Am ⊗ (A' ⊗ 𝟙_ X.Modules) := whiskerLeftIso _ (whiskerLeftIso _ eB)
    _ ≅ Am ⊗ A' := whiskerLeftIso _ (ρ_ _)
    _ ≅ 𝟙_ X.Modules := eA

end PicZeroNsmul

open PicZeroNsmul in
theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (N : A.Modules) (hN : Scheme.Modules.IsInvertible N)
    (hN0 : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      Nonempty ((Scheme.Modules.pullback (L.translate x)).obj N ≅ N))
    (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback (L.schemeNsmul n)).obj N ≅ N.tensorPow n) := by
  classical
  let Φ : ℕ → (A.Modules ⥤ A.Modules) := fun m => Scheme.Modules.pullback (L.schemeNsmul m)
  let D := Scheme.Modules.dual N
  obtain ⟨hDinv, ⟨eN⟩⟩ := hN.dual_monoidalV2

  obtain ⟨eΛ⟩ := (AlgebraicGeometry.Polarisation.inPicZero_iff_nonempty_mumfordBundle_iso_unit k f L hc hA N hN).1 ⟨hN, hN0⟩

  have hsec : ∀ m : ℕ, Nonempty ((Φ (m + 1)).obj N ⊗ ((Φ m).obj D ⊗ D) ≅ 𝟙_ A.Modules) := by
    intro m
    let s : A ⟶ pullback f f := pullback.lift (L.schemeNsmul m) (𝟙 A) (by rw [L.schemeNsmul_over, Category.id_comp])
    have hs1 : s ≫ pullback.fst f f = L.schemeNsmul m := pullback.lift_fst _ _ _
    have hs2 : s ≫ pullback.snd f f = 𝟙 A := pullback.lift_snd _ _ _
    have hsf : s ≫ (pullback.fst f f ≫ f) = f := by rw [← Category.assoc, hs1, L.schemeNsmul_over]
    have hs3 : s ≫ addMor f L = L.schemeNsmul (m + 1) := by
      have hnat := L.mul_natural (pullback.fst f f ≫ f) f s hsf ⟨pullback.fst f f, rfl⟩
        ⟨pullback.snd f f, pullback.condition.symm⟩
      have e1 : schemeHomOverComp s hsf ⟨pullback.fst f f, rfl⟩ = L.nsmul f m RelativeGroupLaw.idPoint :=
        Subtype.ext hs1
      have e2 : schemeHomOverComp s hsf ⟨pullback.snd f f, pullback.condition.symm⟩ = RelativeGroupLaw.idPoint :=
        Subtype.ext hs2
      rw [e1, e2, ← RelativeGroupLaw.nsmul_succ] at hnat
      exact congrArg Subtype.val hnat

    let Ps := Scheme.Modules.pullback s
    have e0 : Ps.obj (mumfordBundle f L N) ≅ 𝟙_ A.Modules := Ps.mapIso eΛ ≪≫ Scheme.Modules.pullbackTensorUnitObjIso s
    refine ⟨?_ ≪≫ e0⟩
    symm
    calc Ps.obj (mumfordBundle f L N)
        ≅ Ps.obj ((Scheme.Modules.pullback (addMor f L)).obj N) ⊗
            Ps.obj ((Scheme.Modules.pullback (pullback.fst f f)).obj D ⊗ (Scheme.Modules.pullback (pullback.snd f f)).obj D) :=
          Scheme.Modules.pullbackTensorObjIso s _ _
      _ ≅ Ps.obj ((Scheme.Modules.pullback (addMor f L)).obj N) ⊗
            (Ps.obj ((Scheme.Modules.pullback (pullback.fst f f)).obj D) ⊗ Ps.obj ((Scheme.Modules.pullback (pullback.snd f f)).obj D)) :=
          whiskerLeftIso _ (Scheme.Modules.pullbackTensorObjIso s _ _)
      _ ≅ (Scheme.Modules.pullback (s ≫ addMor f L)).obj N ⊗
            ((Scheme.Modules.pullback (s ≫ pullback.fst f f)).obj D ⊗ (Scheme.Modules.pullback (s ≫ pullback.snd f f)).obj D) :=
          ((Scheme.Modules.pullbackComp s (addMor f L)).app N) ⊗ᵢ
            (((Scheme.Modules.pullbackComp s (pullback.fst f f)).app D) ⊗ᵢ ((Scheme.Modules.pullbackComp s (pullback.snd f f)).app D))
      _ ≅ (Φ (m + 1)).obj N ⊗ ((Φ m).obj D ⊗ (Scheme.Modules.pullback (𝟙 A)).obj D) :=
          ((Scheme.Modules.pullbackCongr hs3).app N) ⊗ᵢ
            (((Scheme.Modules.pullbackCongr hs1).app D) ⊗ᵢ ((Scheme.Modules.pullbackCongr hs2).app D))
      _ ≅ (Φ (m + 1)).obj N ⊗ ((Φ m).obj D ⊗ D) :=
          whiskerLeftIso _ (whiskerLeftIso _ ((Scheme.Modules.pullbackId A).app D))

  have hrec : ∀ m : ℕ, Nonempty ((Φ (m + 1)).obj N ≅ (Φ m).obj N ⊗ N) := by
    intro m
    obtain ⟨e⟩ := hsec m
    obtain ⟨eDm⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback_dual_monoidalV2 (L.schemeNsmul m) hN

    obtain ⟨-, ⟨eNm⟩⟩ := (hN.pullback (L.schemeNsmul m)).dual_monoidalV2
    have eNm' : (Φ m).obj N ⊗ (Φ m).obj D ≅ 𝟙_ A.Modules := whiskerLeftIso _ eDm ≪≫ eNm
    exact ⟨isoOfTensorInv e (dualPairIso eNm' eN)⟩

  have h1 : L.schemeNsmul 1 = 𝟙 A := congrArg Subtype.val (L.nsmul_one_apply f RelativeGroupLaw.idPoint)
  have hzero : Nonempty ((Φ 0).obj N ≅ 𝟙_ A.Modules) := by
    obtain ⟨e⟩ := hrec 0

    have e1 : N ≅ (Φ 0).obj N ⊗ N :=
      ((Scheme.Modules.pullbackId A).app N).symm ≪≫ ((Scheme.Modules.pullbackCongr h1).app N).symm ≪≫ e
    refine ⟨?_⟩
    calc (Φ 0).obj N ≅ (Φ 0).obj N ⊗ 𝟙_ A.Modules := (ρ_ _).symm
      _ ≅ (Φ 0).obj N ⊗ (N ⊗ D) := whiskerLeftIso _ eN.symm
      _ ≅ ((Φ 0).obj N ⊗ N) ⊗ D := (α_ _ _ _).symm
      _ ≅ N ⊗ D := whiskerRightIso e1.symm _
      _ ≅ 𝟙_ A.Modules := eN

  induction n with
  | zero => obtain ⟨e⟩ := hzero; exact ⟨e⟩
  | succ m ih =>
    obtain ⟨e⟩ := ih
    obtain ⟨e'⟩ := hrec m
    exact ⟨e' ≪≫ whiskerRightIso e _⟩

end
end S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_schemeNsmul_iso_tensorPow_of_forall_pullback_translate_iso_monoidalV2
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_schemeNsmul_iso_tensorPow_of_forall_pullback_translate_iso_monoidalV2 (solution)
