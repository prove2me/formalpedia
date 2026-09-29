-- Prove2me | solution 1 for AlgebraicGeometry.exists_hom_comp_eq_forall_pullback_fst_comp_eq_of_forall_truncation_of_isFinite_proj_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/66b17806-f7d4-5100-b006-04f12380a42f

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_exists_isFinite_of_forall_isFinite_isPullback_of_isProper_of_isAdicComplete
import Theorems.Thm_AlgebraicGeometry_isIso_of_isProper_of_forall_isIso_pullback_snd_truncation_of_isAdicComplete
import Theorems.Thm_AlgebraicGeometry_eq_of_forall_pullback_fst_truncation_comp_eq_of_isProper_of_isSeparated_of_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_hom_comp_eq_forall_pullback_fst_comp_eq_of_forall_truncation_of_isFinite_proj_of_isAdicComplete
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.cechPushforward_obj AlgebraicGeometry.OModulePresheaf.Hom.coe_cechPushforward_app AlgebraicGeometry.OModulePresheaf.AffHom.coe_cechPushforward_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace P2mWs41FHA

theorem isPullback_of_sections {C : Type*} [Category C] {A₁ A₂ B₁ B₂ : C}
    (a : A₁ ⟶ A₂) (b : B₁ ⟶ B₂) (s₁ : A₁ ⟶ B₁) (s₂ : A₂ ⟶ B₂) (p₁ : B₁ ⟶ A₁) (p₂ : B₂ ⟶ A₂)
    (hs₁ : s₁ ≫ p₁ = 𝟙 _) (hs₂ : s₂ ≫ p₂ = 𝟙 _) (hsq : a ≫ s₂ = s₁ ≫ b)
    (H : IsPullback b p₁ p₂ a) : IsPullback a s₁ s₂ b := by
  have outer : IsPullback (s₁ ≫ p₁) a a (s₂ ≫ p₂) := by
    rw [hs₁, hs₂]; exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact (IsPullback.of_right outer hsq.symm H.flip).flip

lemma isPullback_of_right_lift {X X₁ Y B B' : Scheme.{u}} {p : X ⟶ X₁} {g : X ⟶ Y} {f : X₁ ⟶ B} {ι : Y ⟶ B}
    (sq : IsPullback p g f ι) (κ : B' ⟶ B) (ι' : Y ⟶ B') (hι : ι' ≫ κ = ι)
    (w : p ≫ f = (g ≫ ι') ≫ κ) :
    IsPullback (pullback.lift p (g ≫ ι') w) g (pullback.snd f κ) ι' := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f κ) (v₁₃ := f) (h₂₂ := κ) ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback f κ)
  rw [pullback.lift_fst, hι]
  exact sq

end P2mWs41FHA

open P2mWs41FHA in
theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]

    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (rX : ℕ) (GX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (rX + 1)) R)) [IsFinite GX] (hGX : GX ≫ ProjSpace.π R rX = f)
    (Y : Scheme.{u}) (g : Y ⟶ Spec (CommRingCat.of R))
    (rY : ℕ) (GY : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (rY + 1)) R)) [IsFinite GY] (hGY : GY ≫ ProjSpace.π R rY = g)

    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    (tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1 + 1))))
    (htR : ∀ n : ℕ, tR n ≫ sR (n + 1) = sR n)

    (xn : ∀ n : ℕ, Limits.pullback f (sR n) ⟶ Limits.pullback f (sR (n + 1)))
    (hxn₁ : ∀ n : ℕ, xn n ≫ Limits.pullback.fst f (sR (n + 1)) = Limits.pullback.fst f (sR n))
    (hxn₂ : ∀ n : ℕ, xn n ≫ Limits.pullback.snd f (sR (n + 1)) = Limits.pullback.snd f (sR n) ≫ tR n)
    (yn : ∀ n : ℕ, Limits.pullback g (sR n) ⟶ Limits.pullback g (sR (n + 1)))
    (hyn₁ : ∀ n : ℕ, yn n ≫ Limits.pullback.fst g (sR (n + 1)) = Limits.pullback.fst g (sR n))
    (hyn₂ : ∀ n : ℕ, yn n ≫ Limits.pullback.snd g (sR (n + 1)) = Limits.pullback.snd g (sR n) ≫ tR n)

    (φ : ∀ n : ℕ, Limits.pullback f (sR n) ⟶ Limits.pullback g (sR n))
    (hφ : ∀ n : ℕ, φ n ≫ Limits.pullback.snd g (sR n) = Limits.pullback.snd f (sR n))
    (hφc : ∀ n : ℕ, xn n ≫ φ (n + 1) = φ n ≫ yn n) :
    ∃ F : X ⟶ Y, F ≫ g = f ∧
      (∀ n : ℕ, Limits.pullback.fst f (sR n) ≫ F = φ n ≫ Limits.pullback.fst g (sR n)) ∧
      ∀ F' : X ⟶ Y, F' ≫ g = f →
        (∀ n : ℕ, Limits.pullback.fst f (sR n) ≫ F' = φ n ≫ Limits.pullback.fst g (sR n)) → F' = F := by
  classical

  haveI : IsProper f := by rw [← hGX]; infer_instance
  haveI : IsProper g := by rw [← hGY]; infer_instance

  let w : pullback f g ⟶ Spec (CommRingCat.of R) := (pullback.fst f g) ≫ f
  haveI : IsProper w := inferInstance
  have wcond : ∀ n : ℕ, pullback.fst w (sR n) ≫ w = (pullback.snd w (sR n) ≫ tR n) ≫ sR (n + 1) := by
    intro n; rw [Category.assoc, htR]; exact pullback.condition
  let wn : ∀ n : ℕ, pullback w (sR n) ⟶ pullback w (sR (n + 1)) :=
    fun n => pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ tR n) (wcond n)
  have hwn₁ : ∀ n, wn n ≫ pullback.fst _ _ = pullback.fst _ _ := fun n => pullback.lift_fst _ _ _
  have hwn₂ : ∀ n, wn n ≫ pullback.snd _ _ = pullback.snd _ _ ≫ tR n := fun n => pullback.lift_snd _ _ _

  have prcond : ∀ n : ℕ, (pullback.fst w (sR n) ≫ (pullback.fst f g)) ≫ f = pullback.snd w (sR n) ≫ sR n := by
    intro n; rw [Category.assoc]; exact pullback.condition
  let prX : ∀ n : ℕ, pullback w (sR n) ⟶ pullback f (sR n) :=
    fun n => pullback.lift (pullback.fst _ _ ≫ (pullback.fst f g)) (pullback.snd _ _) (prcond n)
  have hprX₁ : ∀ n, prX n ≫ pullback.fst f (sR n) = pullback.fst w (sR n) ≫ (pullback.fst f g) := fun n => pullback.lift_fst _ _ _
  have hprX₂ : ∀ n, prX n ≫ pullback.snd f (sR n) = pullback.snd w (sR n) := fun n => pullback.lift_snd _ _ _
  have sqX : ∀ n, IsPullback (prX n) (pullback.fst w (sR n)) (pullback.fst f (sR n)) (pullback.fst f g) := by
    intro n
    refine IsPullback.of_right (h₁₂ := pullback.snd f (sR n)) (v₁₃ := sR n) (h₂₂ := f) ?_ (hprX₁ n)
      (IsPullback.of_hasPullback f (sR n)).flip
    rw [hprX₂]
    exact (IsPullback.of_hasPullback w (sR n)).flip
  haveI hsep : ∀ n, IsSeparated (prX n) := fun n => MorphismProperty.of_isPullback (P := @IsSeparated) (sqX n).flip inferInstance
  have sqWX : ∀ n, IsPullback (wn n) (prX n) (prX (n + 1)) (xn n) := by
    intro n
    have comm : wn n ≫ prX (n + 1) = prX n ≫ xn n := by
      apply pullback.hom_ext
      · rw [Category.assoc, hprX₁, ← Category.assoc, hwn₁, Category.assoc, hxn₁, hprX₁]
      · rw [Category.assoc, hprX₂, hwn₂, Category.assoc, hxn₂, ← Category.assoc, hprX₂]
    have outer : IsPullback (wn n ≫ pullback.fst w (sR (n + 1))) (prX n) (pullback.fst f g) (xn n ≫ pullback.fst f (sR (n + 1))) := by
      rw [hwn₁, hxn₁]; exact (sqX n).flip
    exact IsPullback.of_right outer comm (sqX (n + 1)).flip

  have γcond : ∀ n : ℕ, pullback.fst f (sR n) ≫ f = (φ n ≫ pullback.fst g (sR n)) ≫ g := by
    intro n
    rw [pullback.condition (f := f) (g := sR n), Category.assoc, pullback.condition (f := g) (g := sR n), ← Category.assoc, hφ n]
  let γ : ∀ n : ℕ, pullback f (sR n) ⟶ pullback f g := fun n => pullback.lift (pullback.fst f (sR n)) (φ n ≫ pullback.fst g (sR n)) (γcond n)
  have hγ₁ : ∀ n, γ n ≫ (pullback.fst f g) = pullback.fst f (sR n) := fun n => pullback.lift_fst _ _ _
  have hγ₂ : ∀ n, γ n ≫ (pullback.snd f g) = φ n ≫ pullback.fst g (sR n) := fun n => pullback.lift_snd _ _ _
  have gcond : ∀ n : ℕ, γ n ≫ w = pullback.snd f (sR n) ≫ sR n := by
    intro n; show γ n ≫ (pullback.fst f g) ≫ f = _; rw [← Category.assoc, hγ₁]; exact pullback.condition
  let gΓ : ∀ n : ℕ, pullback f (sR n) ⟶ pullback w (sR n) := fun n => pullback.lift (γ n) (pullback.snd f (sR n)) (gcond n)
  have hgΓ₁ : ∀ n, gΓ n ≫ pullback.fst w (sR n) = γ n := fun n => pullback.lift_fst _ _ _
  have hgΓ₂ : ∀ n, gΓ n ≫ pullback.snd w (sR n) = pullback.snd f (sR n) := fun n => pullback.lift_snd _ _ _
  have hsec : ∀ n, gΓ n ≫ prX n = 𝟙 _ := by
    intro n
    apply pullback.hom_ext
    · rw [Category.assoc, hprX₁, ← Category.assoc, hgΓ₁, hγ₁, Category.id_comp]
    · rw [Category.assoc, hprX₂, hgΓ₂, Category.id_comp]
  haveI hfinΓ : ∀ n, IsFinite (gΓ n) := by
    intro n
    haveI : IsClosedImmersion (gΓ n ≫ prX n) := by rw [hsec]; infer_instance
    haveI : IsClosedImmersion (gΓ n) := IsClosedImmersion.of_comp (gΓ n) (prX n)
    infer_instance
  have hY : ∀ n, IsPullback (xn n) (gΓ n) (gΓ (n + 1)) (wn n) := by
    intro n
    refine isPullback_of_sections (xn n) (wn n) (gΓ n) (gΓ (n + 1)) (prX n) (prX (n + 1)) (hsec n) (hsec (n + 1)) ?_ (sqWX n)
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, reassoc_of% (hgΓ₁ (n + 1)), reassoc_of% (hγ₁ (n + 1)), hxn₁, reassoc_of% (hwn₁ n),
          reassoc_of% (hgΓ₁ n), hγ₁]
      · simp only [Category.assoc, reassoc_of% (hgΓ₁ (n + 1)), hγ₂, reassoc_of% (hφc n), hyn₁, reassoc_of% (hwn₁ n),
          reassoc_of% (hgΓ₁ n)]
    · simp only [Category.assoc, hgΓ₂, hxn₂, hwn₂, reassoc_of% (hgΓ₂ n)]

  obtain ⟨Γ, G, hGfin, e, he, hcomp⟩ :=
    AlgebraicGeometry.exists_isFinite_of_forall_isFinite_isPullback_of_isProper_of_isAdicComplete
      R I (pullback f g) w sR hsR tR htR wn hwn₁ hwn₂ (fun n => pullback f (sR n)) gΓ xn hY
  haveI := hGfin
  let h : Γ ⟶ X := G ≫ (pullback.fst f g)
  haveI : IsProper h := inferInstance

  have sqh : ∀ n, IsPullback (pullback.fst G (pullback.fst w (sR n)))
      (pullback.snd G (pullback.fst w (sR n)) ≫ prX n) h (pullback.fst f (sR n)) :=
    fun n => (IsPullback.of_hasPullback G (pullback.fst w (sR n))).paste_vert (sqX n).flip
  have hiso : ∀ n, IsIso (pullback.snd G (pullback.fst w (sR n)) ≫ prX n) := by
    intro n; rw [← he n, Category.assoc, hsec, Category.comp_id]; infer_instance
  have hn : ∀ n, IsIso (pullback.snd h (pullback.fst f (sR n))) := by
    intro n
    have : pullback.snd h (pullback.fst f (sR n)) = (sqh n).isoPullback.inv ≫ (pullback.snd G (pullback.fst w (sR n)) ≫ prX n) :=
      ((sqh n).isoPullback_inv_snd).symm
    rw [this]; haveI := hiso n; infer_instance
  haveI : IsIso h :=
    AlgebraicGeometry.isIso_of_isProper_of_forall_isIso_pullback_snd_truncation_of_isAdicComplete R I f h sR hsR hn

  have key : ∀ n, (pullback.snd G (pullback.fst w (sR n)) ≫ prX n) ≫ pullback.fst f (sR n) ≫ inv h ≫ G ≫ (pullback.snd f g) =
      (e n).hom ≫ φ n ≫ pullback.fst g (sR n) := by
    intro n
    rw [← Category.assoc, ← (sqh n).w, Category.assoc, IsIso.hom_inv_id_assoc, ← Category.assoc, pullback.condition,
      Category.assoc, ← he n, Category.assoc, reassoc_of% (hgΓ₁ n), hγ₂]
  have key' : ∀ n, (pullback.snd G (pullback.fst w (sR n)) ≫ prX n) ≫ φ n ≫ pullback.fst g (sR n) =
      (e n).hom ≫ φ n ≫ pullback.fst g (sR n) := by
    intro n
    rw [← he n]; simp only [Category.assoc, reassoc_of% (hsec n)]

  refine ⟨inv h ≫ G ≫ (pullback.snd f g), ?_, ?_, ?_⟩
  · show inv h ≫ G ≫ (pullback.snd f g) ≫ g = f
    rw [← pullback.condition, ← Category.assoc G, IsIso.inv_hom_id_assoc]
  · intro n
    haveI := hiso n
    rw [← cancel_epi (pullback.snd G (pullback.fst w (sR n)) ≫ prX n), key n, key' n]
  · intro F' hF' hF'n
    refine AlgebraicGeometry.eq_of_forall_pullback_fst_truncation_comp_eq_of_isProper_of_isSeparated_of_isAdicComplete
      R I f g sR hsR F' (inv h ≫ G ≫ (pullback.snd f g)) hF' ?_ ?_
    · show inv h ≫ G ≫ (pullback.snd f g) ≫ g = f
      rw [← pullback.condition, ← Category.assoc G, IsIso.inv_hom_id_assoc]
    · intro n
      haveI := hiso n
      rw [hF'n n, ← cancel_epi (pullback.snd G (pullback.fst w (sR n)) ≫ prX n), key n, key' n]

end S_AlgebraicGeometry_exists_hom_comp_eq_forall_pullback_fst_comp_eq_of_forall_truncation_of_isFinite_proj_of_isAdicComplete
end P2MW
export P2MW.S_AlgebraicGeometry_exists_hom_comp_eq_forall_pullback_fst_comp_eq_of_forall_truncation_of_isFinite_proj_of_isAdicComplete (solution)
