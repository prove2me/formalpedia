-- Prove2me | solution 1 for AlgebraicGeometry.exists_isFinite_isPullback_of_isProper_of_forall_points_eq_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/82d3dcb7-1d35-5c92-a946-ee39040430ad

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_isFinite_of_forall_isFinite_isPullback_of_isProper_of_isAdicComplete
import Theorems.Thm_AlgebraicGeometry_UniversallyInjective_of_forall_isAlgClosed_points_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isFinite_isPullback_of_isProper_of_forall_points_eq_of_isAdicComplete
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0"
p2m_attr_erase "simp" "TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.cechPushforward_obj AlgebraicGeometry.OModulePresheaf.Hom.coe_cechPushforward_app AlgebraicGeometry.OModulePresheaf.AffHom.coe_cechPushforward_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val"
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isFinite_isPullback_of_isProper_of_forall_points_eq_of_isAdicComplete.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp UniversallyInjective IsProper LocallyQuasiFinite IsFinite Spec Spec.map Scheme IsSeparated Spec.map_id IsProper.of_comp IsFinite.of_isProper_of_locallyQuasiFinite exists_isFinite_of_forall_isFinite_isPullback_of_isProper_of_isAdicComplete UniversallyInjective.of_forall_isAlgClosed_points_eq"
namespace FiniteFormalGAGALevels
p2m_open "AlgebraicGeometry"

theorem isFinite_of_isProper_comp_of_forall_points_eq {Y X S : Scheme.{u}} (g : Y ⟶ X) (p : X ⟶ S)
    [IsSeparated p] [IsProper (g ≫ p)]
    (hinj : ∀ (K : Type u) [Field K] [IsAlgClosed K] (y y' : Spec (CommRingCat.of K) ⟶ Y),
      y ≫ g = y' ≫ g → y = y') :
    IsFinite g := by
  have : IsProper g := IsProper.of_comp g p
  have : UniversallyInjective g := UniversallyInjective.of_forall_isAlgClosed_points_eq g hinj
  exact IsFinite.of_isProper_of_locallyQuasiFinite g

section Levels

variable (R : Type u) [CommRing R] (ϖ : R)

theorem spec_map_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B) (ψ : B →+* C) :
    Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom (ψ.comp φ)) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

noncomputable abbrev sI (n : ℕ) : Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ} ^ (n + 1))) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ Ideal.span {ϖ} ^ (n + 1))))

theorem span_pow_eq (n : ℕ) : Ideal.span {ϖ} ^ (n + 1) = Ideal.span {ϖ ^ (n + 1)} :=
  Ideal.span_singleton_pow ϖ (n + 1)

noncomputable def eQ (n : ℕ) : (R ⧸ Ideal.span {ϖ} ^ (n + 1)) ≃+* (R ⧸ Ideal.span {ϖ ^ (n + 1)}) :=
  Ideal.quotEquivOfEq (span_pow_eq R ϖ n)

@[scoped simp] theorem eQ_mk (n : ℕ) (x : R) :
    eQ R ϖ n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x :=
  Ideal.quotEquivOfEq_mk _ _

@[scoped simp] theorem eQ_symm_mk (n : ℕ) (x : R) :
    (eQ R ϖ n).symm (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := by
  rw [RingEquiv.symm_apply_eq, eQ_mk]

noncomputable def E (n : ℕ) :
    Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ ^ (n + 1)})) ≅ Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ} ^ (n + 1))) where
  hom := Spec.map (CommRingCat.ofHom (eQ R ϖ n).toRingHom)
  inv := Spec.map (CommRingCat.ofHom (eQ R ϖ n).symm.toRingHom)
  hom_inv_id := by
    rw [spec_map_comp]
    have : (eQ R ϖ n).toRingHom.comp (eQ R ϖ n).symm.toRingHom = RingHom.id _ := by
      ext x; simp
    rw [this, CommRingCat.ofHom_id]; exact Spec.map_id _
  inv_hom_id := by
    rw [spec_map_comp]
    have : (eQ R ϖ n).symm.toRingHom.comp (eQ R ϖ n).toRingHom = RingHom.id _ := by
      ext x; simp
    rw [this, CommRingCat.ofHom_id]; exact Spec.map_id _

theorem E_hom_sI (n : ℕ) :
    (E R ϖ n).hom ≫ sI R ϖ n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ Ideal.span {ϖ ^ (n + 1)}))) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [spec_map_comp]
  congr 2

end Levels

section Adapter

variable {R : Type u} [CommRing R] {ϖ : R} {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  {sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ ^ (n + 1)})) ⟶ Spec (CommRingCat.of R)}

theorem isPullback_E (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ Ideal.span {ϖ ^ (n + 1)}))))
    (n : ℕ) : IsPullback (pullback.fst f (sR n)) (pullback.snd f (sR n) ≫ (E R ϖ n).hom) f (sI R ϖ n) := by
  refine (IsPullback.of_hasPullback f (sR n)).of_iso (Iso.refl _) (Iso.refl _) (E R ϖ n) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · rw [hsR n, ← E_hom_sI]; simp

noncomputable def α (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ Ideal.span {ϖ ^ (n + 1)}))))
    (n : ℕ) : pullback f (sR n) ≅ pullback f (sI R ϖ n) :=
  (isPullback_E f hsR n).isoPullback

@[reassoc]
theorem α_hom_fst (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ Ideal.span {ϖ ^ (n + 1)}))))
    (n : ℕ) : (α f hsR n).hom ≫ pullback.fst _ _ = pullback.fst f (sR n) :=
  IsPullback.isoPullback_hom_fst _

@[reassoc]
theorem α_hom_snd (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ Ideal.span {ϖ ^ (n + 1)}))))
    (n : ℕ) : (α f hsR n).hom ≫ pullback.snd _ _ = pullback.snd f (sR n) ≫ (E R ϖ n).hom :=
  IsPullback.isoPullback_hom_snd _

variable {f} in

noncomputable def tI
    (tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ ^ (n + 1)})) ⟶
      Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ ^ (n + 1 + 1)})))
    (n : ℕ) : Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ} ^ (n + 1))) ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ} ^ (n + 1 + 1))) :=
  (E R ϖ n).inv ≫ tR n ≫ (E R ϖ (n + 1)).hom

theorem tI_sI (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ Ideal.span {ϖ ^ (n + 1)}))))
    (tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ ^ (n + 1)})) ⟶
      Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ ^ (n + 1 + 1)})))
    (htR : ∀ n : ℕ, tR n ≫ sR (n + 1) = sR n) (n : ℕ) : tI tR n ≫ sI R ϖ (n + 1) = sI R ϖ n := by
  simp only [tI, Category.assoc]
  rw [E_hom_sI, ← hsR, htR n, hsR n, ← E_hom_sI, Iso.inv_hom_id_assoc]

noncomputable def xI
    (tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ ^ (n + 1)})) ⟶
      Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ ^ (n + 1 + 1)})))
    (hI : ∀ n : ℕ, tI tR n ≫ sI R ϖ (n + 1) = sI R ϖ n) (n : ℕ) :
    pullback f (sI R ϖ n) ⟶ pullback f (sI R ϖ (n + 1)) :=
  pullback.map _ _ _ _ (𝟙 _) (tI tR n) (𝟙 _) (by simp) (by rw [Category.comp_id, hI])

@[reassoc]
theorem xI_fst
    (tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ ^ (n + 1)})) ⟶
      Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ ^ (n + 1 + 1)})))
    (hI : ∀ n : ℕ, tI tR n ≫ sI R ϖ (n + 1) = sI R ϖ n) (n : ℕ) :
    xI f tR hI n ≫ pullback.fst f (sI R ϖ (n + 1)) = pullback.fst f (sI R ϖ n) := by
  simp only [xI, pullback.lift_fst, Category.comp_id]

@[reassoc]
theorem xI_snd
    (tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ ^ (n + 1)})) ⟶
      Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ ^ (n + 1 + 1)})))
    (hI : ∀ n : ℕ, tI tR n ≫ sI R ϖ (n + 1) = sI R ϖ n) (n : ℕ) :
    xI f tR hI n ≫ pullback.snd f (sI R ϖ (n + 1)) = pullback.snd f (sI R ϖ n) ≫ tI tR n := by
  simp only [xI, pullback.lift_snd]

theorem xn_α (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ Ideal.span {ϖ ^ (n + 1)}))))
    (tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ ^ (n + 1)})) ⟶
      Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ ^ (n + 1 + 1)})))
    (hI : ∀ n : ℕ, tI tR n ≫ sI R ϖ (n + 1) = sI R ϖ n)
    (xn : ∀ n : ℕ, pullback f (sR n) ⟶ pullback f (sR (n + 1)))
    (hxn₁ : ∀ n : ℕ, xn n ≫ pullback.fst f (sR (n + 1)) = pullback.fst f (sR n))
    (hxn₂ : ∀ n : ℕ, xn n ≫ pullback.snd f (sR (n + 1)) = pullback.snd f (sR n) ≫ tR n)
    (n : ℕ) : xn n ≫ (α f hsR (n + 1)).hom = (α f hsR n).hom ≫ xI f tR hI n := by
  apply pullback.hom_ext
  · rw [Category.assoc, α_hom_fst, Category.assoc, xI_fst, α_hom_fst, hxn₁]
  · rw [Category.assoc, α_hom_snd, Category.assoc, xI_snd, α_hom_snd_assoc, ← Category.assoc, hxn₂, Category.assoc]
    simp only [tI, Iso.hom_inv_id_assoc]

end Adapter

theorem main
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ϖ : R) [IsAdicComplete (Ideal.span {ϖ}) R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ ^ (n + 1)})) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ Ideal.span {ϖ ^ (n + 1)}))))
    (tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ ^ (n + 1)})) ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ ^ (n + 1 + 1)})))
    (htR : ∀ n : ℕ, tR n ≫ sR (n + 1) = sR n)
    (xn : ∀ n : ℕ, Limits.pullback f (sR n) ⟶ Limits.pullback f (sR (n + 1)))
    (hxn₁ : ∀ n : ℕ, xn n ≫ Limits.pullback.fst f (sR (n + 1)) = Limits.pullback.fst f (sR n))
    (hxn₂ : ∀ n : ℕ, xn n ≫ Limits.pullback.snd f (sR (n + 1)) = Limits.pullback.snd f (sR n) ≫ tR n)
    (Y : ℕ → Scheme.{u}) (g : ∀ n : ℕ, Y n ⟶ Limits.pullback f (sR n))
    [∀ n : ℕ, IsProper (g n ≫ Limits.pullback.snd f (sR n))]
    (yn : ∀ n : ℕ, Y n ⟶ Y (n + 1))
    (hY : ∀ n : ℕ, IsPullback (yn n) (g n) (g (n + 1)) (xn n))
    (hinj : ∀ (n : ℕ) (K : Type u) [Field K] [IsAlgClosed K] (y y' : Spec (CommRingCat.of K) ⟶ Y n),
      y ≫ g n = y' ≫ g n → y = y') :
    (∀ n : ℕ, IsFinite (g n)) ∧
    ∃ (Yf : Scheme.{u}) (G : Yf ⟶ X) (_ : IsFinite G) (φ : ∀ n : ℕ, Y n ⟶ Yf),
      (∀ n : ℕ, IsPullback (φ n) (g n) G (Limits.pullback.fst f (sR n))) ∧
      (∀ n : ℕ, yn n ≫ φ (n + 1) = φ n) := by
  have hfin : ∀ n : ℕ, IsFinite (g n) := fun n =>
    isFinite_of_isProper_comp_of_forall_points_eq (g n) (Limits.pullback.snd f (sR n)) (hinj n)
  refine ⟨hfin, ?_⟩
  have hI : ∀ n : ℕ, tI tR n ≫ sI R ϖ (n + 1) = sI R ϖ n := tI_sI hsR tR htR
  have hY' : ∀ n : ℕ, IsPullback (yn n) (g n ≫ (α f hsR n).hom) (g (n + 1) ≫ (α f hsR (n + 1)).hom) (xI f tR hI n) :=
    fun n => (hY n).of_iso (Iso.refl _) (Iso.refl _) (α f hsR n) (α f hsR (n + 1)) (by simp) (by simp) (by simp)
      (xn_α f hsR tR hI xn hxn₁ hxn₂ n)
  haveI : ∀ n : ℕ, IsFinite (g n ≫ (α f hsR n).hom) := fun n => inferInstance
  obtain ⟨Yf, G, hG, e, he₁, he₂⟩ :=
    AlgebraicGeometry.exists_isFinite_of_forall_isFinite_isPullback_of_isProper_of_isAdicComplete R
      (Ideal.span {ϖ}) X f (sI R ϖ) (fun _ => rfl) (tI tR) hI (xI f tR hI) (xI_fst f tR hI) (xI_snd f tR hI) Y
      (fun n => g n ≫ (α f hsR n).hom) yn hY'
  refine ⟨Yf, G, hG, fun n => (e n).inv ≫ pullback.fst _ _, ?_, ?_⟩
  · intro n
    refine (IsPullback.of_hasPullback G (pullback.fst f (sI R ϖ n))).of_iso (e n) (Iso.refl _) (α f hsR n).symm
      (Iso.refl _) (by simp) ?_ (by simp) ?_
    · rw [← he₁ n]
      simp only [Category.assoc, Iso.symm_hom, Iso.hom_inv_id, Category.comp_id]
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
      rw [Iso.eq_inv_comp, α_hom_fst]
  · intro n
    have h2 : yn n = (e n).inv ≫ (_ ≫ (e (n + 1)).hom) := (Iso.eq_inv_comp _).mpr (he₂ n).symm
    rw [h2]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_fst, Category.comp_id]

end AlgebraicGeometry.FiniteFormalGAGALevels
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isFinite_isPullback_of_isProper_of_forall_points_eq_of_isAdicComplete.AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isFinite_isPullback_of_isProper_of_forall_points_eq_of_isAdicComplete.AlgebraicGeometry.FiniteFormalGAGALevels"
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_isFinite_isPullback_of_isProper_of_forall_points_eq_of_isAdicComplete.AlgebraicGeometry"

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ϖ : R) [IsAdicComplete (Ideal.span {ϖ}) R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]

    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ ^ (n + 1)})) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ Ideal.span {ϖ ^ (n + 1)}))))
    (tR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ ^ (n + 1)})) ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ϖ ^ (n + 1 + 1)})))
    (htR : ∀ n : ℕ, tR n ≫ sR (n + 1) = sR n)

    (xn : ∀ n : ℕ, Limits.pullback f (sR n) ⟶ Limits.pullback f (sR (n + 1)))
    (hxn₁ : ∀ n : ℕ, xn n ≫ Limits.pullback.fst f (sR (n + 1)) = Limits.pullback.fst f (sR n))
    (hxn₂ : ∀ n : ℕ, xn n ≫ Limits.pullback.snd f (sR (n + 1)) = Limits.pullback.snd f (sR n) ≫ tR n)

    (Y : ℕ → Scheme.{u}) (g : ∀ n : ℕ, Y n ⟶ Limits.pullback f (sR n))
    [∀ n : ℕ, IsProper (g n ≫ Limits.pullback.snd f (sR n))]
    (yn : ∀ n : ℕ, Y n ⟶ Y (n + 1))
    (hY : ∀ n : ℕ, IsPullback (yn n) (g n) (g (n + 1)) (xn n))
    (hinj : ∀ (n : ℕ) (K : Type u) [Field K] [IsAlgClosed K] (y y' : Spec (CommRingCat.of K) ⟶ Y n),
      y ≫ g n = y' ≫ g n → y = y') :

    (∀ n : ℕ, IsFinite (g n)) ∧

    ∃ (Yf : Scheme.{u}) (G : Yf ⟶ X) (_ : IsFinite G) (φ : ∀ n : ℕ, Y n ⟶ Yf),
      (∀ n : ℕ, IsPullback (φ n) (g n) G (Limits.pullback.fst f (sR n))) ∧
      (∀ n : ℕ, yn n ≫ φ (n + 1) = φ n) :=
  AlgebraicGeometry.FiniteFormalGAGALevels.main R ϖ X f sR hsR tR htR xn hxn₁ hxn₂ Y g yn hY hinj

end S_AlgebraicGeometry_exists_isFinite_isPullback_of_isProper_of_forall_points_eq_of_isAdicComplete
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isFinite_isPullback_of_isProper_of_forall_points_eq_of_isAdicComplete (solution)
