-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback_of_descent_of_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/63d64e26-b20f-5d5e-9276-3e923ae1181f

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_smoothOfRelativeDimension_of_forall_topologicalKrullDim_eq
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_descendsAlong_surjective_inf_flat_inf_quasiCompact
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_preimage_singleton_eq
import Theorems.Thm_AlgebraicGeometry_existsUnique_specMap_comp_eq_of_faithfullyFlat
import Theorems.Thm_Module_FaithfullyFlat_exists_ringHom_isAlgClosed_comp_algebraMap_eq
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_level_indep_and_span_of_isPullback_of_faithfullyFlat
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isPullback_of_descent_of_faithfullyFlat
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isPullback_of_descent_of_faithfullyFlat.AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open scoped TensorProduct

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective SmoothOfRelativeDimension IsProper Scheme.Modules.pullback QuasiCompact Spec Spec.map Scheme Smooth Flat HasRingHomProperty.Spec_iff Scheme.Modules HasRingHomProperty Scheme.Modules.geomFibreH0Finrank PolarisedAbelianScheme PolarisedAbelianScheme.IsPullback Scheme.Modules.IsInvertible Scheme.Modules.ClosedImmersionBySections SmoothOfRelativeDimension.descendsAlong_surjective_inf_flat_inf_quasiCompact SmoothOfRelativeDimension.topologicalKrullDim_preimage_singleton_eq existsUnique_specMap_comp_eq_of_faithfullyFlat Scheme.Modules.geomFibreH0Finrank_comp_eq Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback"
namespace StructureDescentAux
p2m_open "AlgebraicGeometry"

universe u

variable {S : Type u} [CommRing S] {S' : Type u} [CommRing S'] [Algebra S S']
variable {X A' : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')}

lemma nsmul_val_congr (L : RelativeGroupLaw S f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂)
    (n : ℕ) (x : SchemeHomOver t₁ f) (y : SchemeHomOver t₂ f) (hxy : x.1 = y.1) :
    (L.nsmul t₁ n x).1 = (L.nsmul t₂ n y).1 := by
  subst h; cases x; cases y; cases hxy; rfl

lemma one_val_congr (L : RelativeGroupLaw S f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂) :
    (L.one t₁).1 = (L.one t₂).1 := by
  subst h; rfl

lemma one_comp (c : A' ⟶ X) (hc : CategoryTheory.IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (hcmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' f'),
      (L'.mul t' x y).1 ≫ c =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')))
          ⟨x.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, y.2]⟩).1)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) :
    (L'.one t').1 ≫ c = (L.one (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')))).1 := by
  letI := L.pointGroup (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')))
  let e : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S'))) f :=
    ⟨(L'.one t').1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, (L'.one t').2]⟩
  have h : e * e = e := by
    apply Subtype.ext
    change (L.mul _ e e).1 = e.1
    have := hcmul t' (L'.one t') (L'.one t')
    rw [L'.one_mul] at this
    exact this.symm
  have he : e = 1 := by
    calc e = e * e * e⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
      _ = e * e⁻¹ := by rw [h]
      _ = 1 := mul_inv_cancel e
  exact congrArg Subtype.val he

lemma nsmul_comp (c : A' ⟶ X) (hc : CategoryTheory.IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (hcmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' f'),
      (L'.mul t' x y).1 ≫ c =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')))
          ⟨x.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, y.2]⟩).1)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (n : ℕ) (x : SchemeHomOver t' f') :
    (L'.nsmul t' n x).1 ≫ c =
      (L.nsmul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S'))) n
        ⟨x.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, x.2]⟩).1 := by
  induction n with
  | zero => exact one_comp c hc L L' hcmul t'
  | succ n ih =>
    rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, hcmul]
    congr 1
    apply congrArg (fun z => L.mul _ z _)
    exact Subtype.ext ih

end AlgebraicGeometry.StructureDescentAux

open AlgebraicGeometry.StructureDescentAux in
theorem solution
    {g d n : ℕ} {S : Type} [CommRing S]
    (S' : Type) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    (u' : PolarisedAbelianScheme g d n S')
    (v'' : PolarisedAbelianScheme g d n (S' ⊗[S] S')) (a₁ a₂ : v''.A ⟶ u'.A)
    (ha₁ : CategoryTheory.IsPullback a₁ v''.f u'.f (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (ha₂ : CategoryTheory.IsPullback a₂ v''.f u'.f (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (ha₁mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (x y : SchemeHomOver t' v''.f),
      (v''.L.mul t' x y).1 ≫ a₁ =
        (u'.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom))
          ⟨x.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, y.2]⟩).1)
    (ha₂mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (x y : SchemeHomOver t' v''.f),
      (v''.L.mul t' x y).1 ≫ a₂ =
        (u'.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom))
          ⟨x.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, y.2]⟩).1)
    (ha₁P : ∀ i, (v''.P i).1 ≫ a₁ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom) ≫ (u'.P i).1)
    (ha₂P : ∀ i, (v''.P i).1 ≫ a₂ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom) ≫ (u'.P i).1)

    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of S)) (c : u'.A ⟶ X)
    (hc : CategoryTheory.IsPullback c u'.f f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (hca : a₁ ≫ c = a₂ ≫ c)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (hLva : Scheme.Modules.ClosedImmersionBySections L f)
    (hcL : Nonempty ((Scheme.Modules.pullback c).obj L ≅ u'.pol)) :
    ∃ u : PolarisedAbelianScheme g d n S, ∃ (hA : u.A = X), PolarisedAbelianScheme.IsPullback (algebraMap S S') u u' := by
  classical
  set ι : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S) := Spec.map (CommRingCat.ofHom (algebraMap S S')) with hι

  have hsurjfun : Function.Surjective ι.base := by
    intro x
    obtain ⟨y, hy⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := S) (B := S') x
    exact ⟨y, hy⟩
  haveI hsurj : Surjective ι := ⟨hsurjfun⟩
  haveI hflat : Flat ι := by
    rw [hι, HasRingHomProperty.Spec_iff (P := @Flat)]
    change (algebraMap S S').Flat
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) ι := ⟨⟨hsurj, hflat⟩, inferInstance⟩
  have hcoface : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S')) ≫ ι =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom) ≫ ι := by
    rw [hι, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext s
    change Algebra.TensorProduct.includeLeftRingHom (algebraMap S S' s) =
      (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S') (algebraMap S S' s)
    rw [AlgHom.commutes]
    exact (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').commutes s

  obtain ⟨LX, hcmul, hcomm⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat
      S' f u'.f c hc v''.f a₁ a₂ ha₁ ha₂ hca u'.L v''.L ha₁mul ha₂mul

  have hbundle : AbelianSchemePropertyBundle S f :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.of_isPullback_of_faithfullyFlat S' c hc u'.bundle LX

  haveI : Smooth u'.f := u'.bundle.smooth
  have hrel' : SmoothOfRelativeDimension g u'.f :=
    GoodReductionJacobian.RelativeGroupLaw.smoothOfRelativeDimension_of_forall_topologicalKrullDim_eq u'.L g u'.dim_fibre
  haveI := AlgebraicGeometry.SmoothOfRelativeDimension.descendsAlong_surjective_inf_flat_inf_quasiCompact.{0} g
  have hrel : SmoothOfRelativeDimension g f :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @SmoothOfRelativeDimension g)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hc.flip hQ hrel'
  have hdim : ∀ s : ↥(Spec (CommRingCat.of S)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g := fun s =>
    AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_preimage_singleton_eq f g s
      (hbundle.connectedFibres s).nonempty

  have key : ∀ i, Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S')) ≫ ((u'.P i).1 ≫ c) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom) ≫ ((u'.P i).1 ≫ c) := by
    intro i
    rw [← Category.assoc, ← Category.assoc]
    have e1 : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S')) ≫ (u'.P i).1 =
        (v''.P i).1 ≫ a₁ := (ha₁P i).symm
    have e2 : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom) ≫ (u'.P i).1 =
        (v''.P i).1 ≫ a₂ := (ha₂P i).symm
    rw [e1, e2, Category.assoc, Category.assoc, hca]
  have hPd : ∀ i, ∃ p : Spec (CommRingCat.of S) ⟶ X, ι ≫ p = (u'.P i).1 ≫ c := fun i =>
    (AlgebraicGeometry.existsUnique_specMap_comp_eq_of_faithfullyFlat ((u'.P i).1 ≫ c) (key i)).exists
  choose p hp using hPd

  have huniq : ∀ {Y : Scheme.{0}} (q₁ q₂ : Spec (CommRingCat.of S) ⟶ Y), ι ≫ q₁ = ι ≫ q₂ → q₁ = q₂ := by
    intro Y q₁ q₂ h
    have hex := AlgebraicGeometry.existsUnique_specMap_comp_eq_of_faithfullyFlat (B := S) (B' := S') (ι ≫ q₂)
      (by rw [← Category.assoc, ← Category.assoc, hcoface])
    exact hex.unique h rfl
  have hpf : ∀ i, p i ≫ f = 𝟙 _ := by
    intro i
    apply huniq
    rw [← Category.assoc, hp i, Category.assoc, hc.w, ← Category.assoc, (u'.P i).2, Category.id_comp, Category.comp_id]
  let P : Fin (2 * g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f := fun i => ⟨p i, hpf i⟩
  have hPc : ∀ i, (u'.P i).1 ≫ c = ι ≫ (P i).1 := fun i => (hp i).symm

  have hPt : ∀ i, LX.nsmul (𝟙 _) n (P i) = LX.one (𝟙 _) := by
    intro i
    apply Subtype.ext
    apply huniq

    have h1 : ι ≫ (LX.nsmul (𝟙 _) n (P i)).1 = (LX.nsmul (ι ≫ 𝟙 _) n (schemeHomOverComp ι rfl (P i))).1 := by
      rw [← LX.nsmul_natural (𝟙 _) (ι ≫ 𝟙 _) ι rfl n (P i)]; rfl
    have h2 : (LX.nsmul (ι ≫ 𝟙 _) n (schemeHomOverComp ι rfl (P i))).1 =
        (LX.nsmul (𝟙 _ ≫ ι) n ⟨(u'.P i).1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, (u'.P i).2]⟩).1 :=
      nsmul_val_congr LX (by simp) n _ _ (by rw [schemeHomOverComp_coe]; exact (hPc i).symm)
    have h3 := nsmul_comp c hc LX u'.L hcmul (𝟙 _) n (u'.P i)
    have h4 : ι ≫ (LX.one (𝟙 _)).1 = (LX.one (ι ≫ 𝟙 _)).1 := by
      rw [← LX.one_natural (𝟙 _) (ι ≫ 𝟙 _) ι rfl]; rfl
    rw [h1, h2, ← h3, u'.P_torsion i, one_comp c hc LX u'.L hcmul, h4]
    exact one_val_congr LX (by simp [hι])

  obtain ⟨hind, hspan⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.level_indep_and_span_of_isPullback_of_faithfullyFlat
      S' LX u'.L c hc hcmul n P u'.P hPc u'.P_indep u'.P_span

  haveI : IsProper f := hbundle.proper
  have hpol : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k), Scheme.Modules.geomFibreH0Finrank f L k sk = d := by
    intro k _ _ sk
    obtain ⟨K, _, _, j, sK, hsK⟩ := Module.FaithfullyFlat.exists_ringHom_isAlgClosed_comp_algebraMap_eq S' k sk
    rw [← AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_comp_eq f L hL k K sk j, ← hsK,
      ← AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback (algebraMap S S') f u'.f c hc L u'.pol
        hcL.some K sK]
    exact u'.pol_finrank K sK

  refine ⟨⟨X, f, LX, hcomm u'.comm, hbundle, hdim, P, hPt, hind, hspan, L, hL, hLva, hpol⟩, rfl, c, hc, ?_, hPc, hcL⟩
  intro T t' x y
  exact hcmul t' x y

end S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isPullback_of_descent_of_faithfullyFlat
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isPullback_of_descent_of_faithfullyFlat (solution)
