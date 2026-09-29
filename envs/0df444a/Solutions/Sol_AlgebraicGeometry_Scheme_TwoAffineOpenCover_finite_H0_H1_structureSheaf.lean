-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.finite_H0_H1_structureSheaf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/86f212d6-0c24-5772-bbe6-237ad3359115

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_toOrderedAffineCover_iff
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isProper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finite_H0_H1_structureSheaf
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

universe u

namespace TwoChartCech
p2m_export "TwoChartCech" "Cover Sections Sections.cechDiff_apply Cover.lineBundle_r0_apply Cover.lineBundle_r1_apply kerMap cokerMap"
namespace Sk1
p2m_open "TwoChartCech"

universe uR uK uC

variable {R : Type uR} [CommRing R]
variable {K0 K1 : Type uK} [AddCommGroup K0] [Module R K0] [AddCommGroup K1] [Module R K1]
variable {C0 C1 : Type uK} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]

theorem kerMap_bijective_of_bijective (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0)
    (ι1 : K1 →ₗ[R] C1) (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) (h0 : Function.Bijective ι0)
    (h1 : Function.Injective ι1) : Function.Bijective (kerMap dK d ι0 ι1 comm) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply h0.1
    exact congrArg Subtype.val hxy
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := h0.2 y
    have hx : x ∈ LinearMap.ker dK := by
      rw [LinearMap.mem_ker] at hy ⊢
      apply h1
      rw [map_zero, ← LinearMap.comp_apply, ← comm, LinearMap.comp_apply, hy]
    exact ⟨⟨x, hx⟩, rfl⟩

theorem cokerMap_bijective_of_bijective (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0)
    (ι1 : K1 →ₗ[R] C1) (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) (h0 : Function.Surjective ι0)
    (h1 : Function.Bijective ι1) : Function.Bijective (cokerMap dK d ι0 ι1 comm) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [LinearMap.mem_ker] at hq
    change Submodule.Quotient.mk (ι1 y) = 0 at hq
    rw [Submodule.Quotient.mk_eq_zero] at hq ⊢
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hq
    obtain ⟨x, rfl⟩ := h0 c
    refine ⟨x, h1.1 ?_⟩
    rw [← hc, ← LinearMap.comp_apply, ← comm, LinearMap.comp_apply]
  · intro q
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨y, rfl⟩ := h1.2 c
    exact ⟨Submodule.Quotient.mk y, rfl⟩

end TwoChartCech.Sk1

open CategoryTheory AlgebraicGeometry in

theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ Spec (.of R)) [IsProper c] :
    Module.Finite R (𝒱.structureSheafSections c).H0 ∧ Module.Finite R (𝒱.structureSheafSections c).H1 := by
  obtain ⟨h0, h1⟩ := (AlgebraicGeometry.OModulePresheaf.cechFinite_toOrderedAffineCover_iff
    (OModulePresheaf.unit c) 𝒱).mp (OModulePresheaf.cechFinite_unit_of_isProper c 𝒱.toOrderedAffineCover)

  let S := (OModulePresheaf.unit c).twoChartSections 𝒱
  let T := 𝒱.structureSheafSections c
  let ι0 : S.M0 × S.M1 →ₗ[R] T.M0 × T.M1 :=
    { toFun := fun p => p, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let ι1 : S.M01 →ₗ[R] T.M01 :=
    { toFun := fun p => p, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have comm : T.cechDiff ∘ₗ ι0 = ι1 ∘ₗ S.cechDiff := by
    apply LinearMap.ext
    rintro ⟨x0, x1⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, TwoChartCech.Sections.cechDiff_apply,
      TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Cover.lineBundle_r1_apply,
      TwoChartCech.Cover.lineBundle_r0_apply, Units.val_one, one_mul]
    rfl
  have hι0 : Function.Bijective ι0 := ⟨fun _ _ h => h, fun p => ⟨p, rfl⟩⟩
  have hι1 : Function.Bijective ι1 := ⟨fun _ _ h => h, fun p => ⟨p, rfl⟩⟩
  haveI := h0
  haveI := h1
  exact ⟨Module.Finite.equiv (LinearEquiv.ofBijective _
      (TwoChartCech.Sk1.kerMap_bijective_of_bijective S.cechDiff T.cechDiff ι0 ι1 comm hι0 hι1.1)),
    Module.Finite.equiv (LinearEquiv.ofBijective _
      (TwoChartCech.Sk1.cokerMap_bijective_of_bijective S.cechDiff T.cechDiff ι0 ι1 comm hι0.2 hι1))⟩

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finite_H0_H1_structureSheaf
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finite_H0_H1_structureSheaf (solution)
