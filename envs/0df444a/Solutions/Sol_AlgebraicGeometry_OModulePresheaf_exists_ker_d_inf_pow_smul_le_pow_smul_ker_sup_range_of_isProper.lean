-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/926cd0eb-1b4f-5f53-a73c-235169c81679

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_unit_of_isProper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_of_isProper
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (i n : ℕ) :
    ∃ c : ℕ, LinearMap.ker (F.d K (i + 1)) ⊓ I ^ (n + c) • (⊤ : Submodule A (F.cochain K (i + 1))) ≤
      I ^ n • LinearMap.ker (F.d K (i + 1)) ⊔ LinearMap.range (F.d K i) := by
  classical
  obtain ⟨Y, q', hq', K', L, Q, hQL, hdL, hdQ⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_unit_cochain_linearMap_comp_eq_d_of_isProper q F hc hqc K
  haveI := hq'
  obtain ⟨c, hc'⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_unit_of_isProper I q' K' i n
  refine ⟨c, fun z hz => ?_⟩
  obtain ⟨hzZ, hzI⟩ := Submodule.mem_inf.mp hz

  have h1 : L (i + 1) z ∈ LinearMap.ker ((OModulePresheaf.unit q').d K' (i + 1)) ⊓
      I ^ (n + c) • (⊤ : Submodule A ((OModulePresheaf.unit q').cochain K' (i + 1))) := by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [LinearMap.mem_ker, hdL, LinearMap.mem_ker.mp hzZ, map_zero]
    · have : (I ^ (n + c) • (⊤ : Submodule A (F.cochain K (i + 1)))).map (L (i + 1)) ≤
          I ^ (n + c) • (⊤ : Submodule A ((OModulePresheaf.unit q').cochain K' (i + 1))) := by
        rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
      exact this (Submodule.mem_map_of_mem hzI)
  have h2 := hc' h1

  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp h2
  have hzQ : z = Q (i + 1) u + Q (i + 1) v := by rw [← map_add, huv, hQL]
  rw [hzQ]
  refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · have : (I ^ n • LinearMap.ker ((OModulePresheaf.unit q').d K' (i + 1))).map (Q (i + 1)) ≤
        I ^ n • LinearMap.ker (F.d K (i + 1)) := by
      rw [Submodule.map_smul'']
      refine Submodule.smul_mono le_rfl ?_
      rintro _ ⟨y, hy, rfl⟩
      rw [LinearMap.mem_ker, hdQ, LinearMap.mem_ker.mp hy, map_zero]
    exact this (Submodule.mem_map_of_mem hu)
  · obtain ⟨w, rfl⟩ := hv
    exact ⟨Q i w, (hdQ i w)⟩

end S_AlgebraicGeometry_OModulePresheaf_exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_of_isProper (solution)
