-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.mem_range_d_of_d_eq_zero_of_forall_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/1362f73e-de0a-579a-87a7-90a97ce5fcba

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_mem_range_d_of_d_eq_zero_of_forall_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace D2Sol

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

theorem coe_mem_smul_iff (J : Ideal A) (p : Submodule A M) (x : p) :
    (x : M) ∈ J • p ↔ x ∈ J • (⊤ : Submodule A p) := by
  have hmap : (J • (⊤ : Submodule A p)).map p.subtype = J • p := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
  constructor
  · intro hx
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext (by simpa using hyx)
    exact this ▸ hy
  · intro hx
    rw [← hmap]
    exact ⟨x, hx, rfl⟩

end D2Sol

open D2Sol in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (i : ℕ) (a : F.cochain K (i + 1)) (ha : F.d K (i + 1) a = 0)
    (h : ∀ n : ℕ, a ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 1))) ⊔ LinearMap.range (F.d K i)) :
    a ∈ LinearMap.range (F.d K i) := by
  classical
  set Z : Submodule A (F.cochain K (i + 1)) := LinearMap.ker (F.d K (i + 1)) with hZ
  set B : Submodule A (F.cochain K (i + 1)) := LinearMap.range (F.d K i) with hB
  have hdd : ∀ y : F.cochain K i, F.d K (i + 1) (F.d K i y) = 0 := fun y => by
    have := congrArg (fun φ => φ y) (AlgebraicGeometry.OModulePresheaf.d_comp_d F K i)
    simpa using this
  have hBZ : B ≤ Z := by
    rintro _ ⟨y, rfl⟩
    exact (LinearMap.mem_ker).mpr (hdd y)

  haveI : Module.Finite A (F.HSucc K i) := (AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper F hc hqc K).2 i
  have hH : IsHausdorff I (F.HSucc K i) := IsHausdorff.of_le_jacobson I _ (IsAdicComplete.le_jacobson_bot I)

  have step : ∀ n : ℕ, a ∈ I ^ n • Z ⊔ B := by
    intro n
    obtain ⟨c, hc'⟩ :=
      AlgebraicGeometry.OModulePresheaf.exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_of_isProper I q F hc hqc K i n
    obtain ⟨u, hu, b, hb, hub⟩ := Submodule.mem_sup.mp (h (n + c))
    have hu' : u ∈ I ^ (n + c) • (⊤ : Submodule A (F.cochain K (i + 1))) :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ _)) hu
    have huZ : u ∈ Z := by
      rw [LinearMap.mem_ker]
      have hbZ : b ∈ Z := hBZ hb
      rw [LinearMap.mem_ker] at hbZ
      have : u = a - b := by rw [← hub]; abel
      rw [this, map_sub, ha, hbZ, sub_zero]
    have := hc' ⟨huZ, hu'⟩
    rw [← hub]
    exact Submodule.add_mem _ this (Submodule.mem_sup_right hb)

  let W : Submodule A Z := B.comap Z.subtype
  let ahat : Z := ⟨a, (LinearMap.mem_ker).mpr ha⟩
  have hcls : ∀ n : ℕ, (Submodule.Quotient.mk ahat : Z ⧸ W) ∈ I ^ n • (⊤ : Submodule A (Z ⧸ W)) := by
    intro n
    obtain ⟨z, hz, b, hb, hzb⟩ := Submodule.mem_sup.mp (step n)
    have hzZ : z ∈ Z := (Submodule.smul_le_right : I ^ n • Z ≤ Z) hz
    have hzhat : (⟨z, hzZ⟩ : Z) ∈ I ^ n • (⊤ : Submodule A Z) := (coe_mem_smul_iff (I ^ n) Z ⟨z, hzZ⟩).mp hz
    have hq : (Submodule.Quotient.mk ahat : Z ⧸ W) = Submodule.Quotient.mk ⟨z, hzZ⟩ := by
      rw [Submodule.Quotient.eq]
      show Z.subtype (ahat - ⟨z, hzZ⟩) ∈ B
      have : Z.subtype (ahat - ⟨z, hzZ⟩) = b := by
        simp only [map_sub, Submodule.coe_subtype]
        show a - z = b
        rw [← hzb]; abel
      rw [this]; exact hb
    rw [hq]
    have := Submodule.mem_map_of_mem (f := W.mkQ) hzhat
    rwa [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at this
  have hzero : (Submodule.Quotient.mk ahat : Z ⧸ W) = 0 :=
    IsHausdorff.haus hH _ (fun n => by rw [SModEq.sub_mem, sub_zero]; exact hcls n)
  have hmem : ahat ∈ W := (Submodule.Quotient.mk_eq_zero W).mp hzero
  exact hmem

end S_AlgebraicGeometry_OModulePresheaf_mem_range_d_of_d_eq_zero_of_forall_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_mem_range_d_of_d_eq_zero_of_forall_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper (solution)
