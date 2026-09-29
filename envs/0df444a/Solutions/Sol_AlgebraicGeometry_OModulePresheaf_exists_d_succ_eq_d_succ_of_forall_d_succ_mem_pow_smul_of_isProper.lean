-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_smul_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/95a0612a-1f8e-575d-a574-fe7997364f5a

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_unit_cochain_linearMap_comp_eq_d_of_isProper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_smul_of_isProper
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace G2Sol

theorem apply_mem_smul_top {A : Type*} [CommRing A] {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    [∀ i, Module A (M i)] (J : Ideal A) {x : ∀ i, M i} (hx : x ∈ J • (⊤ : Submodule A (∀ i, M i))) (i : ι) :
    x i ∈ J • (⊤ : Submodule A (M i)) := by
  have := Submodule.mem_map_of_mem (f := (LinearMap.proj i : (∀ i, M i) →ₗ[A] M i)) hx
  rw [Submodule.map_smul''] at this
  exact Submodule.smul_mono le_rfl le_top this

theorem mem_smul_top_of_forall {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)] (J : Ideal A) {x : ∀ i, M i}
    (hx : ∀ i, x i ∈ J • (⊤ : Submodule A (M i))) : x ∈ J • (⊤ : Submodule A (∀ i, M i)) := by
  have hsum : x = ∑ i, (LinearMap.single A M i) (x i) := by
    ext j
    simp [Finset.sum_apply, LinearMap.single_apply]
  rw [hsum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have := Submodule.mem_map_of_mem (f := (LinearMap.single A M i : M i →ₗ[A] ∀ i, M i)) (hx i)
  rw [Submodule.map_smul''] at this
  exact Submodule.smul_mono le_rfl le_top this

theorem map_mem_smul_top {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (J : Ideal A) {x : M}
    (hx : x ∈ J • (⊤ : Submodule A M)) : f x ∈ J • (⊤ : Submodule A N) := by
  have := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at this
  exact Submodule.smul_mono le_rfl le_top this

end G2Sol

open G2Sol in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)} [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hq : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (i n : ℕ) :
    ∃ c : ℕ, ∀ w : F.cochain K (i + 1),
      (∀ s : K.Idx (i + 2), F.d K (i + 1) w s ∈ I ^ (n + c) • (⊤ : Submodule A (F.obj (K.inter s)))) →
      ∃ w' : F.cochain K (i + 1),
        (∀ s : K.Idx (i + 1), w' s ∈ I ^ n • (⊤ : Submodule A (F.obj (K.inter s)))) ∧
        F.d K (i + 1) w' = F.d K (i + 1) w := by
  classical
  obtain ⟨Y, q', hq', K', L, Q, hQL, hdL, hdQ⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_unit_cochain_linearMap_comp_eq_d_of_isProper q F hc hq K
  haveI : IsProper q' := hq'
  obtain ⟨c, hc'⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_unit_of_isProper I q' K' i n
  refine ⟨c, fun w hw => ?_⟩
  have hdw : F.d K (i + 1) w ∈ I ^ (n + c) • (⊤ : Submodule A (F.cochain K (i + 1 + 1))) :=
    mem_smul_top_of_forall _ hw
  have h1 : ∀ s : K'.Idx (i + 2), (OModulePresheaf.unit q').d K' (i + 1) (L (i + 1) w) s ∈
      I ^ (n + c) • (⊤ : Submodule A ((OModulePresheaf.unit q').obj (K'.inter s))) := by
    intro s
    rw [hdL]
    exact apply_mem_smul_top _ (map_mem_smul_top (L (i + 1 + 1)) _ hdw) s
  obtain ⟨v', hv'1, hv'2⟩ := hc' (L (i + 1) w) h1
  refine ⟨Q (i + 1) v', fun s => ?_, ?_⟩
  · exact apply_mem_smul_top _ (map_mem_smul_top (Q (i + 1)) _ (mem_smul_top_of_forall _ hv'1)) s
  · rw [hdQ, hv'2, hdL, hQL]

end S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_smul_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_d_succ_of_forall_d_succ_mem_pow_smul_of_isProper (solution)
