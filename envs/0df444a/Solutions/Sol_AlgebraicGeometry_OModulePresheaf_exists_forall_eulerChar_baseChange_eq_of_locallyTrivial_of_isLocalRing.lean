-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_forall_eulerChar_baseChange_eq_of_locallyTrivial_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/bb8346b9-f849-5f00-af4b-d63f8028bf84

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial
import Theorems.Thm_Module_exists_forall_alternatingSum_finrank_cohomology_baseChange_eq_of_flat_complex_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eulerChar_baseChange_eq_of_locallyTrivial_of_isLocalRing
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace MumfordModelChi

theorem isEmpty_idx {V : Scheme.{u}} (K : V.OrderedAffineCover) {i : ℕ} (hi : Fintype.card K.ι < i + 1) :
    IsEmpty (K.Idx i) := by
  refine ⟨fun s => ?_⟩
  have hinj : Function.Injective s.1 := s.2.injective
  have := Fintype.card_le_of_injective s.1 hinj
  simp only [Fintype.card_fin] at this
  omega

theorem subsingleton_cochain {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) {i : ℕ} (hi : Fintype.card K.ι < i + 1) :
    Subsingleton (F.cochain K i) := by
  haveI := isEmpty_idx K hi
  infer_instance

end MumfordModelChi

open MumfordModelChi in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R))
    [IsProper π] [Flat π] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (𝒰 : X.OrderedAffineCover) :
    ∃ χ₀ : ℤ, ∀ (A : Type u) [Field A] [Algebra R A],
      (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).eulerChar (𝒰.baseChange π A)
        = χ₀ := by

  rcases Nat.eq_zero_or_pos (Fintype.card 𝒰.ι) with h0 | hpos
  ·
    refine ⟨0, fun A _ _ => ?_⟩
    rw [OModulePresheaf.eulerChar_def]
    have : Fintype.card (𝒰.baseChange π A).ι = 0 := h0
    rw [this, Finset.range_zero, Finset.sum_empty]
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card 𝒰.ι = m + 1 := ⟨Fintype.card 𝒰.ι - 1, by omega⟩
  haveI hflat : ∀ i, Module.Flat R ((OModulePresheaf.ofModules π M).cochain 𝒰 i) := fun i =>
    OModulePresheaf.flat_cochain_ofModules_of_locallyTrivial π M htriv 𝒰 i
  have hfinC : (OModulePresheaf.ofModules π M).CechFinite 𝒰 := OModulePresheaf.cechFinite_ofModules_of_locallyTrivial π M htriv 𝒰
  obtain ⟨χ₀, hχ⟩ :=
    Module.exists_forall_alternatingSum_finrank_cohomology_baseChange_eq_of_flat_complex_of_isLocalRing R
      (fun i => (OModulePresheaf.ofModules π M).cochain 𝒰 i) (fun i => (OModulePresheaf.ofModules π M).d 𝒰 i) (fun i => (OModulePresheaf.ofModules π M).d_comp_d 𝒰 i) m
      (fun i hi => subsingleton_cochain (OModulePresheaf.ofModules π M) 𝒰 (by omega)) hfinC.1 hfinC.2
  refine ⟨χ₀, fun A _ _ => ?_⟩

  obtain ⟨⟨⟨e₀⟩, hS⟩, -⟩ := OModulePresheaf.nonempty_cech_baseChange_equiv_of_locallyTrivial π 𝒰 M htriv A
  choose φ hφ using hS
  have key := hχ A
    ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
      ((Scheme.Modules.pullback (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).H0
      (𝒰.baseChange π A))
    e₀
    (fun i => (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
      ((Scheme.Modules.pullback (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).HSucc
      (𝒰.baseChange π A) i)
    φ (fun i => (hφ i).1) (fun i => (hφ i).2)
  rw [OModulePresheaf.eulerChar_def, show Fintype.card (𝒰.baseChange π A).ι = m + 1 from hm, Finset.sum_range_succ']
  rw [← key]
  simp only [OModulePresheaf.cechFinrank_zero, OModulePresheaf.cechFinrank_succ, pow_zero, one_mul]
  ring

end S_AlgebraicGeometry_OModulePresheaf_exists_forall_eulerChar_baseChange_eq_of_locallyTrivial_of_isLocalRing
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_eulerChar_baseChange_eq_of_locallyTrivial_of_isLocalRing (solution)
