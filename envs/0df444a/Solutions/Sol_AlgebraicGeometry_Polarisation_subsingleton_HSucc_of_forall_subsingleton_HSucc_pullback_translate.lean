-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.subsingleton_HSucc_of_forall_subsingleton_HSucc_pullback_translate
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/acfb95b2-4b67-572d-aaf7-fd8b04a108d6

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_translate_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_HSucc_of_forall_subsingleton_HSucc_pullback_translate
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec"
p2m_attr_erase "simp" "DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (h : ∀ (𝒰 : A.OrderedAffineCover) (i : ℕ),
      Subsingleton ((OModulePresheaf.ofModules f ((Scheme.Modules.pullback (L.translate x)).obj 𝓜)).HSucc 𝒰 i))
    (𝒰 : A.OrderedAffineCover) (i : ℕ) :
    Subsingleton ((OModulePresheaf.ofModules f 𝓜).HSucc 𝒰 i) := by
  classical
  haveI : IsProper f := hA.proper

  have hT : L.translate x ≫ f = f := L.translate_over x
  haveI : IsIso (L.translate x) := by
    refine ⟨⟨L.translate (L.inv (𝟙 _) x), ?_, ?_⟩⟩
    · rw [← L.translate_mul, L.mul_inv_cancel, L.translate_one]
    · rw [← L.translate_mul, L.inv_mul_cancel, L.translate_one]

  have hfin : (OModulePresheaf.ofModules f 𝓜).CechFinite 𝒰 :=
    AlgebraicGeometry.OModulePresheaf.cechFinite_ofModules_of_locallyTrivial f 𝓜 h𝓜.exists_trivialization 𝒰
  have hfin' : (OModulePresheaf.ofModules f ((Scheme.Modules.pullback (L.translate x)).obj 𝓜)).CechFinite 𝒰 :=
    AlgebraicGeometry.OModulePresheaf.cechFinite_ofModules_of_locallyTrivial f _ (h𝓜.pullback _).exists_trivialization 𝒰
  haveI : Module.Finite k ((OModulePresheaf.ofModules f 𝓜).HSucc 𝒰 i) := hfin.2 i
  haveI : Module.Finite k ((OModulePresheaf.ofModules f ((Scheme.Modules.pullback (L.translate x)).obj 𝓜)).HSucc 𝒰 i) :=
    hfin'.2 i

  have hrk := AlgebraicGeometry.OModulePresheaf.cechFinrank_ofModules_pullback_eq_of_isIso f (L.translate x) 𝓜 h𝓜 𝒰 𝒰 (i + 1)
  have htransport : ∀ (g : A ⟶ Spec (CommRingCat.of k)) (hg : g = f) (N : A.Modules),
      (OModulePresheaf.ofModules g N).cechFinrank 𝒰 (i + 1) = (OModulePresheaf.ofModules f N).cechFinrank 𝒰 (i + 1) := by
    rintro g rfl N; rfl
  rw [htransport _ hT, OModulePresheaf.cechFinrank_succ, OModulePresheaf.cechFinrank_succ] at hrk
  have h0 : Module.finrank k ((OModulePresheaf.ofModules f ((Scheme.Modules.pullback (L.translate x)).obj 𝓜)).HSucc 𝒰 i) = 0 :=
    haveI := h 𝒰 i; Module.finrank_zero_of_subsingleton
  rw [h0] at hrk
  exact Module.finrank_zero_iff.mp hrk.symm

end S_AlgebraicGeometry_Polarisation_subsingleton_HSucc_of_forall_subsingleton_HSucc_pullback_translate
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_HSucc_of_forall_subsingleton_HSucc_pullback_translate (solution)
