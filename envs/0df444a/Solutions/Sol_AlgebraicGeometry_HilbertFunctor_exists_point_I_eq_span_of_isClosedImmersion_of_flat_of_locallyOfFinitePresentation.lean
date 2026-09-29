-- Prove2me | solution 1 for AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/3bdf0276-ce12-53ce-86c5-69f66912b9e0

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_point_hilbertFunctionOf
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_fg_subalgebra_isClosedImmersion_flat_isPullback_comp_map_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_isClosedImmersion_isPullback_comp_eq_map
import Theorems.Thm_AlgebraicGeometry_ProjSpace_flat_cochain_twist_and_subsingleton_cochain_of_flat
import Theorems.Thm_AlgebraicGeometry_ProjSpace_finite_H0_twist_and_finite_HSucc_twist_of_isClosedImmersion
import Theorems.Thm_Module_Flat_exists_forall_isUnit_projective_ker_baseChange_of_ker_baseChange_residueField_le_range
import Theorems.Thm_AlgebraicGeometry_ProjSpace_ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_forall_surjective_of_forall_projective
import Theorems.Thm_Module_ker_baseChange_le_range_and_finrank_eq_of_field_extension
import Theorems.Thm_Module_exists_forall_isUnit_surjective_baseChange_of_surjective_baseChange_residueField
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_comp_and_comp_eq_map_of_isScalarTower
import Theorems.Thm_Module_finite_projective_ker_baseChange_of_forall_exists_isUnit
import Theorems.Thm_AlgebraicGeometry_ProjSpace_finite_projective_H0_twist_of_ker_baseChange_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct AlgebraicGeometry.HilbertFunctor

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace PointDescentAssembly

universe u

theorem res_top_mem_H0 {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) (g : F.obj ⊤) :
    (fun s : K.Idx 0 => F.res (le_top : K.inter s ≤ ⊤) g) ∈ F.H0 K := by
  rw [LinearMap.mem_ker]
  funext s
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two, Pi.zero_apply]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, F.res_res]
  exact add_neg_cancel _

variable {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}

theorem exists_theta (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsClosedImmersion ι] (d : ℕ) :
    ∃ Θ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A d) →ₗ[A] (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback ι) 0,
      (∀ (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d) (s : (ProjSpace.stdCoverPullback ι).Idx 0) (i : Fin (n + 1)),
        (Θ ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ s).val i =
          ProjSpace.restrictFun
            (inf_le_right : (ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι i ≤ ProjSpace.pullbackChart ι i)
            ((ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)))
                (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)
                  (HomogeneousLocalization.mk
                    { deg := d
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                      den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                        (MvPolynomial.isHomogeneous_X_pow i d)⟩
                      den_mem := ⟨d, rfl⟩ })))) ∧
      (∀ x, Θ x ∈ (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).H0 (ProjSpace.stdCoverPullback ι)) := by
  obtain ⟨θ, hθ, -⟩ :=
    AlgebraicGeometry.ProjSpace.exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq (k := A) (n := n) ι d
  let ψ : ∀ s : (ProjSpace.stdCoverPullback ι).Idx 0, ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A d) →ₗ[A]
      (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).obj ((ProjSpace.stdCoverPullback ι).inter s) :=
    fun s => (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).res (le_top : (ProjSpace.stdCoverPullback ι).inter s ≤ ⊤) ∘ₗ θ
  refine ⟨{ toFun := fun x s => ψ s x,
            map_add' := fun x y => funext fun s => (ψ s).map_add x y,
            map_smul' := fun a x => funext fun s => (ψ s).map_smul a x }, ?_, ?_⟩
  · intro F hF s i
    show ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).res (le_top : (ProjSpace.stdCoverPullback ι).inter s ≤ ⊤)
      (θ ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩)).val i = _
    rw [ProjSpace.twist_res_val]
    exact (congrArg _ (hθ F hF i)).trans (ProjSpace.restrictFun_restrictFun _ _ _)
  · intro x
    exact res_top_mem_H0 (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d) (ProjSpace.stdCoverPullback ι) (θ x)

def vertex₀ (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsClosedImmersion ι] (i : Fin (n + 1)) :
    (ProjSpace.stdCoverPullback ι).Idx 0 :=
  ⟨fun _ => ULift.up i, fun a b hab => absurd (Fin.lt_def.mp hab) (by have := a.isLt; have := b.isLt; omega)⟩

theorem pullbackChart_le_inter_vertex₀ (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsClosedImmersion ι]
    (i : Fin (n + 1)) :
    ProjSpace.pullbackChart ι i ≤ (ProjSpace.stdCoverPullback ι).inter (vertex₀ ι i) ⊓ ProjSpace.pullbackChart ι i :=
  le_inf (le_iInf fun _ => le_rfl) le_rfl

theorem theta_eq_zero_iff (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsClosedImmersion ι] (d : ℕ)
    (Θ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A d) →ₗ[A] (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback ι) 0)
    (hΘ : ∀ (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d) (s : (ProjSpace.stdCoverPullback ι).Idx 0) (i : Fin (n + 1)),
      (Θ ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ s).val i =
        ProjSpace.restrictFun
          (inf_le_right : (ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι i ≤ ProjSpace.pullbackChart ι i)
          ((ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)))
                (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)
                  (HomogeneousLocalization.mk
                    { deg := d
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                      den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                        (MvPolynomial.isHomogeneous_X_pow i d)⟩
                      den_mem := ⟨d, rfl⟩ }))))
    (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d) :
    Θ ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ = 0 ↔
      ∀ i : Fin (n + 1), ((ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)))
                (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)
                  (HomogeneousLocalization.mk
                    { deg := d
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                      den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                        (MvPolynomial.isHomogeneous_X_pow i d)⟩
                      den_mem := ⟨d, rfl⟩ }))) = 0 := by
  constructor
  · intro hz i

    have h1 := hΘ F hF (vertex₀ ι i) i
    rw [hz] at h1
    have h2 : ProjSpace.restrictFun
        (inf_le_right : (ProjSpace.stdCoverPullback ι).inter (vertex₀ ι i) ⊓ ProjSpace.pullbackChart ι i ≤
          ProjSpace.pullbackChart ι i)
        ((ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)))
          (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)
            (HomogeneousLocalization.mk
              { deg := d
                num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                  (MvPolynomial.isHomogeneous_X_pow i d)⟩
                den_mem := ⟨d, rfl⟩ }))) = 0 := by
      rw [← h1]; rfl

    have h3 : ∀ x : Γ(Z, ProjSpace.pullbackChart ι i),
        x = ProjSpace.restrictFun (pullbackChart_le_inter_vertex₀ ι i)
          (ProjSpace.restrictFun
            (inf_le_right : (ProjSpace.stdCoverPullback ι).inter (vertex₀ ι i) ⊓ ProjSpace.pullbackChart ι i ≤
              ProjSpace.pullbackChart ι i) x) := by
      intro x
      rw [ProjSpace.restrictFun_restrictFun]
      exact (ProjSpace.restrictFun_refl x).symm
    rw [h3 ((ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)))
          (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)
            (HomogeneousLocalization.mk
              { deg := d
                num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                  (MvPolynomial.isHomogeneous_X_pow i d)⟩
                den_mem := ⟨d, rfl⟩ }))), h2, map_zero]
    rfl
  · intro h
    funext s
    refine ProjSpace.twistObj.ext (funext fun i => ?_)
    rw [hΘ F hF s i, h i]
    refine (map_zero _).trans ?_
    rfl

theorem chart_vanish_mul (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) (d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d)
    (e : ℕ) (G : MvPolynomial (Fin (n + 1)) A) (hG : G.IsHomogeneous e)
    (h0 : ∀ i : Fin (n + 1), ((ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)))
                (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)
                  (HomogeneousLocalization.mk
                    { deg := d
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                      den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                        (MvPolynomial.isHomogeneous_X_pow i d)⟩
                      den_mem := ⟨d, rfl⟩ }))) = 0) :
    ∀ i : Fin (n + 1), ((ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)))
                (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)
                  (HomogeneousLocalization.mk
                    { deg := (e + d)
                      num := ⟨(G * F), (MvPolynomial.mem_homogeneousSubmodule (e + d) (G * F)).mpr (hG.mul hF)⟩
                      den := ⟨MvPolynomial.X i ^ (e + d), (MvPolynomial.mem_homogeneousSubmodule (e + d) _).mpr
                        (MvPolynomial.isHomogeneous_X_pow i (e + d))⟩
                      den_mem := ⟨(e + d), rfl⟩ }))) = 0 := by
  intro i
  have hmk :
      (HomogeneousLocalization.mk
          { deg := (e + d)
            num := ⟨(G * F), (MvPolynomial.mem_homogeneousSubmodule (e + d) (G * F)).mpr (hG.mul hF)⟩
            den := ⟨MvPolynomial.X i ^ (e + d), (MvPolynomial.mem_homogeneousSubmodule (e + d) _).mpr
              (MvPolynomial.isHomogeneous_X_pow i (e + d))⟩
            den_mem := ⟨(e + d), rfl⟩ } :
        HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)) =
      (HomogeneousLocalization.mk
          { deg := e
            num := ⟨G, (MvPolynomial.mem_homogeneousSubmodule e G).mpr hG⟩
            den := ⟨MvPolynomial.X i ^ e, (MvPolynomial.mem_homogeneousSubmodule e _).mpr
              (MvPolynomial.isHomogeneous_X_pow i e)⟩
            den_mem := ⟨e, rfl⟩ } : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)) *
        (HomogeneousLocalization.mk
          { deg := d
            num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
            den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
              (MvPolynomial.isHomogeneous_X_pow i d)⟩
            den_mem := ⟨d, rfl⟩ } : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)) := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk,
      HomogeneousLocalization.val_mk, Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp [pow_add]⟩
  rw [hmk, map_mul, map_mul, h0 i, mul_zero]

theorem exists_theta_eq_of_forall_H0 (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsClosedImmersion ι] (d : ℕ)
    (Θ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A d) →ₗ[A] (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback ι) 0)
    (hΘ : ∀ (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d) (s : (ProjSpace.stdCoverPullback ι).Idx 0) (i : Fin (n + 1)),
      (Θ ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ s).val i =
        ProjSpace.restrictFun
          (inf_le_right : (ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι i ≤ ProjSpace.pullbackChart ι i)
          ((ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)))
                (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)
                  (HomogeneousLocalization.mk
                    { deg := d
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                      den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                        (MvPolynomial.isHomogeneous_X_pow i d)⟩
                      den_mem := ⟨d, rfl⟩ }))))
    (hb : (∀ c ∈ (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).H0 (ProjSpace.stdCoverPullback ι),
          ∃ (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
            ∀ (s : (ProjSpace.stdCoverPullback ι).Idx 0) (i : Fin (n + 1)),
              (c s).val i =
                ProjSpace.restrictFun
                  (inf_le_right : (ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι i ≤ ProjSpace.pullbackChart ι i)
                  ((ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)))
                (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X i)
                  (HomogeneousLocalization.mk
                    { deg := d
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                      den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                        (MvPolynomial.isHomogeneous_X_pow i d)⟩
                      den_mem := ⟨d, rfl⟩ })))))
    (c : (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback ι) 0) (hc : c ∈ (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).H0 (ProjSpace.stdCoverPullback ι)) :
    ∃ x : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A d), Θ x = c := by
  obtain ⟨F, hF, hcF⟩ := hb c hc
  refine ⟨⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩, ?_⟩
  funext s
  refine ProjSpace.twistObj.ext (funext fun i => ?_)
  rw [hΘ F hF s i, hcF s i]

set_option maxHeartbeats 1600000 in
theorem local_data {A : Type} [CommRing A] {n : ℕ} {Z : Scheme.{0}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsClosedImmersion ι]
    (A₀ : Type) [CommRing A₀] [IsNoetherianRing A₀] [Algebra A₀ A] {Z₀ : Scheme.{0}}
    (ι₀ : Z₀ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A₀)) [IsClosedImmersion ι₀]
    (hfl₀ : Flat (ι₀ ≫ ProjSpace.π A₀ n))
    (g : Z ⟶ Z₀)
    (hpb₀ : IsPullback g (ι ≫ ProjSpace.π A n) (ι₀ ≫ ProjSpace.π A₀ n) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))
    (hcomp₀ : g ≫ ι₀ = ι ≫ ProjSpace.map A₀ A n)
    (h : ℕ → ℕ) (m d : ℕ) (hd : m ≤ d)
    (Θ₀ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A₀ d) →ₗ[A₀] (ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).cochain (ProjSpace.stdCoverPullback ι₀) 0)
    (hΘ₀ : ∀ (F : MvPolynomial (Fin (n + 1)) A₀) (hF : F.IsHomogeneous d) (s : (ProjSpace.stdCoverPullback ι₀).Idx 0) (i : Fin (n + 1)),
      (Θ₀ ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ s).val i =
        ProjSpace.restrictFun
          (inf_le_right : (ProjSpace.stdCoverPullback ι₀).inter s ⊓ ProjSpace.pullbackChart ι₀ i ≤ ProjSpace.pullbackChart ι₀ i)
          ((ι₀.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A₀) (MvPolynomial.X i)))
                (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A₀) (MvPolynomial.X i)
                  (HomogeneousLocalization.mk
                    { deg := d
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                      den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                        (MvPolynomial.isHomogeneous_X_pow i d)⟩
                      den_mem := ⟨d, rfl⟩ }))))
    (hΘ₀ker : ∀ x, Θ₀ x ∈ (ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).H0 (ProjSpace.stdCoverPullback ι₀))
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra A k]
        (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) (e : Zk ⟶ Z),
        IsClosedImmersion ιk →
        IsPullback e (ιk ≫ ProjSpace.π k n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom (algebraMap A k))) →
        e ≫ ι = ιk ≫ ProjSpace.map A k n →
        ∃ q : Point k n h, (∀ (d' : ℕ), m ≤ d' → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d'),
          (F ∈ q.I ↔ ∀ i : Fin (n + 1), ((ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
                (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                  (HomogeneousLocalization.mk
                    { deg := d'
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d' F).mpr hF⟩
                      den := ⟨MvPolynomial.X i ^ d', (MvPolynomial.mem_homogeneousSubmodule d' _).mpr
                        (MvPolynomial.isHomogeneous_X_pow i d')⟩
                      den_mem := ⟨d', rfl⟩ }))) = 0)))
    (hREG : ∀ (k : Type) [Field k] (Zk : Scheme.{0})
        (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ιk] (q : Point k n h),
        (∀ (d' : ℕ), m ≤ d' → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d'),
          (F ∈ q.I ↔ ∀ i : Fin (n + 1), ((ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
                (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                  (HomogeneousLocalization.mk
                    { deg := d'
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d' F).mpr hF⟩
                      den := ⟨MvPolynomial.X i ^ d', (MvPolynomial.mem_homogeneousSubmodule d' _).mpr
                        (MvPolynomial.isHomogeneous_X_pow i d')⟩
                      den_mem := ⟨d', rfl⟩ }))) = 0)) →
        ∀ d' : ℕ, m ≤ d' → (∀ i : ℕ, Subsingleton ((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d').HSucc (ProjSpace.stdCoverPullback ιk) i)) ∧ (∀ c ∈ (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d').H0 (ProjSpace.stdCoverPullback ιk),
          ∃ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d'),
            ∀ (s : (ProjSpace.stdCoverPullback ιk).Idx 0) (i : Fin (n + 1)),
              (c s).val i =
                ProjSpace.restrictFun
                  (inf_le_right : (ProjSpace.stdCoverPullback ιk).inter s ⊓ ProjSpace.pullbackChart ιk i ≤ ProjSpace.pullbackChart ιk i)
                  ((ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
                (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                  (HomogeneousLocalization.mk
                    { deg := d'
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d' F).mpr hF⟩
                      den := ⟨MvPolynomial.X i ^ d', (MvPolynomial.mem_homogeneousSubmodule d' _).mpr
                        (MvPolynomial.isHomogeneous_X_pow i d')⟩
                      den_mem := ⟨d', rfl⟩ })))))
    (𝔮 : PrimeSpectrum A) (𝔭₀ : PrimeSpectrum A₀) (h𝔭₀ : 𝔭₀ = PrimeSpectrum.comap (algebraMap A₀ A) 𝔮)
    (kb : Type) [Field kb] [IsAlgClosed kb] [Algebra A kb] [Algebra A₀ kb]
    (hST : ∀ x : A₀, algebraMap A kb (algebraMap A₀ A x) = algebraMap A₀ kb x)
    [Algebra 𝔭₀.asIdeal.ResidueField kb]
    (hST' : ∀ x : A₀, algebraMap 𝔭₀.asIdeal.ResidueField kb (algebraMap A₀ 𝔭₀.asIdeal.ResidueField x) =
      algebraMap A₀ kb x) :
    ∃ g₀ : A₀, algebraMap A₀ A g₀ ∉ 𝔮.asIdeal ∧
      ∀ (A' : Type) [CommRing A'] [Algebra A₀ A'], IsUnit (algebraMap A₀ A' g₀) →
        Module.Finite A' (LinearMap.ker (((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) 0).baseChange A')) ∧
        Module.Projective A' (LinearMap.ker (((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) 0).baseChange A')) ∧
        (∀ 𝔮' : PrimeSpectrum A', Module.rankAtStalk
          (LinearMap.ker (((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) 0).baseChange A')) 𝔮' = h d) ∧
        LinearMap.ker (((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) 0).baseChange A') ≤ LinearMap.range (Θ₀.baseChange A') := by
  classical
  haveI := IsScalarTower.of_algebraMap_eq (R := A₀) (S := A) (A := kb) fun x => (hST x).symm
  haveI := IsScalarTower.of_algebraMap_eq (R := A₀) (S := 𝔭₀.asIdeal.ResidueField) (A := kb) fun x => (hST' x).symm
  have h8 := AlgebraicGeometry.ProjSpace.exists_isClosedImmersion_isPullback_comp_eq_map ι kb
  obtain ⟨Zk, ιk, hclk, e, hpb, hcomp⟩ := h8
  haveI := hclk
  have hfq := hfib kb Zk ιk e hclk hpb hcomp
  obtain ⟨q, hq⟩ := hfq
  have hreg := hREG kb Zk ιk q hq d hd
  have hG := AlgebraicGeometry.ProjSpace.isPullback_comp_and_comp_eq_map_of_isScalarTower A kb ι₀ ι ιk g e hpb₀ hcomp₀ hpb hcomp
  obtain ⟨hpb', hcomp'⟩ := hG
  have hC := AlgebraicGeometry.ProjSpace.ker_baseChange_le_range_and_finrank_ker_eq_of_point_of_isPullback ι₀ kb ιk (e ≫ g) hpb' hcomp' d Θ₀ hΘ₀ h q (hq d hd) hreg.1 hreg.2
  have hE := Module.ker_baseChange_le_range_and_finrank_eq_of_field_extension
    (fun i => (ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).cochain (ProjSpace.stdCoverPullback ι₀) i)
    (fun i => (ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) i) Θ₀ 𝔭₀.asIdeal.ResidueField kb (h d) hC.1 hC.2.1 hC.2.2
  obtain ⟨hE1, hE2, hE3⟩ := hE

  have hA1 := AlgebraicGeometry.ProjSpace.flat_cochain_twist_and_subsingleton_cochain_of_flat ι₀ hfl₀ d
  have hA2 := AlgebraicGeometry.ProjSpace.finite_H0_twist_and_finite_HSucc_twist_of_isClosedImmersion ι₀ d
  haveI : ∀ i : ℕ, Module.Flat A₀ ((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).cochain (ProjSpace.stdCoverPullback ι₀) i) := hA1.1

  have hB := Module.Flat.exists_forall_isUnit_projective_ker_baseChange_of_ker_baseChange_residueField_le_range
    (fun i => (ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).cochain (ProjSpace.stdCoverPullback ι₀) i)
    (fun i => (ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) i)
    (fun i => AlgebraicGeometry.OModulePresheaf.d_comp_d (ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d) (ProjSpace.stdCoverPullback ι₀) i)
    (n + 1) hA1.2 hA2.1 hA2.2 𝔭₀ hE1
  obtain ⟨g₁, hg₁, H₁⟩ := hB

  let Θ' : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A₀ d) →ₗ[A₀]
      ↥(LinearMap.ker ((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) 0)) :=
    LinearMap.codRestrict _ Θ₀ hΘ₀ker
  have hΘ' : (LinearMap.ker ((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) 0)).subtype ∘ₗ Θ' = Θ₀ := LinearMap.subtype_comp_codRestrict _ _ _
  have hunitκ : IsUnit (algebraMap A₀ 𝔭₀.asIdeal.ResidueField g₁) := by
    rw [isUnit_iff_ne_zero, ne_eq, Ideal.algebraMap_residueField_eq_zero]; exact hg₁
  obtain ⟨-, -, -, hbijκ, -⟩ := H₁ 𝔭₀.asIdeal.ResidueField hunitκ
  have hsurjκ : Function.Surjective (Θ'.baseChange 𝔭₀.asIdeal.ResidueField) := by
    intro y
    obtain ⟨w, hw⟩ := hE2 (TwoChartCech.kerBaseChangeHom ((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) 0) 𝔭₀.asIdeal.ResidueField y).2
    refine ⟨w, hbijκ.1 ?_⟩
    apply Subtype.ext
    rw [TwoChartCech.kerBaseChangeHom_apply_coe, TwoChartCech.kerBaseChangeHom_apply_coe,
      ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hΘ', hw, TwoChartCech.kerBaseChangeHom_apply_coe]
  haveI : Module.Finite A₀ ↥(LinearMap.ker ((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) 0)) := hA2.1
  have hF := Module.exists_forall_isUnit_surjective_baseChange_of_surjective_baseChange_residueField Θ' 𝔭₀ hsurjκ
  obtain ⟨g₂, hg₂, H₂⟩ := hF

  refine ⟨g₁ * g₂, ?_, ?_⟩
  · rw [h𝔭₀] at hg₁ hg₂
    intro hmem
    rw [map_mul] at hmem
    rcases 𝔮.isPrime.mem_or_mem hmem with h1 | h2
    · exact hg₁ h1
    · exact hg₂ h2
  intro A' _ _ hunit
  rw [map_mul] at hunit
  obtain ⟨hfinA, hprojA, -, hbijA, hrankA⟩ := H₁ A' (isUnit_of_mul_isUnit_left hunit)
  have hsurjA := H₂ A' (isUnit_of_mul_isUnit_right hunit)
  refine ⟨hfinA, hprojA, fun 𝔮' => (hrankA 𝔮').trans hE3, ?_⟩
  intro x hx
  obtain ⟨y, hy⟩ := hbijA.2 ⟨x, hx⟩
  obtain ⟨w, hw⟩ := hsurjA y
  refine ⟨w, ?_⟩
  have := congrArg (fun t => (TwoChartCech.kerBaseChangeHom ((ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) 0) A' t : A' ⊗[A₀] (ProjSpace.twist (ι₀ ≫ ProjSpace.π A₀ n) ι₀ d).cochain (ProjSpace.stdCoverPullback ι₀) 0)) hw
  rw [hy, TwoChartCech.kerBaseChangeHom_apply_coe, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hΘ'] at this
  exact this

end PointDescentAssembly

open PointDescentAssembly in
set_option maxHeartbeats 3200000 in
theorem solution
    (n : ℕ) (P : Polynomial ℚ)
    (hP : ∃ (K : Type) (_ : Field K) (I : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → (Module.finrank K (piece I d) : ℚ) = P.eval (d : ℚ)) :
    ∃ D₀ : ℕ, ∀ m : ℕ, D₀ ≤ m → ∀ (A : Type) [CommRing A] (Z : Scheme.{0})
      (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)),
      IsClosedImmersion ι → Flat (ι ≫ ProjSpace.π A n) → LocallyOfFinitePresentation (ι ≫ ProjSpace.π A n) →
      (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra A k]
          (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) (e : Zk ⟶ Z),
          IsClosedImmersion ιk →
          IsPullback e (ιk ≫ ProjSpace.π k n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom (algebraMap A k))) →
          e ≫ ι = ιk ≫ ProjSpace.map A k n →
          ∃ q : Point k n (hilbertFunctionOf n P m), ∀ (d : ℕ), m ≤ d →
            ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
              (F ∈ q.I ↔ ∀ i : Fin (n + 1),
            ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (X i))
              ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (X i))
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })) = 0)) →
      ∃ p : Point A n (hilbertFunctionOf n P m),
        p.I = Ideal.span { F : MvPolynomial (Fin (n + 1)) A | ∃ (d : ℕ) (hF : F.IsHomogeneous d), m ≤ d ∧
          ∀ i : Fin (n + 1),
            ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
              ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })) = 0 } := by
  classical
  obtain ⟨D₀, hREG⟩ :=
    AlgebraicGeometry.HilbertFunctor.exists_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_point_hilbertFunctionOf n P hP
  refine ⟨D₀, fun m hm A _ Z ι hcl hfl hlfp hfib => ?_⟩
  haveI := hcl

  obtain ⟨A₀, hA₀, Z₀, ι₀, g, hcl₀, hfl₀, hlfp₀, hpb₀, hcomp₀⟩ :=
    AlgebraicGeometry.ProjSpace.exists_fg_subalgebra_isClosedImmersion_flat_isPullback_comp_map_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation n Z ι hcl hfl hlfp
  haveI := hcl₀
  haveI : IsNoetherianRing ↥A₀ := by
    haveI : Algebra.FiniteType ℤ ↥A₀ := ⟨(Subalgebra.fg_top A₀).mpr hA₀⟩
    exact Algebra.FiniteType.isNoetherianRing ℤ ↥A₀

  choose Θ₀ hΘ₀ hΘ₀ker using fun d => exists_theta (A := ↥A₀) ι₀ d
  choose Θ hΘ hΘker using fun d => exists_theta (A := A) ι d

  have hH : ∀ d : ℕ, m ≤ d →
      Module.Finite A (LinearMap.ker (((ProjSpace.twist (ι₀ ≫ ProjSpace.π ↥A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) 0).baseChange A)) ∧
      Module.Projective A (LinearMap.ker (((ProjSpace.twist (ι₀ ≫ ProjSpace.π ↥A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) 0).baseChange A)) ∧
      (∀ 𝔮 : PrimeSpectrum A, Module.rankAtStalk
        (LinearMap.ker (((ProjSpace.twist (ι₀ ≫ ProjSpace.π ↥A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) 0).baseChange A)) 𝔮 = hilbertFunctionOf n P m d) ∧
      LinearMap.ker (((ProjSpace.twist (ι₀ ≫ ProjSpace.π ↥A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) 0).baseChange A) ≤ LinearMap.range ((Θ₀ d).baseChange A) := by
    intro d hd
    refine Module.finite_projective_ker_baseChange_of_forall_exists_isUnit A (((ProjSpace.twist (ι₀ ≫ ProjSpace.π ↥A₀ n) ι₀ d).d (ProjSpace.stdCoverPullback ι₀) 0)) (Θ₀ d) (hilbertFunctionOf n P m d) (fun 𝔮 => ?_)

    letI algκ : Algebra (PrimeSpectrum.comap (algebraMap (↥A₀) A) 𝔮).asIdeal.ResidueField
        (AlgebraicClosure 𝔮.asIdeal.ResidueField) :=
      ((algebraMap 𝔮.asIdeal.ResidueField (AlgebraicClosure 𝔮.asIdeal.ResidueField)).comp
        (Ideal.ResidueField.map (PrimeSpectrum.comap (algebraMap (↥A₀) A) 𝔮).asIdeal 𝔮.asIdeal
          (algebraMap (↥A₀) A) rfl)).toAlgebra
    exact local_data ι (↥A₀) ι₀ hfl₀ g hpb₀ hcomp₀ (hilbertFunctionOf n P m) m d hd (Θ₀ d) (hΘ₀ d) (hΘ₀ker d)
      hfib (hREG m hm) 𝔮 (PrimeSpectrum.comap (algebraMap (↥A₀) A) 𝔮) rfl
      (AlgebraicClosure 𝔮.asIdeal.ResidueField)
      (fun x => (IsScalarTower.algebraMap_apply (↥A₀) A (AlgebraicClosure 𝔮.asIdeal.ResidueField) x).symm)
      (fun x => by
        rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
        exact (IsScalarTower.algebraMap_apply (↥A₀) 𝔮.asIdeal.ResidueField
          (AlgebraicClosure 𝔮.asIdeal.ResidueField) x).symm)

  have hI := fun d (hd : m ≤ d) =>
    AlgebraicGeometry.ProjSpace.finite_projective_H0_twist_of_ker_baseChange_of_isPullback ι₀ A ι g hpb₀ hcomp₀ d (Θ₀ d) (hΘ₀ d)
      (hilbertFunctionOf n P m d) (hH d hd).1 (hH d hd).2.1 (hH d hd).2.2.1 (hH d hd).2.2.2

  let ΘZ : ∀ d : ℕ, ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A d) →ₗ[A] ↥((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).H0 (ProjSpace.stdCoverPullback ι)) :=
    fun d => LinearMap.codRestrict _ (Θ d) (hΘker d)
  obtain ⟨p, hp⟩ := AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_span_of_forall_surjective_of_forall_projective n m A (hilbertFunctionOf n P m)
    (fun d hdm => by simp [hilbertFunctionOf, hdm])
    (fun d => ↥((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).H0 (ProjSpace.stdCoverPullback ι))) ΘZ
    (fun d hd => (hI d hd).1) (fun d hd => (hI d hd).2.1) (fun d hd => (hI d hd).2.2.1)
    (fun d hd => fun y => by
      obtain ⟨x, hx⟩ := exists_theta_eq_of_forall_H0 ι d (Θ d) (hΘ d) (hI d hd).2.2.2 y.1 y.2
      exact ⟨x, Subtype.ext hx⟩)
    (fun d hd F hF e G hG hzero => by
      apply Subtype.ext
      have hF0 : Θ d ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ = 0 := congrArg Subtype.val hzero
      exact (theta_eq_zero_iff ι (e + d) (Θ (e + d)) (hΘ (e + d)) (G * F) (hG.mul hF)).mpr
        (chart_vanish_mul ι d F hF e G hG ((theta_eq_zero_iff ι d (Θ d) (hΘ d) F hF).mp hF0)))
  refine ⟨p, ?_⟩
  rw [hp]
  congr 1
  ext F
  simp only [Set.mem_setOf_eq]
  refine exists_congr fun d => exists_congr fun hF => and_congr_right fun _ => ?_
  exact (Iff.intro (fun h => congrArg Subtype.val h) (fun h => Subtype.ext h)).trans
    (theta_eq_zero_iff ι d (Θ d) (hΘ d) F hF)

end
end S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation
end P2MW
export P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation (solution)
