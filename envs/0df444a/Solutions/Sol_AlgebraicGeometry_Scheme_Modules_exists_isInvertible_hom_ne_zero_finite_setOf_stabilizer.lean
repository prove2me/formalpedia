-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_isInvertible_hom_ne_zero_finite_setOf_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/b9aaebde-215d-54f8-bdac-5d8c6168fb1c

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullbackSection_eq_zero_iff_notMem_of_isAffineOpen
import Theorems.Thm_AlgebraicGeometry_Scheme_finite_setOf_forall_mem_iff_mul_mem_of_isClosed_of_compl_subset_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_hom_ne_zero_finite_setOf_stabilizer
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

open scoped CategoryTheory.MonObj

namespace P2mThetaFin

variable {X : Scheme.{u}}

lemma pullbackSection_zero {X' : Scheme.{u}} (F : X' ⟶ X) (M : X.Modules) :
    Scheme.Modules.pullbackSection F (0 : 𝟙_ X.Modules ⟶ M) = 0 := by
  have h : (Scheme.Modules.pullback F).map (0 : (𝟙_ X.Modules) ⟶ M) = 0 := Functor.map_zero _ _ _
  exact (congrArg ((Scheme.Modules.pullbackUnitIso F).inv ≫ ·) h).trans comp_zero

end P2mThetaFin

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [IsProper t] [IsIntegral X] [GrpObj (Over.mk t)] (hsm : Smooth t) :
    ∃ (L : X.Modules) (_ : Scheme.Modules.IsInvertible L) (θ : 𝟙_ X.Modules ⟶ L), θ ≠ 0 ∧
      Set.Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t |
        ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
          Scheme.Modules.pullbackSection z.left θ = 0 ↔ Scheme.Modules.pullbackSection (z * x).left θ = 0} := by

  set e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t := 1 with he_def
  obtain ⟨_, ⟨U, hU, rfl⟩, heU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((e.left : Spec (CommRingCat.of k) ⟶ X) (IsLocalRing.closedPoint k))) isOpen_univ

  obtain ⟨L, hL, θ, hθ⟩ :=
    Scheme.Modules.exists_isInvertible_pullbackSection_eq_zero_iff_notMem_of_isAffineOpen k t U hU
  refine ⟨L, hL, θ, ?_, ?_⟩
  ·
    rintro rfl
    exact ((hθ k e.left).1 (P2mThetaFin.pullbackSection_zero _ L)) heU
  ·
    have hfin :=
      Scheme.finite_setOf_forall_mem_iff_mul_mem_of_isClosed_of_compl_subset_of_isAffineOpen k t
        ((U : Set X)ᶜ) U.isOpen.isClosed_compl U hU (by rw [compl_compl]) (fun h => h heU)
    have hset : {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t |
        ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
          Scheme.Modules.pullbackSection z.left θ = 0 ↔
            Scheme.Modules.pullbackSection (z * x).left θ = 0} =
        {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t |
          ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
            z.left (IsLocalRing.closedPoint k) ∈ (U : Set X)ᶜ ↔
              (z * x).left (IsLocalRing.closedPoint k) ∈ (U : Set X)ᶜ} := by
      ext x
      refine forall_congr' fun z => ?_
      exact iff_congr (hθ k z.left) (hθ k (z * x).left)
    rw [hset]
    exact hfin

end S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_hom_ne_zero_finite_setOf_stabilizer
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_hom_ne_zero_finite_setOf_stabilizer (solution)
