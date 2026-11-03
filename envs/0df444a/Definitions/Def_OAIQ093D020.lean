-- Prove2me | Definitions.Def_OAIQ093D020
-- name    : OAIQ093D020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-02T18:24:00.222604+00:00
-- url     : https://prove2.me/theorems/b18a739d-c260-4e6e-8ffa-56963680961d
-- title:
--   Definitions bundle OAIQ093D020 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 96 declarations of OpenAI's Lean: 48 definitions, 4 inductive types or structures, 3 instances and 41 theorems. The definitions and types are `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData`, `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData`, `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.sourceCoordinates`, `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.sourceQuotientCell`, `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.sourceQuotientCoordinates`, `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.sourceSection`, `OAI.PolycyclicRecognition.JointFixedReductionData`, `OAI.PolycyclicRecognition.JointFixedReductionData.action`, `OAI.PolycyclicRecognition.JointFixedReductionData.lowerCentralLayer`, `OAI.PolycyclicRecognition.JointFixedReductionData.residualKernelLayer`, `OAI.PolycyclicRecognition.NilpotentKernelCompletion`, `OAI.PolycyclicRecognition.NilpotentKernelCompletion.extendedAction`, `OAI.PolycyclicRecognition.NilpotentKernelCompletion.extendedAutomorphism`, `OAI.PolycyclicRecognition.NilpotentKernelCompletion.of_equiv`, `OAI.PolycyclicRecognition.NilpotentKernelCompletion.of_polynomial_kernel`, `OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism`, `OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.completedExtensionLattice`, `OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.completedExtensionLatticeEquiv`, `OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.extensionEmbedding`, `OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.extensionFactorMap`, `OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.extensionFactorSystem`, `OAI.PolycyclicRecognition.booleanStepColimit`, `OAI.PolycyclicRecognition.derivationLieSpaceSplit`, `OAI.PolycyclicRecognition.derivationModelEquiv`, `OAI.PolycyclicRecognition.derivationNilpotentLieModel`, `OAI.PolycyclicRecognition.derivationSolvableLieModel`, `OAI.PolycyclicRecognition.innerCentralizerCentralProjection`, `OAI.PolycyclicRecognition.innerCentralizerFactorSystem`, `OAI.PolycyclicRecognition.innerCentralizerFixedProjection`, `OAI.PolycyclicRecognition.innerCentralizerGroupAction`, `OAI.PolycyclicRecognition.innerCentralizerLieSubalgebra`, `OAI.PolycyclicRecognition.innerCentralizerMovingGroupProjection`, `OAI.PolycyclicRecognition.innerCentralizerMovingInclusion`, `OAI.PolycyclicRecognition.integralRealHeight`, `OAI.PolycyclicRecognition.jointFixedExtensionEmbedding`, `OAI.PolycyclicRecognition.jointFixedFactorInclusion`, `OAI.PolycyclicRecognition.jointFixedFactorSystem`, `OAI.PolycyclicRecognition.jointFixedGroupAction`, `OAI.PolycyclicRecognition.jointFixedLieAction`, `OAI.PolycyclicRecognition.jointFixedLinearAction` and 12 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `PolycyclicRecognition_Algebra_InnerCentralizerFactorSystem`, `PolycyclicRecognition_Algebra_InnerCentralizerMembership`, `PolycyclicRecognition_Algebra_InnerCentralizerProduct`, `PolycyclicRecognition_Algebra_NilpotentExtensionEmbedding`, `PolycyclicRecognition_Algebra_NilpotentExtensionFactorSystem`, `PolycyclicRecognition_Algebra_PolynomialInnerLogarithm`, `PolycyclicRecognition_Algebra_PolynomialInnerUnipotence`, `PolycyclicRecognition_Algebra_ResidualLowerCentralLayers`, `PolycyclicRecognition_Algebra_SemisimpleCentralDecomposition`, `PolycyclicRecognition_Algebra_SemisimpleMovingAction`, `PolycyclicRecognition_Algebra_SemisimpleMovingLang`, `PolycyclicRecognition_Algebra_SmallCoefficientIdentityCycle`, `PolycyclicRecognition_Finiteness_BooleanStepProjective`, `PolycyclicRecognition_Finiteness_SmallCoefficientCompletedUnit`, `PolycyclicRecognition_Finiteness_SmallCoefficientRing`, `PolycyclicRecognition_Geometry_CartanPolarTiledSamplers`, `PolycyclicRecognition_Geometry_CartanTiledProbeChains`, `PolycyclicRecognition_Geometry_CartanTiledSourceCell`, `PolycyclicRecognition_Geometry_DerivationLieSpace`, `PolycyclicRecognition_Geometry_InnerCentralizerLieSubalgebra`, `PolycyclicRecognition_Geometry_PolynomialInnerAdjoint`, `PolycyclicRecognition_Geometry_SmoothPolynomialAutomorphisms`, `PolycyclicRecognition_Lattices_DerivationSolvableModel`, `PolycyclicRecognition_Lattices_JointFixedActionFiltration`, `PolycyclicRecognition_Lattices_JointFixedFactorSystem`, `PolycyclicRecognition_Lattices_JointFixedLayerAction`, `PolycyclicRecognition_Lattices_JointFixedReductionData`, `PolycyclicRecognition_Lattices_JointFixedSubalgebra`, `PolycyclicRecognition_Lattices_KernelCompletionAction`, `PolycyclicRecognition_Lattices_KernelCompletionHeight`, `PolycyclicRecognition_Lattices_KernelCompletionTransport`, `PolycyclicRecognition_Lattices_NilpotentExtensionLattice`, `PolycyclicRecognition_Lattices_NilpotentKernelCompletion`, `PolycyclicRecognition_Lattices_NilpotentLatticeAutomorphisms`, `PolycyclicRecognition_Lattices_NilpotentLatticeInnerAdjoint`.
--
--   **Imports.** It imports the published bundle `Def_PolycyclicRecognition`; the bundles `OAIQ093D016`, `OAIQ093D017` and `OAIQ093D018` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ093D021` and `OAIQ093D022`; the statements `OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.polar_offset_nonpos`, `OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.exists_canonical_polar_samplers`, `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.count_le_offset_rate`, `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.linked_chains_from_neighbor_boxes`, `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.measured_target_offset_nonpos`, `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.original_box_law_offset_nonpos`, `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.source_probability_data`, `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.source_section_rightInverse`, `OAI.PolycyclicRecognition.CartanWordModel.exists_normalized_polar_samplers`, `OAI_PolycyclicRecognition_CartanWordModel_exists_polar_flow_tiling` and `OAI.PolycyclicRecognition.CartanWordModel.exists_polar_tiled_probe_chains_from_box`; the proofs of `OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.polar_offset_nonpos`, `OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.exists_canonical_polar_samplers`, `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.count_le_offset_rate`, `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.linked_chains_from_neighbor_boxes`, `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.measured_target_offset_nonpos`, `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.source_probability_data`, `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.source_section_rightInverse`, `OAI.PolycyclicRecognition.CartanWordModel.exists_normalized_polar_samplers`, `OAI_PolycyclicRecognition_CartanWordModel_exists_polar_flow_tiling`, `OAI.PolycyclicRecognition.CartanWordModel.exists_polar_tiled_probe_chains_from_box`, `OAI_PolycyclicRecognition_CartanWordModel_ray_boundary_homeomorphisms_of_compact_shadows`, `OAI_PolycyclicRecognition_CartanWordModel_uniform_affine_bound_of_published_inputs_and_sublinear`, `OAI.PolycyclicRecognition.TypeFPInfinity.heightKernel_virtualSolvable`, `OAI_PolycyclicRecognition_exists_semidirect_box_metric_bound` and `OAI.PolycyclicRecognition.recognition_and_lattice_of_uniform_normalized_height_proved`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D016
import Definitions.Def_OAIQ093D017
import Definitions.Def_OAIQ093D018

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PolynomialInnerAdjoint
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.derivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.groupAutomorphism_apply _root_.OAI.PolycyclicRecognition.abelianRealLatticeEquiv_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.polynomialCoordinateHom_apply _root_.OAI.PolycyclicRecognition.polynomialInnerLieEquiv_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inner conjugation in the concrete exponential coordinates -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
attribute [local instance] LieRing.ofAssociativeRing
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

theorem polynomial_adjoint_apply (u x : L) :
    adjointLinearMap (E := L) u x = u * x * u⁻¹ := by
  have h := PolynomialExponentialCoordinates.isGroupExponential_identity.map_of_mdifferentiable
    (PolynomialExponentialCoordinates.isGroupExponential_identity (L := L))
    (MulAut.conj u).toMonoidHom ((contMDiff_conjugation u).mdifferentiable (by simp)) x
  exact h.symm

theorem polynomial_adjointOperator (u : L) :
    groupAdjointOperator (P.tangentEquiv u) =
      LinearMap.toContinuousLinearMap (LieAlgebra.ad ℝ L u) := by
  apply ContinuousLinearMap.ext
  intro v
  have h := (P.tangentEquiv.map_lie u v).symm
  rw [P.tangentEquiv_apply v, P.tangentEquiv_apply ⁅u, v⁆] at h
  exact h

theorem polynomial_inner_eq_exp_ad (u x : L) :
    u * x * u⁻¹ = NormedSpace.exp (LinearMap.toContinuousLinearMap (LieAlgebra.ad ℝ L u)) x := by
  have h := adjointLinearMap_exponential
    (PolynomialExponentialCoordinates.isGroupExponential_identity (L := L)) (P.tangentEquiv u) 1
  rw [one_smul, polynomial_adjointOperator, P.tangentEquiv_apply] at h
  simp only [one_smul] at h
  rw [← polynomial_adjoint_apply u x, h]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialInnerUnipotence
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.derivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.groupAutomorphism_apply _root_.OAI.PolycyclicRecognition.abelianRealLatticeEquiv_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.polynomialCoordinateHom_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inner perturbations of unipotent nilpotent-group automorphisms

Inner conjugations act trivially on every lower-central quotient. Consequently
multiplying a unipotent automorphism by an arbitrary inner automorphism is
still unipotent, even when the two automorphisms do not commute.
-/

noncomputable section
namespace PolycyclicRecognition
open LieModule
open scoped Manifold ContDiff
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

theorem polynomial_inner_sub_mem_succ (w : L) (k : ℕ) (x : L)
    (hx : x ∈ lowerCentralSeries ℝ L L k) :
    polynomialInnerLieEquiv w x - x ∈ lowerCentralSeries ℝ L L (k + 1) := by
  let F : ℕ → Submodule ℝ L := fun k => (lowerCentralSeries ℝ L L k).toSubmodule
  have hw0 : w * (0 : L) = w := by rw [← P.one_eq_zero, mul_one]
  have h1 : (w * x - w) - x ∈ F (k + 1) := by
    simpa only [sub_self, sub_zero, zero_add, hw0] using
      polynomial_mul_difference k w x w 0 (by simp) (by simpa using hx)
  have hd : w * x - w ∈ F k := by
    have hh := (F k).add_mem
      ((antitone_lowerCentralSeries ℝ L L (Nat.le_succ k)) h1) hx
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (abel)
  have h2 : (w * x * w⁻¹ - 0) - (w * x - w) ∈ F (k + 1) := by
    simpa only [sub_self, add_zero, mul_inv_cancel, P.one_eq_zero] using
      polynomial_mul_difference k (w * x) w⁻¹ w w⁻¹ hd (by simp)
  have hh := (F (k + 1)).add_mem h2 h1
  change polynomialInnerLieEquiv w x - x ∈ F (k + 1)
  rw [polynomialInnerLieEquiv_apply]
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (abel)

variable [LieRing.IsNilpotent L]

theorem polynomial_inner_mul_unipotent (U : L ≃ₗ⁅ℝ⁆ L)
    (hU : IsNilpotent (U.toLinearMap - 1)) (w : L) :
    IsNilpotent ((polynomialInnerLieEquiv w).toLinearMap * U.toLinearMap - 1) := by
  let F : ℕ → Submodule ℝ L := fun k => (lowerCentralSeries ℝ L L k).toSubmodule
  let a : Module.End ℝ L := (polynomialInnerLieEquiv w).toLinearMap * U.toLinearMap - 1
  let b : Module.End ℝ L := U.toLinearMap - 1
  have hUp (k : ℕ) (x : L) (hx : x ∈ F k) : U x ∈ F k :=
    LieIdeal.map_lowerCentralSeries_le k (LieIdeal.mem_map hx)
  have hIp (k : ℕ) (x : L) (hx : x ∈ F k) : polynomialInnerLieEquiv w x ∈ F k :=
    LieIdeal.map_lowerCentralSeries_le k (LieIdeal.mem_map hx)
  obtain ⟨c, hc⟩ := (LieModule.isNilpotent_iff ℝ L L).mp
    (inferInstance : LieModule.IsNilpotent L L)
  apply nilpotent_of_filtered_nilpotent_perturbation F (by simp [F])
    (congrArg LieSubmodule.toSubmodule hc) a b
  · intro k x hx
    exact (F k).sub_mem (hIp k _ (hUp k x hx)) hx
  · intro k x hx
    exact (F k).sub_mem (hUp k x hx) hx
  · intro k x hx
    have hh := polynomial_inner_sub_mem_succ w k (U x) (hUp k x hx)
    change polynomialInnerLieEquiv w (U x) - U x ∈ F (k + 1) at hh
    change (polynomialInnerLieEquiv w (U x) - x) - (U x - x) ∈ F (k + 1)
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (abel)
  · exact hU

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialInnerLogarithm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.derivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.groupAutomorphism_apply _root_.OAI.PolycyclicRecognition.abelianRealLatticeEquiv_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.polynomialCoordinateHom_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact logarithm of every inner automorphism in exponential coordinates -/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
local instance polynomialInnerRationalModule : Module ℚ L :=
  Module.compHom L (algebraMap ℚ ℝ)

theorem polynomial_inner_unipotent (w : L) :
    IsNilpotent ((polynomialInnerLieEquiv w).toLinearMap - 1) := by
  have h := polynomial_inner_mul_unipotent (LieEquiv.refl : L ≃ₗ⁅ℝ⁆ L)
    (by change IsNilpotent ((1 : Module.End ℝ L) - 1); simp) w
  change IsNilpotent ((polynomialInnerLieEquiv w).toLinearMap * 1 - 1) at h
  simpa only [mul_one] using h

theorem polynomial_inner_log (w : L) :
    nilpotentLog ((polynomialInnerLieEquiv w).toLinearMap - 1) = LieAlgebra.ad ℝ L w := by
  let E := Module.End.toContinuousLinearMap (𝕜 := ℝ) L
  let := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  have hn : IsNilpotent (LieAlgebra.ad ℝ L w) :=
    LieModule.isNilpotent_toEnd_of_isNilpotent ℝ L L w
  have hexp : E (polynomialInnerLieEquiv w).toLinearMap =
      NormedSpace.exp (LinearMap.toContinuousLinearMap (LieAlgebra.ad ℝ L w)) := by
    apply ContinuousLinearMap.ext
    intro x
    exact (polynomialInnerLieEquiv_apply w x).trans (polynomial_inner_eq_exp_ad w x)
  apply E.injective
  have he : E (nilpotentLog ((polynomialInnerLieEquiv w).toLinearMap - 1)) =
      nilpotentLog (E ((polynomialInnerLieEquiv w).toLinearMap - 1)) :=
    (nilpotentLog_map E.toRingHom _ (polynomial_inner_unipotent w)).symm
  rw [he, map_sub, map_one, hexp]
  have hn' : IsNilpotent (LinearMap.toContinuousLinearMap (LieAlgebra.ad ℝ L w)) :=
    hn.map E.toRingHom
  rw [analytic_exp_eq_nilpotent_exp hn', nilpotentLog_exp _ hn']
  rfl

theorem polynomial_inner_eq_implies_ad_eq (u v : L)
    (h : (polynomialInnerLieEquiv u).toLinearMap = (polynomialInnerLieEquiv v).toLinearMap) :
    LieAlgebra.ad ℝ L u = LieAlgebra.ad ℝ L v := by
  rw [← polynomial_inner_log u, ← polynomial_inner_log v, h]

omit [LieRing.IsNilpotent L] in
theorem polynomial_inner_eq_of_ad_eq (u v : L)
    (h : LieAlgebra.ad ℝ L u = LieAlgebra.ad ℝ L v) :
    (polynomialInnerLieEquiv u).toLinearMap = (polynomialInnerLieEquiv v).toLinearMap := by
  apply LinearMap.ext
  intro x
  change polynomialInnerLieEquiv u x = polynomialInnerLieEquiv v x
  rw [polynomialInnerLieEquiv_apply, polynomialInnerLieEquiv_apply,
    polynomial_inner_eq_exp_ad, polynomial_inner_eq_exp_ad, h]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SemisimpleCentralDecomposition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed and central parts of a semisimple inner centralizer

The canonical fixed projection separates the center from the fixed subgroup.
The moving part of any inner-centralizing vector is genuinely central.
-/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

omit [FiniteDimensional ℝ L] in
theorem ad_kernel_invariant (S : L ≃ₗ⁅ℝ⁆ L) (x : L)
    (hx : LieAlgebra.ad ℝ L x = 0) : LieAlgebra.ad ℝ L (S x) = 0 := by
  apply LinearMap.ext
  intro y
  have hxy : ⁅x, S.symm y⁆ = 0 := LinearMap.congr_fun hx (S.symm y)
  change ⁅S x, y⁆ = 0
  calc
    _ = S ⁅x, S.symm y⁆ := by rw [S.map_lie, S.apply_symm_apply]
    _ = 0 := by rw [hxy, map_zero]

def semisimpleOneProjection (S : Module.End ℝ L) (hS : S.IsSemisimple) : Module.End ℝ L :=
  semisimpleKernelProjection (S - 1) (semisimple_sub_one S hS)

theorem semisimple_central_difference_of_ad_sub_zero (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) (x : L)
    (hx : LieAlgebra.ad ℝ L (S x - x) = 0) :
    LieAlgebra.ad ℝ L (x - semisimpleOneProjection S.toLinearMap hS x) = 0 := by
  let Z : Submodule ℝ L := (LieAlgebra.ad ℝ L).ker.toSubmodule
  let B : Module.End ℝ L := S.toLinearMap - 1
  have hZ (z : L) (hz : z ∈ Z) : B z ∈ Z := by
    change LieAlgebra.ad ℝ L z = 0 at hz
    change LieAlgebra.ad ℝ L (S z - z) = 0
    rw [map_sub, ad_kernel_invariant S z hz, hz, sub_self]
  exact semisimple_sub_projection_mem_of_apply_mem B (semisimple_sub_one S.toLinearMap hS) Z hZ hx

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_InnerCentralizerLieSubalgebra
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Lie algebra of the inner centralizer

Vectors centralizing S modulo the center form a Lie subalgebra. Their brackets
are actually fixed by S, which makes the fixed projection a Lie homomorphism.
-/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

omit [FiniteDimensional ℝ L] in
theorem bracket_fixed_of_central_differences (S : L ≃ₗ⁅ℝ⁆ L) (x y : L)
    (hx : LieAlgebra.ad ℝ L (S x - x) = 0)
    (hy : LieAlgebra.ad ℝ L (S y - y) = 0) : S ⁅x, y⁆ = ⁅x, y⁆ := by
  have hx' : ⁅S x, S y⁆ = ⁅x, S y⁆ := by
    have hh : ⁅S x - x, S y⁆ = 0 := LinearMap.congr_fun hx (S y)
    rw [sub_lie, sub_eq_zero] at hh
    exact hh
  have hy' : ⁅x, S y⁆ = ⁅x, y⁆ := by
    have hh : ⁅S y - y, x⁆ = 0 := LinearMap.congr_fun hy x
    have hh' : ⁅x, S y - y⁆ = 0 := by rw [← lie_skew, hh, neg_zero]
    rwa [lie_sub, sub_eq_zero] at hh'
  rw [S.map_lie, hx', hy']

def innerCentralizerLieSubalgebra (S : L ≃ₗ⁅ℝ⁆ L) : LieSubalgebra ℝ L where
  toSubmodule := ((LieAlgebra.ad ℝ L).toLinearMap.comp (S.toLinearMap - 1)).ker
  lie_mem' := by
    intro x y hx hy
    change LieAlgebra.ad ℝ L (S x - x) = 0 at hx
    change LieAlgebra.ad ℝ L (S y - y) = 0 at hy
    change LieAlgebra.ad ℝ L (S ⁅x, y⁆ - ⁅x, y⁆) = 0
    rw [bracket_fixed_of_central_differences S x y hx hy, sub_self, map_zero]

theorem fixed_projection_bracket (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) (x y : L)
    (hx : LieAlgebra.ad ℝ L (S x - x) = 0)
    (hy : LieAlgebra.ad ℝ L (S y - y) = 0) :
    semisimpleOneProjection S.toLinearMap hS ⁅x, y⁆ =
      ⁅semisimpleOneProjection S.toLinearMap hS x, semisimpleOneProjection S.toLinearMap hS y⁆ := by
  let P := semisimpleOneProjection S.toLinearMap hS
  have hpx : S (P x) = P x := sub_eq_zero.mp
    (semisimpleKernelProjection_mem _ (semisimple_sub_one S.toLinearMap hS) x)
  have hpy : S (P y) = P y := sub_eq_zero.mp
    (semisimpleKernelProjection_mem _ (semisimple_sub_one S.toLinearMap hS) y)
  have hx0 := semisimple_central_difference_of_ad_sub_zero S hS x hx
  have hy0 := semisimple_central_difference_of_ad_sub_zero S hS y hy
  have hbr : ⁅x, y⁆ = ⁅P x, P y⁆ := by
    have ha : ⁅x - P x, y⁆ = 0 := LinearMap.congr_fun hx0 y
    have hb : ⁅y - P y, P x⁆ = 0 := LinearMap.congr_fun hy0 (P x)
    have hb' : ⁅P x, y - P y⁆ = 0 := by rw [← lie_skew, hb, neg_zero]
    rw [sub_lie, sub_eq_zero] at ha
    rw [lie_sub, sub_eq_zero] at hb'
    exact ha.trans hb'
  have hfix : S ⁅P x, P y⁆ = ⁅P x, P y⁆ := by rw [S.map_lie, hpx, hpy]
  have hp : P ⁅P x, P y⁆ = ⁅P x, P y⁆ :=
    Submodule.projection_apply_of_mem_left _ (sub_eq_zero.mpr hfix)
  change P ⁅x, y⁆ = ⁅P x, P y⁆
  rw [hbr, hp]

def innerCentralizerFixedProjection (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) : innerCentralizerLieSubalgebra S →ₗ⁅ℝ⁆ L where
  toFun x := semisimpleOneProjection S.toLinearMap hS x
  map_add' x y := (semisimpleOneProjection S.toLinearMap hS).map_add x y
  map_smul' r x := (semisimpleOneProjection S.toLinearMap hS).map_smul r x
  map_lie' {x y} := fixed_projection_bracket S hS x y x.property y.property

def innerCentralizerCentralProjection (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) : innerCentralizerLieSubalgebra S →ₗ⁅ℝ⁆ L where
  toLinearMap := (innerCentralizerLieSubalgebra S).subtype -
    (innerCentralizerFixedProjection S hS).toLinearMap
  map_lie' := by
    intro x y
    let P := semisimpleOneProjection S.toLinearMap hS
    have hfix : S ⁅(x : L), (y : L)⁆ = ⁅(x : L), (y : L)⁆ :=
      bracket_fixed_of_central_differences S x y x.property y.property
    have hp : P ⁅(x : L), (y : L)⁆ = ⁅(x : L), (y : L)⁆ :=
      Submodule.projection_apply_of_mem_left _ (sub_eq_zero.mpr hfix)
    have hz : LieAlgebra.ad ℝ L ((x : L) - P x) = 0 :=
      semisimple_central_difference_of_ad_sub_zero S hS x x.property
    have hbr : ⁅(x : L) - P x, (y : L) - P y⁆ = 0 :=
      LinearMap.congr_fun hz ((y : L) - P y)
    change ⁅(x : L), (y : L)⁆ - P ⁅(x : L), (y : L)⁆ =
      ⁅(x : L) - P x, (y : L) - P y⁆
    rw [hp, sub_self, hbr]

theorem innerCentralizerCentralProjection_central (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) (x : innerCentralizerLieSubalgebra S) :
    LieAlgebra.ad ℝ L (innerCentralizerCentralProjection S hS x) = 0 :=
  semisimple_central_difference_of_ad_sub_zero S hS x x.property

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InnerCentralizerProduct
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A direct product decomposition of the semisimple inner centralizer

The moving factor is central and the other factor is fixed pointwise. Both
projections preserve the actual polynomial group law.
-/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing polynomialSubalgebraGroup
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

def semisimpleMovingCenter (S : L ≃ₗ⁅ℝ⁆ L) : LieSubalgebra ℝ L where
  toSubmodule := (LieAlgebra.ad ℝ L).ker.toSubmodule ⊓ (S.toLinearMap - 1).range
  lie_mem' := by
    intro x y hx _
    have hz : ⁅x, y⁆ = 0 := LinearMap.congr_fun hx.1 y
    rw [hz]
    exact ⟨map_zero _, Submodule.zero_mem _⟩

omit [FiniteDimensional ℝ L] in
theorem movingCenter_mem_innerCentralizer (S : L ≃ₗ⁅ℝ⁆ L) {x : L}
    (hx : x ∈ semisimpleMovingCenter S) : x ∈ innerCentralizerLieSubalgebra S := by
  have hSx : LieAlgebra.ad ℝ L (S x) = 0 := by
    apply LinearMap.ext
    intro y
    have hh : ⁅x, S.symm y⁆ = 0 := LinearMap.congr_fun hx.1 (S.symm y)
    change ⁅S x, y⁆ = 0
    rw [← S.apply_symm_apply y, ← S.map_lie, hh, map_zero]
  change LieAlgebra.ad ℝ L (S x - x) = 0
  rw [map_sub, hSx, show LieAlgebra.ad ℝ L x = 0 from hx.1, sub_self]

variable [P : PolynomialExponentialCoordinates L]

def innerCentralizerMovingGroupProjection (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) :
    innerCentralizerLieSubalgebra S →* semisimpleMovingCenter S :=
  polynomialSubalgebraMap _ _ (innerCentralizerCentralProjection S hS) (fun x =>
    ⟨innerCentralizerCentralProjection_central S hS x,
      Submodule.sub_projection_mem (semisimple_kernel_range_isCompl _
        (semisimple_sub_one S.toLinearMap hS)) x⟩)

def innerCentralizerMovingInclusion (S : L ≃ₗ⁅ℝ⁆ L) :
    semisimpleMovingCenter S →* innerCentralizerLieSubalgebra S :=
  polynomialSubalgebraMap _ _ (semisimpleMovingCenter S).incl
    (fun x => movingCenter_mem_innerCentralizer S x.property)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InnerCentralizerMembership
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Lie subalgebra is the actual inner-action centralizer

The exact finite logarithm identifies the group condition with centrality of
Sx-x. This connects the product decomposition to kernels of group extensions.
-/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

theorem mem_innerCentralizerLieSubalgebra_iff (S : L ≃ₗ⁅ℝ⁆ L) (x : L) :
    x ∈ innerCentralizerLieSubalgebra S ↔
      Commute S.toLinearMap (polynomialInnerLieEquiv x).toLinearMap := by
  let s := PolynomialExponentialCoordinates.groupAutomorphism (P := P) S
  have he (y : L) : S (polynomialInnerLieEquiv x y) =
      polynomialInnerLieEquiv (S x) (S y) := by
    rw [polynomialInnerLieEquiv_apply, polynomialInnerLieEquiv_apply]
    change s (x * y * x⁻¹) = s x * s y * (s x)⁻¹
    rw [map_mul, map_mul, map_inv]
  constructor
  · intro hx
    have hd : LieAlgebra.ad ℝ L (S x) = LieAlgebra.ad ℝ L x := by
      change LieAlgebra.ad ℝ L (S x - x) = 0 at hx
      rwa [map_sub, sub_eq_zero] at hx
    have hi := polynomial_inner_eq_of_ad_eq (S x) x hd
    apply LinearMap.ext
    intro y
    change S (polynomialInnerLieEquiv x y) = polynomialInnerLieEquiv x (S y)
    rw [he]
    exact LinearMap.congr_fun hi (S y)
  · intro hc
    have hi : (polynomialInnerLieEquiv (S x)).toLinearMap =
        (polynomialInnerLieEquiv x).toLinearMap := by
      apply LinearMap.ext
      intro y
      have hh : S (polynomialInnerLieEquiv x (S.symm y)) =
          polynomialInnerLieEquiv x (S (S.symm y)) :=
        LinearMap.congr_fun hc.eq (S.symm y)
      rw [he, S.apply_symm_apply] at hh
      exact hh
    change LieAlgebra.ad ℝ L (S x - x) = 0
    rw [map_sub, polynomial_inner_eq_implies_ad_eq (S x) x hi, sub_self]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SemisimpleMovingAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equivariance of the centralizer product decomposition -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing polynomialSubalgebraGroup
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

omit [FiniteDimensional ℝ L] in
theorem lieEquiv_map_ad_eq_zero (T : L ≃ₗ⁅ℝ⁆ L) (x : L)
    (hx : LieAlgebra.ad ℝ L x = 0) : LieAlgebra.ad ℝ L (T x) = 0 := by
  apply LinearMap.ext
  intro y
  have hh : ⁅x, T.symm y⁆ = 0 := LinearMap.congr_fun hx (T.symm y)
  change ⁅T x, y⁆ = 0
  rw [← T.apply_symm_apply y, ← T.map_lie, hh, map_zero]

omit [FiniteDimensional ℝ L] in
theorem commuting_lieEquiv_preserves_movingCenter (S T : L ≃ₗ⁅ℝ⁆ L)
    (hST : Commute S.toLinearMap T.toLinearMap) (x : L)
    (hx : x ∈ semisimpleMovingCenter S) : T x ∈ semisimpleMovingCenter S := by
  refine ⟨lieEquiv_map_ad_eq_zero T x hx.1, ?_⟩
  obtain ⟨y, hy⟩ := hx.2
  refine ⟨T y, ?_⟩
  have hh : S (T y) = T (S y) := LinearMap.congr_fun hST.eq y
  change S (T y) - T y = T x
  rw [hh, ← map_sub]
  exact congrArg T hy

omit [FiniteDimensional ℝ L] in
theorem commuting_lieEquiv_preserves_innerCentralizer (S T : L ≃ₗ⁅ℝ⁆ L)
    (hST : Commute S.toLinearMap T.toLinearMap) (x : L)
    (hx : x ∈ innerCentralizerLieSubalgebra S) : T x ∈ innerCentralizerLieSubalgebra S := by
  have hh : S (T x) = T (S x) := LinearMap.congr_fun hST.eq x
  change LieAlgebra.ad ℝ L (S (T x) - T x) = 0
  rw [hh, ← map_sub]
  exact lieEquiv_map_ad_eq_zero T _ hx

variable [P : PolynomialExponentialCoordinates L]

def semisimpleMovingGroupAction (S T : L ≃ₗ⁅ℝ⁆ L)
    (hST : Commute S.toLinearMap T.toLinearMap) :
    MulAut (semisimpleMovingCenter S) :=
  polynomialSubalgebraEquiv _ _ T
    (commuting_lieEquiv_preserves_movingCenter S T hST)
    (commuting_lieEquiv_preserves_movingCenter S T.symm
      (linear_commute_symm T.toLinearEquiv S.toLinearMap hST))

def innerCentralizerGroupAction (S T : L ≃ₗ⁅ℝ⁆ L)
    (hST : Commute S.toLinearMap T.toLinearMap) :
    MulAut (innerCentralizerLieSubalgebra S) :=
  polynomialSubalgebraEquiv _ _ T
    (commuting_lieEquiv_preserves_innerCentralizer S T hST)
    (commuting_lieEquiv_preserves_innerCentralizer S T.symm
      (linear_commute_symm T.toLinearEquiv S.toLinearMap hST))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_InnerCentralizerFactorSystem
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restriction of a factor system to the inner centralizer

Commutation of every quotient action with S forces every section factor into
the inner centralizer. The restriction retains the exact nonabelian cocycle.
-/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] polynomialSubalgebraGroup
variable {L Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L] [Group Q]

theorem factor_mem_innerCentralizer (F : NonabelianFactorSystem L Q)
    (A : Q → L ≃ₗ⁅ℝ⁆ L) (hact : ∀ q x, F.action q x = A q x)
    (S : L ≃ₗ⁅ℝ⁆ L) (hSA : ∀ q, Commute S.toLinearMap (A q).toLinearMap) (q r : Q) :
    F.factor q r ∈ innerCentralizerLieSubalgebra S := by
  have he : (A q).toLinearMap * (A r).toLinearMap =
      (polynomialInnerLieEquiv (F.factor q r)).toLinearMap * (A (q * r)).toLinearMap := by
    apply LinearMap.ext
    intro x
    change A q (A r x) = polynomialInnerLieEquiv (F.factor q r) (A (q * r) x)
    rw [polynomialInnerLieEquiv_apply, ← hact, ← hact, ← hact, F.action_mul_apply]
  apply (mem_innerCentralizerLieSubalgebra_iff S _).mpr
  have hc := (hSA q).mul_right (hSA r)
  rw [he] at hc
  exact linear_commute_of_mul_equiv_right S.toLinearMap
    (polynomialInnerLieEquiv (F.factor q r)).toLinearMap (A (q * r)).toLinearEquiv (hSA _) hc

def innerCentralizerFactorSystem (F : NonabelianFactorSystem L Q)
    (A : Q → L ≃ₗ⁅ℝ⁆ L) (hact : ∀ q x, F.action q x = A q x)
    (S : L ≃ₗ⁅ℝ⁆ L) (hSA : ∀ q, Commute S.toLinearMap (A q).toLinearMap) :
    NonabelianFactorSystem (innerCentralizerLieSubalgebra S) Q where
  action q := innerCentralizerGroupAction S (A q) (hSA q)
  factor q r := ⟨F.factor q r, factor_mem_innerCentralizer F A hact S hSA q r⟩
  action_one := by
    apply DFunLike.ext
    intro x
    apply Subtype.ext
    change A 1 x = x
    rw [← hact, F.action_one]
    rfl
  factor_one_left q := Subtype.ext (F.factor_one_left q)
  factor_one_right q := Subtype.ext (F.factor_one_right q)
  action_mul q r := by
    apply DFunLike.ext
    intro x
    apply Subtype.ext
    change A q (A r x) = F.factor q r * A (q * r) x * (F.factor q r)⁻¹
    rw [← hact, ← hact, ← hact, F.action_mul_apply]
  cocycle q r s := by
    apply Subtype.ext
    change F.factor q r * F.factor (q * r) s = A q (F.factor r s) * F.factor q (r * s)
    rw [← hact]
    exact F.cocycle q r s

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilpotentLatticeAutomorphisms
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.derivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.groupAutomorphism_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.polynomialCoordinateHom_apply _root_.OAI.PolycyclicRecognition.polynomialInnerLieEquiv_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending the lattice automorphism group to its nilpotent Lie model

The extension respects composition. This retains arbitrary discrete actions,
without imposing unipotence on their automorphisms.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {H : Type} [Group H]

namespace NilpotentLatticeCoordinates
variable (C : NilpotentLatticeCoordinates H)

theorem ext_polynomial {f g : C.carrier → C.carrier}
    (hf : IsPolynomialInBasis C.basis C.basis f)
    (hg : IsPolynomialInBasis C.basis C.basis g)
    (h : ∀ x : H, f (C.equiv x) = g (C.equiv x)) : f = g := by
  have hp : f ∘ C.parameter = g ∘ C.parameter :=
    (hf.comp C.polynomial).ext_integer_grid (hg.comp C.polynomial) (by
      intro z
      change f (C.parameter (C.basis.equivFun.symm (fun i => (z i : ℝ)))) =
        g (C.parameter (C.basis.equivFun.symm (fun i => (z i : ℝ))))
      rw [C.integer_parameter]
      exact h _)
  funext x
  obtain ⟨y, rfl⟩ := C.parameter.surjective x
  exact congrFun hp y

def automorphism (a : MulAut H) : MulAut C.carrier :=
  latticeWordAut C.basis C.parameter (C.lattice.subtype.comp C.equiv.toMonoidHom)
    C.generators C.polynomial C.polynomial_symm C.integer_parameter C.word_surjective a

theorem automorphism_polynomial (a : MulAut H) :
    IsPolynomialInBasis C.basis C.basis (C.automorphism a) :=
  latticeWordMap_polynomial C.basis C.parameter
    (C.lattice.subtype.comp C.equiv.toMonoidHom) C.generators
    C.polynomial_symm a.toMonoidHom

@[simp] theorem automorphism_on_lattice (a : MulAut H) (x : H) :
    C.automorphism a (C.equiv x) = (C.equiv (a x) : C.carrier) :=
  latticeWordAut_on_lattice C.basis C.parameter
    (C.lattice.subtype.comp C.equiv.toMonoidHom) C.generators
    C.polynomial C.polynomial_symm C.integer_parameter C.word_surjective a x

@[simp] theorem automorphism_one : C.automorphism 1 = 1 := by
  apply DFunLike.ext
  intro x
  have h : (C.automorphism 1 : C.carrier → C.carrier) = id :=
    C.ext_polynomial (C.automorphism_polynomial 1)
      (IsPolynomialInBasis.linear (LinearMap.id)) (by intro y; simp)
  exact congrFun h x

@[simp] theorem automorphism_mul (a b : MulAut H) :
    C.automorphism (a * b) = C.automorphism a * C.automorphism b := by
  apply DFunLike.ext
  intro x
  have h : (C.automorphism (a * b) : C.carrier → C.carrier) =
      (C.automorphism a : C.carrier → C.carrier) ∘ C.automorphism b :=
    C.ext_polynomial (C.automorphism_polynomial (a * b))
      ((C.automorphism_polynomial a).comp (C.automorphism_polynomial b)) (by
        intro y
        change C.automorphism (a * b) (C.equiv y) =
          C.automorphism a (C.automorphism b (C.equiv y))
        rw [C.automorphism_on_lattice, C.automorphism_on_lattice, C.automorphism_on_lattice]
        rfl)
  exact congrFun h x

end NilpotentLatticeCoordinates
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilpotentLatticeInnerAdjoint
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.derivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.groupAutomorphism_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.polynomialCoordinateHom_apply _root_.OAI.PolycyclicRecognition.polynomialInnerLieEquiv_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact inner action on a constructed nilpotent lattice model -/

noncomputable section
namespace PolycyclicRecognition.NilpotentLatticeCoordinates
open scoped Manifold
variable {H : Type} [Group H] (C : NilpotentLatticeCoordinates H)

theorem automorphism_inner_apply (t : H) (v : C.carrier) :
    C.automorphism (MulAut.conj t) v = (C.equiv t : C.carrier) * v * (C.equiv t : C.carrier)⁻¹ := by
  let u : C.carrier := C.equiv t
  let B := polynomialModelLieHom (MulAut.conj u).toMonoidHom
    ((contMDiff_conjugation u).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hB : (B : C.carrier → C.carrier) = fun v => u * v * u⁻¹ := by
    funext v
    exact polynomialModelLieHom_apply _ _ v
  have hpoly : IsPolynomialInBasis C.basis C.basis (fun v => u * v * u⁻¹) := by
    rw [← hB]
    exact IsPolynomialInBasis.linear B.toLinearMap
  have he : (C.automorphism (MulAut.conj t) : C.carrier → C.carrier) =
      fun v => u * v * u⁻¹ := C.ext_polynomial (C.automorphism_polynomial _) hpoly (by
    intro y
    rw [C.automorphism_on_lattice]
    simp only [MulAut.conj_apply, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rfl)
  exact congrFun he v

end PolycyclicRecognition.NilpotentLatticeCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentExtensionFactorSystem
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual real factor system of a nilpotent-kernel extension

Its failure to be an action is exactly the exponential of the inner Lie
derivation obtained from the section defect.
-/

noncomputable section
namespace PolycyclicRecognition.NilpotentLatticeCoordinates
variable {N G Q : Type} [Group N] [Group G] [Group Q]
  (C : NilpotentLatticeCoordinates N) (S : GroupExtension N G Q)
  (σ : S.Section) (hσ : σ 1 = 1)
open GroupExtensionSection
open scoped Manifold ContDiff

def extensionFactorSystem : NonabelianFactorSystem C.carrier Q where
  action q := C.automorphism (S.conjAct (σ q))
  factor q r := C.equiv (factor S σ q r)
  action_one := by rw [hσ, map_one, C.automorphism_one]
  factor_one_left q := by rw [factor_one_left S σ hσ, map_one, Subgroup.coe_one]
  factor_one_right q := by rw [factor_one_right S σ hσ, map_one, Subgroup.coe_one]
  action_mul q r := by
    rw [← C.automorphism_mul, section_action_mul, C.automorphism_mul]
    congr 1
    apply DFunLike.ext
    intro v
    exact C.automorphism_inner_apply _ v
  cocycle q r s := by
    have h := congrArg (fun n : N => (C.equiv n : C.carrier)) (factor_cocycle S σ q r s)
    simpa only [map_mul, Subgroup.coe_mul, C.automorphism_on_lattice] using h

end PolycyclicRecognition.NilpotentLatticeCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentExtensionEmbedding
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending a nilpotent lattice to the full nonsplit extension

Only the nilpotent kernel is completed here. The original quotient, section,
and all of its defects are retained exactly.
-/

noncomputable section
namespace PolycyclicRecognition.NilpotentLatticeCoordinates
variable {N G Q : Type} [Group N] [Group G] [Group Q]
  (C : NilpotentLatticeCoordinates N) (S : GroupExtension N G Q)
  (σ : S.Section) (hσ : σ 1 = 1)

/-- The original and completed factor systems agree on the kernel lattice. -/
def extensionFactorMap :
    FactorExtension (GroupExtensionSection.factorSystem S σ hσ) →*
      FactorExtension (C.extensionFactorSystem S σ hσ) :=
  FactorExtension.map _ _ (C.lattice.subtype.comp C.equiv.toMonoidHom)
    (fun q n => (C.automorphism_on_lattice (S.conjAct (σ q)) n).symm)
    (fun _ _ => rfl)

theorem extensionFactorMap_injective : Function.Injective (C.extensionFactorMap S σ hσ) :=
  FactorExtension.map_injective _ _ _ _ _ (Subtype.val_injective.comp C.equiv.injective)

/-- A faithful map of the original nonsplit extension into the group with
completed nilpotent kernel and unchanged quotient. -/
def extensionEmbedding : G →* FactorExtension (C.extensionFactorSystem S σ hσ) :=
  (C.extensionFactorMap S σ hσ).comp (GroupExtensionSection.mulEquiv S σ hσ).toMonoidHom

theorem extensionEmbedding_injective : Function.Injective (C.extensionEmbedding S σ hσ) :=
  (C.extensionFactorMap_injective S σ hσ).comp (GroupExtensionSection.mulEquiv S σ hσ).injective

end PolycyclicRecognition.NilpotentLatticeCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SemisimpleMovingLang
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bijective Lang maps on the moving central factor

The unipotent factor causes no fixed directions on the range of S-1. The
central group's Lang map is exactly that invertible linear difference.
-/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing polynomialSubalgebraGroup
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

def semisimpleMovingDifference (S T : L ≃ₗ⁅ℝ⁆ L)
    (hST : Commute S.toLinearMap T.toLinearMap) :
    Module.End ℝ (semisimpleMovingCenter S) :=
  (T.toLinearMap - 1).restrict (fun x hx => (semisimpleMovingCenter S).sub_mem
    (commuting_lieEquiv_preserves_movingCenter S T hST x hx) hx)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_JointFixedSubalgebra
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The joint fixed algebra and its unipotent quotient-lift actions -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] polynomialSubalgebraGroup
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

omit [FiniteDimensional ℝ L] in
theorem commuting_lieEquiv_preserves_jointFixed (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (T : L ≃ₗ⁅ℝ⁆ L) (hT : ∀ S ∈ ss, Commute S.toLinearMap T.toLinearMap)
    (x : L) (hx : x ∈ jointFixedLieSubalgebra ss) : T x ∈ jointFixedLieSubalgebra ss := by
  apply (mem_jointFixedLieSubalgebra ss _).mpr
  intro S hS
  have hh : S (T x) = T (S x) := LinearMap.congr_fun (hT S hS).eq x
  rw [hh, (mem_jointFixedLieSubalgebra ss x).mp hx S hS]

def jointFixedLinearAction (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (T : L ≃ₗ⁅ℝ⁆ L) (hT : ∀ S ∈ ss, Commute S.toLinearMap T.toLinearMap) :
    Module.End ℝ (jointFixedLieSubalgebra ss) :=
  T.toLinearMap.restrict (commuting_lieEquiv_preserves_jointFixed ss T hT)

def jointFixedLieAction (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (T : L ≃ₗ⁅ℝ⁆ L) (hT : ∀ S ∈ ss, Commute S.toLinearMap T.toLinearMap) :
    jointFixedLieSubalgebra ss ≃ₗ⁅ℝ⁆ jointFixedLieSubalgebra ss where
  toFun x := ⟨T x, commuting_lieEquiv_preserves_jointFixed ss T hT x x.property⟩
  invFun x := ⟨T.symm x, commuting_lieEquiv_preserves_jointFixed ss T.symm
    (fun S hS => linear_commute_symm T.toLinearEquiv S.toLinearMap (hT S hS)) x x.property⟩
  left_inv x := Subtype.ext (T.symm_apply_apply x)
  right_inv x := Subtype.ext (T.apply_symm_apply x)
  map_add' x y := Subtype.ext (T.map_add x y)
  map_smul' r x := Subtype.ext (T.map_smul r x)
  map_lie' {x y} := Subtype.ext (T.map_lie x y)

variable [P : PolynomialExponentialCoordinates L]

def jointFixedGroupAction (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (T : L ≃ₗ⁅ℝ⁆ L) (hT : ∀ S ∈ ss, Commute S.toLinearMap T.toLinearMap) :
    MulAut (jointFixedLieSubalgebra ss) :=
  polynomialSubalgebraEquiv _ _ T (commuting_lieEquiv_preserves_jointFixed ss T hT)
    (commuting_lieEquiv_preserves_jointFixed ss T.symm
      (fun S hS => linear_commute_symm T.toLinearEquiv S.toLinearMap (hT S hS)))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_JointFixedFactorSystem
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instLocallyCompactSpaceFactorExtension _root_.OAI.PolycyclicRecognition.instT2SpaceFactorExtension _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual extension on the joint fixed kernel

Once the section factors are fixed by the family, the joint fixed subgroup
supports the same nonabelian cocycle. Its factor extension embeds faithfully
in the original group.
-/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] polynomialSubalgebraGroup
variable {L Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group Q]

def jointFixedFactorSystem (F : NonabelianFactorSystem L Q)
    (A : Q → L ≃ₗ⁅ℝ⁆ L) (hact : ∀ q x, F.action q x = A q x)
    (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (hcomm : ∀ S ∈ ss, ∀ q, Commute S.toLinearMap (A q).toLinearMap)
    (hfixed : ∀ S ∈ ss, ∀ q r, S (F.factor q r) = F.factor q r) :
    NonabelianFactorSystem (jointFixedLieSubalgebra ss) Q where
  action q := jointFixedGroupAction ss (A q) (fun S hS => hcomm S hS q)
  factor q r := ⟨F.factor q r, (mem_jointFixedLieSubalgebra ss _).mpr
    (fun S hS => hfixed S hS q r)⟩
  action_one := by
    apply DFunLike.ext
    intro x
    apply Subtype.ext
    change A 1 x = x
    rw [← hact, F.action_one]
    rfl
  factor_one_left q := Subtype.ext (F.factor_one_left q)
  factor_one_right q := Subtype.ext (F.factor_one_right q)
  action_mul q r := by
    apply DFunLike.ext
    intro x
    apply Subtype.ext
    change A q (A r x) = F.factor q r * A (q * r) x * (F.factor q r)⁻¹
    rw [← hact, ← hact, ← hact, F.action_mul_apply]
  cocycle q r s := by
    apply Subtype.ext
    change F.factor q r * F.factor (q * r) s = A q (F.factor r s) * F.factor q (r * s)
    rw [← hact]
    exact F.cocycle q r s

def jointFixedFactorInclusion (F : NonabelianFactorSystem L Q)
    (A : Q → L ≃ₗ⁅ℝ⁆ L) (hact : ∀ q x, F.action q x = A q x)
    (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (hcomm : ∀ S ∈ ss, ∀ q, Commute S.toLinearMap (A q).toLinearMap)
    (hfixed : ∀ S ∈ ss, ∀ q r, S (F.factor q r) = F.factor q r) :
    FactorExtension (jointFixedFactorSystem F A hact ss hcomm hfixed) →* FactorExtension F :=
  FactorExtension.map _ _
    (polynomialSubalgebraHom _ (jointFixedLieSubalgebra ss).incl)
    (fun q x => (hact q x).symm) (fun _ _ => rfl)

variable {G : Type} [Group G]

def jointFixedExtensionEmbedding (E : GroupExtension L G Q) (σ : E.Section) (hσ : σ 1 = 1)
    (A : Q → L ≃ₗ⁅ℝ⁆ L) (hact : ∀ q x, E.conjAct (σ q) x = A q x)
    (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (hcomm : ∀ S ∈ ss, ∀ q, Commute S.toLinearMap (A q).toLinearMap)
    (hfixed : ∀ S ∈ ss, ∀ q r, S (GroupExtensionSection.factor E σ q r) =
      GroupExtensionSection.factor E σ q r) :
    FactorExtension (jointFixedFactorSystem (GroupExtensionSection.factorSystem E σ hσ)
      A hact ss hcomm hfixed) →* G :=
  (GroupExtensionSection.mulEquiv E σ hσ).symm.toMonoidHom.comp
    (jointFixedFactorInclusion _ A hact ss hcomm hfixed)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_JointFixedReductionData
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Constructed joint-fixed residual data for an actual extension

The residual group is defined by the actual section factors and embeds in the
original extension. The prescribed quotient lifts act unipotently on its
kernel Lie algebra.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff IsMulCommutative
attribute [local instance] polynomialSubalgebraGroup
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q]

structure JointFixedReductionData (E : GroupExtension L G Q)
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)) (qs : List Q) where
  operators : List (L ≃ₗ⁅ℝ⁆ L)
  semisimple : ∀ S ∈ operators, Module.End.IsSemisimple S.toLinearMap
  commute : ∀ S ∈ operators, ∀ T ∈ operators, Commute S.toLinearMap T.toLinearMap
  sectionMap : E.Section
  normalized : sectionMap 1 = 1
  centralizes : ∀ S ∈ operators, ∀ q, sectionMap q ∈ semisimpleActionCentralizer E S
  factorsFixed : ∀ S ∈ operators, ∀ q r, S (GroupExtensionSection.factor E sectionMap q r) =
    GroupExtensionSection.factor E sectionMap q r
  jordanLifts : ∀ q ∈ qs, ∃ S ∈ operators, ∃ U : L ≃ₗ⁅ℝ⁆ L,
    IsNilpotent (U.toLinearMap - 1) ∧ Commute S.toLinearMap U.toLinearMap ∧
    (polynomialModelLieEquiv (E.conjAct (sectionMap q)) (hsmooth (sectionMap q))).toLinearMap =
      S.toLinearMap * U.toLinearMap

namespace JointFixedReductionData
variable {E : GroupExtension L G Q}
  {hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)} {qs : List Q}
  (D : JointFixedReductionData E hsmooth qs)

def action (q : Q) : L ≃ₗ⁅ℝ⁆ L :=
  polynomialModelLieEquiv (E.conjAct (D.sectionMap q)) (hsmooth (D.sectionMap q))

end JointFixedReductionData
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_JointFixedActionFiltration
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # The residual quotient actions commute on lower-central factors

The two orders of quotient lifts differ by inner automorphisms. Intrinsic BCH
commutator estimates make both inner corrections disappear on the next Lie
lower-central quotient.
-/

noncomputable section
namespace PolycyclicRecognition
open LieModule
open scoped IsMulCommutative
attribute [local instance] polynomialSubalgebraGroup
variable {L Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group Q] [IsMulCommutative Q]

theorem jointFixed_action_preserves_lowerCentral (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (T : L ≃ₗ⁅ℝ⁆ L) (hT : ∀ S ∈ ss, Commute S.toLinearMap T.toLinearMap)
    (k : ℕ) (x : jointFixedLieSubalgebra ss)
    (hx : x ∈ lowerCentralSeries ℝ (jointFixedLieSubalgebra ss) (jointFixedLieSubalgebra ss) k) :
    jointFixedGroupAction ss T hT x ∈
      lowerCentralSeries ℝ (jointFixedLieSubalgebra ss) (jointFixedLieSubalgebra ss) k :=
  LieIdeal.map_lowerCentralSeries_le k (LieIdeal.mem_map (f := (jointFixedLieAction ss T hT).toLieHom) hx)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_JointFixedLayerAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # The abelian quotient acts on the residual lower-central layers

Inner section factors disappear on these layers, so this is an actual linear
representation of the quotient. Its selected generators are unipotent.
-/

noncomputable section
namespace PolycyclicRecognition
open LieModule
open scoped Manifold ContDiff IsMulCommutative
attribute [local instance] polynomialSubalgebraGroup
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q]
  {E : GroupExtension L G Q}
  {hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)} {qs : List Q}

namespace JointFixedReductionData
variable (D : JointFixedReductionData E hsmooth qs)

abbrev lowerCentralLayer (k : ℕ) := InvariantLinearLayer
  (lowerCentralSeries ℝ (jointFixedLieSubalgebra D.operators) (jointFixedLieSubalgebra D.operators) k).toSubmodule
  (lowerCentralSeries ℝ (jointFixedLieSubalgebra D.operators) (jointFixedLieSubalgebra D.operators) (k + 1)).toSubmodule

end JointFixedReductionData
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ResidualLowerCentralLayers
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Group commutators on the joint-fixed lower-central layers -/

noncomputable section
namespace PolycyclicRecognition
open LieModule
open scoped Manifold ContDiff IsMulCommutative
attribute [local instance] polynomialSubalgebraGroup
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q] [IsMulCommutative Q]
  {E : GroupExtension L G Q}
  {hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)} {qs : List Q}

namespace JointFixedReductionData
variable (D : JointFixedReductionData E hsmooth qs)

abbrev residualKernelLayer (k : ℕ) : Subgroup (jointFixedLieSubalgebra D.operators) :=
  polynomialLieIdealSubgroup _ (lowerCentralSeries ℝ _ _ k)

end JointFixedReductionData
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_BooleanStepProjective
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.telescopeAugmentation_epi _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.horseshoeCover_projective _root_.OAI.PolycyclicRecognition.integralRepresentationSum_projective _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedSyzygy_projective _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countable Boolean step rings are projective over the integers

Enumerating the Boolean coordinates gives a sequence of finite partitions.
Their modules are free, the refinement maps split, and their colimit is the
step ring itself. No freeness theorem about all bounded functions is needed.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
variable {X I : Type} (a : I → X → Bool) (b : ℕ → I)

def booleanStepColimit (hb : Function.Surjective b) :
    (booleanPartitionDiagram a b).ColimitCocone (booleanStepRepresentation a) where
  ι n := booleanPartitionEvaluation a (booleanPrefix b n)
  comm _ _ h := booleanPartitionMap_evaluation a (booleanPrefix_mono b h)
  surj f := by
    obtain ⟨s, hs⟩ := f.property
    obtain ⟨n, hn⟩ := exists_booleanPrefix_contains b hb s
    obtain ⟨v, hv⟩ := dependsOnBoolean_factorization (hs.mono hn)
    refine ⟨n, v, ?_⟩
    apply Subtype.ext
    exact hv.symm
  zero_exact i v hv := by
    refine ⟨i, le_rfl, ?_⟩
    have h0 : v = 0 := booleanPartitionEvaluation_injective a (booleanPrefix b i)
      (hv.trans (map_zero _).symm)
    rw [h0, map_zero]

theorem booleanStepRepresentation_projective (hb : Function.Surjective b) :
    Projective (booleanStepRepresentation a) := by
  let D := booleanPartitionDiagram a b
  let r : ∀ i, D.obj (i + 1) ⟶ D.obj i := fun i =>
    booleanPartitionRetraction a (booleanPrefix_mono b (Nat.le_succ i))
  have hr : ∀ i, D.map i (i + 1) (Nat.le_succ i) ≫ r i = 𝟙 _ :=
    fun i => booleanPartitionMap_retraction a (booleanPrefix_mono b (Nat.le_succ i))
  let : ∀ i, Projective (D.obj i) := fun i => booleanPartitionStage_projective a _
  exact D.split_colimit_projective r hr (booleanStepColimit a b hb)

/-- The small step-function algebra required in the countable group application. -/
theorem booleanStepRing_integer_projective [Countable I] [Nonempty I] :
    Module.Projective ℤ (booleanStepRing a) := by
  obtain ⟨b, hb⟩ := exists_surjective_nat I
  let := booleanStepRepresentation_projective a b hb
  exact integer_projective_of_projective_rep (booleanStepRepresentation a)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_SmallCoefficientRing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A small ring of bounded functions with finite-subgroup projectivity

For each finite subgroup choose its right-coset transversal. Take the Boolean
algebra generated by every left translate of these transversals and of
subgroup coset partitions inside finitely generated subgroups. When the group
is countable, this uses countably many coordinates. Its step-function ring is
projective over the integers and has a trace-one element for every finite
subgroup.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance] Classical.propDecidable
variable (G : Type) [Group G]

set_option synthInstance.maxHeartbeats 400000 in
instance smallCoefficientRing_integer_projective [Countable G] :
    Module.Projective ℤ (SmallCoefficientRing G) :=
  booleanStepRing_integer_projective (smallCoefficientFeature G)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_SmallCoefficientIdentityCycle
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unit identity cocycles in the coefficient-ring tower

The ordinary integral resolution remains the source of the cochains. Their
coefficients are the same syzygies tensored with the small coefficient ring.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2300] TensorProduct.instModule
variable (G : Type) [Group G] [Countable G]

set_option synthInstance.maxHeartbeats 400000 in
abbrev smallCoefficientTower : IntegralProjectiveTower G :=
  tensorNormalizedProjectiveTower (smallCoefficientRepresentation G)

set_option synthInstance.maxHeartbeats 400000 in
def smallCoefficientIdentityCochain (n : ℕ) :
    (normalizedResolutionComplex (trivialIntegral G)).X n ⟶ (smallCoefficientTower G).obj n :=
  normalizedResolutionProjection (trivialIntegral G) n ≫
    smallCoefficientTensorUnit ((iteratedNormalizedSyzygy n).obj (trivialIntegral G))

set_option synthInstance.maxHeartbeats 400000 in
theorem smallCoefficientIdentityCochain_closed (n : ℕ) :
    (normalizedResolutionComplex (trivialIntegral G)).d (n + 1) n ≫
      smallCoefficientIdentityCochain G n = 0 := by
  unfold smallCoefficientIdentityCochain
  erw [← Category.assoc, normalizedResolution_d_projection, zero_comp]

set_option synthInstance.maxHeartbeats 400000 in
def smallCoefficientIdentityCycle (n : ℕ) :
    ((normalizedResolutionComplex (trivialIntegral G)).linearYonedaObj ℤ
      ((smallCoefficientTower G).obj n)).cycles n :=
  ((normalizedResolutionComplex (trivialIntegral G)).linearYonedaObj ℤ
      ((smallCoefficientTower G).obj n)).cyclesMk (smallCoefficientIdentityCochain G n)
    (n + 1) (by simp) (smallCoefficientIdentityCochain_closed G n)

set_option synthInstance.maxHeartbeats 400000 in
def smallCoefficientIdentityClass (n : ℕ) :
    ((normalizedResolutionComplex (trivialIntegral G)).linearYonedaObj ℤ
      ((smallCoefficientTower G).obj n)).homology n :=
  ((normalizedResolutionComplex (trivialIntegral G)).linearYonedaObj ℤ
      ((smallCoefficientTower G).obj n)).homologyπ n (smallCoefficientIdentityCycle G n)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_SmallCoefficientCompletedUnit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.cyclicTopHomologyInjection_mono _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complete vanishing detects the dimension of the coefficient ring

The unit cocycles are carried by the connecting maps in the tensor tower.
If their completed class vanishes, an actual positive-degree identity class
vanishes and the previous splitting theorem applies.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Module.DirectLimit.module
variable (G : Type) [Group G] [Countable G]

set_option synthInstance.maxHeartbeats 400000 in
def smallCoefficientGroupIdentity (n : ℕ) : (smallCoefficientTower G).cohomologyStage 0 n :=
  (coefficientNaturalCohomologyIso (normalizedProjectiveResolution (trivialIntegral G))
    ((smallCoefficientTower G).obj n) n).inv (smallCoefficientIdentityClass G n)

set_option synthInstance.maxHeartbeats 400000 in
def smallCoefficientCompletedUnit : (smallCoefficientTower G).Cohomology 0 :=
  Module.DirectLimit.of ℤ ℕ _ ((smallCoefficientTower G).forward 0) 0
    (smallCoefficientGroupIdentity G 0)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanTiledProbeChains
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous actual chains for the three tiled probe sheets -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric
open scoped Manifold Pointwise

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (C : Set (H →ₗ[ℝ] ℝ))
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]

set_option maxHeartbeats 1000000 in
/-- The joint sampler data, packaged before specializing the templates.
This keeps dependent elimination small at the polar-template application. -/
structure TiledProbeChainData
    (ExpI : M.coneWordIdeal C → I)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (β : Fin 3 → M.ConeIdealBases C)
    (ambient : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    (φ : ℕ → I ≃ₜ* I) (ι : I →* F.N.carrier)
    (tiles : ℕ → ℕ) (anchor : ∀ n, Fin (tiles n) → I) where
  bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
    ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)
  lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → cartanRootIdeal H
  index : ∀ n, M.coneIdealBox C ExpI
    ((M.supportIn T hunimod eW).weightSupport (E 0)) (β 0) (scale n) 1 → Fin (tiles n)
  probe : ∀ n, Fin 3 →
    (closedBall (0 : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1) ×
      (M.coneIdealBox C ExpI ((M.supportIn T hunimod eW).weightSupport (E 0))
        (β 0) (scale n) 1) → F.N.carrier
  lifts : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j
  index_measurable : ∀ n, Measurable (index n)
  probe_measurable : ∀ n j, Measurable (probe n j)
  chains : ∀ j, Nonempty (M.BoxProbeChains T F hunimod eW bN (E j) ambient t scale
    (fun n => probe n j))
  first : ∀ n y, probe n 0 y = ι y.2.val * F.ExpN (F.N.equiv
    (quotientLinearSection (M.coneWordIdeal C) bQ lift (bQ.equivFun.symm y.1.val)))
  second : ∀ n y, probe n 1 y = ι ((φ n).symm (anchor n (index n y.2)))
  third : ∀ n y, probe n 2 y = ι ((φ n).symm ((anchor n (index n y.2))⁻¹ * y.2.val))

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPolarTiledSamplers
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counted polar samplers from the actual inside-letter flow -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric Filter MeasureTheory
open scoped Manifold Pointwise Topology

variable {EG G W EI I A : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (K : ProperCone ℝ (StrongDual ℝ W))
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]
  [NormedAddCommGroup EI] [NormedSpace ℝ EI] [FiniteDimensional ℝ EI]
  [ChartedSpace EI I] [LieGroup (𝓘(ℝ, EI)) ⊤ I] [SimplyConnectedSpace I] [T2Space I]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "C" => heightConePreimage T eW K

set_option maxHeartbeats 1000000 in
/-- A single source partition retains its exact count and all three actual
samplers. The logarithmic chain coordinates are supplied by the proved box
construction, not chosen as additional input. -/
structure PolarTiledSamplerData
    (ExpI : M.coneWordIdeal C → I) (ι : I →* F.N.carrier)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (ε : ℝ) (β : M.ConeIdealBases C) (R : ℝ) (scale : ℕ → ℝ)
    (φ : ℕ → I ≃ₜ* I) where
  tiles : ℕ → ℕ
  anchor : ∀ n, Fin (tiles n) → I
  tile : ∀ n, Fin (tiles n) → Set I
  measurable : ∀ n j, MeasurableSet (tile n j)
  disjoint : ∀ n, Pairwise (fun j l => Disjoint (tile n j) (tile n l))
  cover : ∀ n, (⋃ j, tile n j) = M.coneIdealBox C ExpI
    ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 0)) β (scale n) 1
  reverse_anchor : ∀ n j, (φ n).symm (anchor n j) ∈ M.coneIdealBox C ExpI
    ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 1)) β (scale n) 1
  small_tile : ∀ n j, tile n j ⊆ anchor n j • ((φ n) '' M.coneIdealBox C ExpI
    ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 2)) β (scale n) R)
  count : ∀ n, (tiles n : ℝ) ≤ R ^ finrank ℝ (M.coneWordIdeal C) * Real.exp (scale n *
    ((ε / 3) * ∑ l, M.coneIdealWordCost C (M.polarProbeWidths T hunimod eW K) (β.val l)))
  ambient : M.Bases
  chain : M.TiledProbeChainData T F hunimod eW C ExpI bN
    (normalizedPolarTemplates K ε) (fun _ => β) ambient
    (fun i => ε * M.polarProbeWidths T hunimod eW K i) scale φ ι tiles anchor

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanTiledSourceCell
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The counted samplers on the original quotient/kernel probability cell -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric
open scoped Manifold Pointwise

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (C : Set (H →ₗ[ℝ] ℝ))
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]


variable
    (ExpI : M.coneWordIdeal C → I)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (β : Fin 3 → M.ConeIdealBases C)
    (ambient : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    (φ : ℕ → I ≃ₜ* I) (ι : I →* F.N.carrier)
    (tiles : ℕ → ℕ) (anchor : ∀ n, Fin (tiles n) → I)
    (D : M.TiledProbeChainData T F hunimod eW C ExpI bN E β ambient t scale φ ι tiles anchor)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (πQ : F.N.carrier →* Q.carrier)
    (hι : Topology.IsClosedEmbedding ι) (hrange : range ι = (πQ.ker : Set F.N.carrier))

set_option maxHeartbeats 1000000 in
/-- The actual quotient chart associated to the section retained by the tiles. -/
def TiledProbeChainData.sourceQuotientCoordinates :
    (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) ≃ₜ Q.carrier :=
  (D.bQ.equivFun.symm.trans Q.equiv.toLinearEquiv).toContinuousLinearEquiv.toHomeomorph.trans chartQ

set_option maxHeartbeats 1000000 in
/-- The tile construction's fixed linear section as a continuous group section. -/
def TiledProbeChainData.sourceSection : C(Q.carrier, F.N.carrier) :=
  exponentialQuotientSection (M.coneWordIdeal C) D.bQ D.lift
    F.N.equiv.toLinearEquiv Q.equiv.toLinearEquiv chartN chartQ

set_option maxHeartbeats 1000000 in
/-- The fixed quotient part of the original source probability cell. -/
def TiledProbeChainData.sourceQuotientCell : Set Q.carrier :=
  (TiledProbeChainData.sourceQuotientCoordinates (T := T) (M := M) (F := F)
    (hunimod := hunimod) (eW := eW) (C := C) (ExpI := ExpI) (bN := bN)
    (E := E) (β := β) (ambient := ambient) (t := t) (scale := scale)
    (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D)
    (Q := Q) (chartQ := chartQ)) ''
      closedBall (0 : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1

set_option maxHeartbeats 1000000 in
/-- Reparametrization uses the actual Haar product cell, so the selected
probability measure can be chosen there before concentration is applied. -/
def TiledProbeChainData.sourceCoordinates (n : ℕ) :=
  sectionProbeCoordinates
    (TiledProbeChainData.sourceQuotientCoordinates (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
      (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
      (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ))
    (kernelRealization πQ ι hι hrange).toHomeomorph
    (closedBall (0 : Fin (finrank ℝ
      (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1)
    (M.coneIdealBox C ExpI ((M.supportIn T hunimod eW).weightSupport (E 0))
      (β 0) (scale n) 1)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_DerivationLieSpace
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual tangent algebra of the derivation extension

The type synonym keeps exponential group coordinates distinct from the raw
semidirect group on the product vector space.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

instance derivationLieSpaceRealNormed
    (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap) :
    RealNormedLieAlgebra (DerivationLieSpace D hD) := by
  let := derivationSemidirectGroup D hD
  let := derivationSemidirectLieGroup D hD
  let T := GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ)
  let lr : LieRing (L × ℝ) := inferInstanceAs (LieRing T)
  let la : @LieAlgebra ℝ (L × ℝ) _ lr := inferInstanceAs (LieAlgebra ℝ T)
  change RealNormedLieAlgebra (L × ℝ)
  exact { (inferInstance : NormedAddCommGroup (L × ℝ)), lr,
    (inferInstance : NormedSpace ℝ (L × ℝ)), la with }

instance derivationLieSpaceFiniteDimensional
    (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap) :
    FiniteDimensional ℝ (DerivationLieSpace D hD) :=
  inferInstanceAs (FiniteDimensional ℝ (L × ℝ))

def derivationLieSpaceSplit (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap) :
    DerivationLieSpace D hD ≃ₗ[ℝ] L × ℝ := LinearEquiv.refl ℝ (L × ℝ)

def derivationNilpotentLieModel
    (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap) :
    NilpotentLieModel (DerivationLieSpace D hD) := by
  let := derivationSemidirectGroup D hD
  let := derivationSemidirectLieGroup D hD
  let : MeasurableSpace (L × ℝ) := borel (L × ℝ)
  let : BorelSpace (L × ℝ) := ⟨rfl⟩
  let V := L × ℝ
  exact {
    modelSpace := V
    carrier := V
    equiv := LieEquiv.refl }

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothPolynomialAutomorphisms
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The subgroup of smooth automorphisms of a polynomial Lie group -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

def smoothPolynomialAutomorphisms : Subgroup (MulAut L) where
  carrier := {A | ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ A ∧
    ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ A.symm}
  one_mem' := ⟨contMDiff_id, contMDiff_id⟩
  mul_mem' := by
    intro A B hA hB
    exact ⟨hA.1.comp hB.1, hB.2.comp hA.2⟩
  inv_mem' := by
    intro A hA
    exact ⟨hA.2, hA.1⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_DerivationSolvableModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The solvable real model of a nilpotent derivation extension -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group.IsSolvable L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

def derivationSolvableLieModel : SimplyConnectedSolvableLieModel := by
  let g : Group (L × ℝ) := derivationSemidirectGroup D hD
  let : Mul (L × ℝ) := g.toMul
  let : One (L × ℝ) := g.toOne
  let : Monoid (L × ℝ) := g.toMonoid
  let : MulOneClass (L × ℝ) := g.toMulOneClass
  let : Group (L × ℝ) := g
  let : LieGroup (𝓘(ℝ, L × ℝ)) ⊤ (L × ℝ) := derivationSemidirectLieGroup D hD
  let e : (L × ℝ) ≃* (L ⋊[P.derivationAction D hD] Multiplicative ℝ) :=
    { derivationSemidirectEquiv D hD with map_mul' := fun _ _ => rfl }
  let : Group.IsSolvable (L ⋊[P.derivationAction D hD] Multiplicative ℝ) :=
    semidirect_solvable _
  let : Group.IsSolvable (L × ℝ) :=
    @Group.isSolvable_of_isSolvable_injective (L × ℝ)
      (L ⋊[P.derivationAction D hD] Multiplicative ℝ)
      g inferInstance e.toMonoidHom e.injective inferInstance
  exact { modelSpace := L × ℝ, carrier := L × ℝ }

def derivationModelEquiv : (derivationSolvableLieModel D hD).carrier ≃*
    (L ⋊[P.derivationAction D hD] Multiplicative ℝ) :=
  { derivationSemidirectEquiv D hD with map_mul' := fun _ _ => rfl }

attribute [local instance] semidirectProductTopology

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilpotentKernelCompletion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Induction data for completing a nilpotent group with a real kernel

The integer grid is required only to lie in the embedded group. The kernel
may already contain real one-parameter groups, so discreteness is not assumed.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {K H : Type} [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [PK : PolynomialExponentialCoordinates K] [Group H]

structure NilpotentKernelCompletion (i : K →* H) where
  carrier : Type
  [normed : RealNormedLieAlgebra carrier]
  [finiteDimensional : FiniteDimensional ℝ carrier]
  [coordinates : PolynomialExponentialCoordinates carrier]
  [nilpotent : LieRing.IsNilpotent carrier]
  embed : H →* carrier
  injective : Function.Injective embed
  kernel_smooth : ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, carrier)) ∞ (embed.comp i)
  dimension : ℕ
  basis : Module.Basis (Fin dimension) ℝ carrier
  parameter : carrier ≃ carrier
  polynomial : IsPolynomialInBasis basis basis parameter
  polynomial_symm : IsPolynomialInBasis basis basis parameter.symm
  integer_grid : ∀ z : Fin dimension → ℤ, ∃ h : H,
    embed h = parameter (basis.equivFun.symm (fun j => (z j : ℝ)))
  extend : ∀ (M : Type) [RealNormedLieAlgebra M] [FiniteDimensional ℝ M]
    [PolynomialExponentialCoordinates M] [LieRing.IsNilpotent M]
    (f : H →* M), ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, M)) ∞ (f.comp i) →
    ∃ φ : carrier →* M, ContMDiff (𝓘(ℝ, carrier)) (𝓘(ℝ, M)) ∞ φ ∧
      ∀ h, φ (embed h) = f h

attribute [instance] NilpotentKernelCompletion.normed
  NilpotentKernelCompletion.finiteDimensional NilpotentKernelCompletion.coordinates
  NilpotentKernelCompletion.nilpotent

namespace NilpotentKernelCompletion

def of_polynomial_kernel [LieRing.IsNilpotent K] :
    NilpotentKernelCompletion (MonoidHom.id K) where
  carrier := K
  embed := MonoidHom.id K
  injective := Function.injective_id
  kernel_smooth := contMDiff_id
  dimension := Module.finrank ℝ K
  basis := Module.finBasis ℝ K
  parameter := Equiv.refl K
  polynomial := IsPolynomialInBasis.linear LinearMap.id
  polynomial_symm := IsPolynomialInBasis.linear LinearMap.id
  integer_grid z := ⟨(Module.finBasis ℝ K).equivFun.symm (fun j => (z j : ℝ)), rfl⟩
  extend _ _ _ _ _ f hf := ⟨f, hf, fun _ => rfl⟩

variable {i : K →* H} (C : NilpotentKernelCompletion i)

/-- The polynomial integer grid determines every smooth homomorphism. -/
theorem hom_ext (M : Type) [RealNormedLieAlgebra M] [FiniteDimensional ℝ M]
    [PM : PolynomialExponentialCoordinates M]
    (φ ψ : C.carrier →* M)
    (hφ : ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, M)) ∞ φ)
    (hψ : ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, M)) ∞ ψ)
    (h : ∀ a, φ (C.embed a) = ψ (C.embed a)) : φ = ψ := by
  let b := Module.finBasis ℝ M
  let f := polynomialModelLieHom φ hφ
  let g := polynomialModelLieHom ψ hψ
  have he : (f.toLinearMap ∘ C.parameter) = (g.toLinearMap ∘ C.parameter) := by
    apply ((IsPolynomialInBasis.linear (b := C.basis) (c := b) f.toLinearMap).comp
      C.polynomial).ext_integer_grid
      ((IsPolynomialInBasis.linear (b := C.basis) (c := b) g.toLinearMap).comp C.polynomial)
    intro z
    obtain ⟨a, ha⟩ := C.integer_grid z
    change f (C.parameter (C.basis.equivFun.symm (fun j => (z j : ℝ)))) =
      g (C.parameter (C.basis.equivFun.symm (fun j => (z j : ℝ))))
    rw [← ha]
    exact (polynomialModelLieHom_apply φ hφ _).trans
      ((h a).trans (polynomialModelLieHom_apply ψ hψ _).symm)
  apply MonoidHom.ext
  intro x
  have hh := congrFun he (C.parameter.symm x)
  change f (C.parameter (C.parameter.symm x)) = g (C.parameter (C.parameter.symm x)) at hh
  rw [C.parameter.apply_symm_apply] at hh
  exact (polynomialModelLieHom_apply φ hφ x).symm.trans
    (hh.trans (polynomialModelLieHom_apply ψ hψ x))

/-- Compatible automorphisms of the original group extend with their inverse. -/
theorem automorphism_extension (a : MulAut H)
    (ha : ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, C.carrier)) ∞
      ((C.embed.comp a.toMonoidHom).comp i))
    (hai : ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, C.carrier)) ∞
      ((C.embed.comp a.symm.toMonoidHom).comp i)) :
    ∃ A : MulAut C.carrier, ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, C.carrier)) ∞ A ∧
      ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, C.carrier)) ∞ A.symm ∧
      ∀ h, A (C.embed h) = C.embed (a h) := by
  obtain ⟨f, hf, hfe⟩ := C.extend C.carrier (C.embed.comp a.toMonoidHom) ha
  obtain ⟨g, hg, hge⟩ := C.extend C.carrier (C.embed.comp a.symm.toMonoidHom) hai
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hfe hge
  have hgf : g.comp f = MonoidHom.id C.carrier := by
    apply C.hom_ext C.carrier (g.comp f) (MonoidHom.id C.carrier) (hg.comp hf) contMDiff_id
    intro h
    change g (f (C.embed h)) = C.embed h
    rw [hfe, hge]
    exact congrArg C.embed (a.symm_apply_apply h)
  have hfg : f.comp g = MonoidHom.id C.carrier := by
    apply C.hom_ext C.carrier (f.comp g) (MonoidHom.id C.carrier) (hf.comp hg) contMDiff_id
    intro h
    change f (g (C.embed h)) = C.embed h
    rw [hge, hfe]
    exact congrArg C.embed (a.apply_symm_apply h)
  let A : MulAut C.carrier :=
    { toFun := f
      invFun := g
      left_inv := fun x => DFunLike.congr_fun hgf x
      right_inv := fun x => DFunLike.congr_fun hfg x
      map_mul' := f.map_mul }
  exact ⟨A, hf, hg, hfe⟩

end NilpotentKernelCompletion
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_KernelCompletionTransport
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting a constructed completion across an exact group isomorphism -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {K H J : Type} [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [PK : PolynomialExponentialCoordinates K] [Group H] [Group J]
  {i : K →* H}

namespace NilpotentKernelCompletion

def of_equiv (C : NilpotentKernelCompletion i) (e : H ≃* J) :
    NilpotentKernelCompletion (e.toMonoidHom.comp i) where
  carrier := C.carrier
  embed := C.embed.comp e.symm.toMonoidHom
  injective := C.injective.comp e.symm.injective
  kernel_smooth := by
    convert C.kernel_smooth using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    exact congrArg C.embed (e.symm_apply_apply (i x))
  dimension := C.dimension
  basis := C.basis
  parameter := C.parameter
  polynomial := C.polynomial
  polynomial_symm := C.polynomial_symm
  integer_grid z := by
    obtain ⟨h, hh⟩ := C.integer_grid z
    refine ⟨e h, ?_⟩
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using hh
  extend M _ _ _ _ f hf := by
    obtain ⟨φ, hφ, he⟩ := C.extend M (f.comp e.toMonoidHom) hf
    refine ⟨φ, hφ, ?_⟩
    intro j
    exact (he (e.symm j)).trans (congrArg f (e.apply_symm_apply j))

end NilpotentKernelCompletion
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_KernelCompletionHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.latticeNormalFlag_normal _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real quotient of a nilpotent kernel completion

The quotient homomorphism extends to the constructed completion. Its kernel
is exactly the original real kernel, by the dimension retained in the cyclic
construction. No exactness property is postulated for the completion.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {K G : Type} [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [PK : PolynomialExponentialCoordinates K] [Group G] {n : ℕ}

def integralRealHeight : IntegralLatticeGroup n →* AbelianRealSpace n where
  toFun z := integerVectorMap n z.toAdd
  map_one' := (integerVectorMap n).map_zero
  map_mul' z w := (integerVectorMap n).map_add z.toAdd w.toAdd

namespace NilpotentKernelCompletion
variable (E : GroupExtension K G (IntegralLatticeGroup n))
  (C : NilpotentKernelCompletion E.inl)

theorem exists_height :
    ∃ π : C.carrier →* AbelianRealSpace n,
      ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, AbelianRealSpace n)) ∞ π ∧
      ∀ g, π (C.embed g) = integralRealHeight (E.rightHom g) := by
  apply C.extend (AbelianRealSpace n) (integralRealHeight.comp E.rightHom)
  have he : (integralRealHeight.comp E.rightHom).comp E.inl =
      (1 : K →* AbelianRealSpace n) := by
    ext x
    simp only [MonoidHom.comp_apply, E.rightHom_inl, map_one, MonoidHom.one_apply]
  rw [he]
  exact contMDiff_const

end NilpotentKernelCompletion
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_KernelCompletionAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_mul _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_on_lattice _root_.OAI.PolycyclicRecognition.NilpotentLatticeCoordinates.automorphism_one _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending an action to the nilpotent completion

Existence comes from the constructed homomorphism extension. Uniqueness on
the integer grid forces the extensions to satisfy the action law.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {K G Q : Type} [RealNormedLieAlgebra K] [FiniteDimensional ℝ K]
  [PK : PolynomialExponentialCoordinates K] [Group G] [Group Q]
  {i : K →* G} (C : NilpotentKernelCompletion i) (ρ : Q →* MulAut G)
  (hρ : ∀ q, ContMDiff (𝓘(ℝ, K)) (𝓘(ℝ, C.carrier)) ∞
    ((C.embed.comp (ρ q).toMonoidHom).comp i))

namespace NilpotentKernelCompletion

include hρ in
theorem action_extension_exists (q : Q) :
    ∃ A : MulAut C.carrier, ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, C.carrier)) ∞ A ∧
      ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, C.carrier)) ∞ A.symm ∧
      ∀ g, A (C.embed g) = C.embed (ρ q g) := by
  apply C.automorphism_extension (ρ q) (hρ q)
  have hi : (ρ q).symm = ρ q⁻¹ := (map_inv ρ q).symm
  rw [hi]
  exact hρ q⁻¹

def extendedAutomorphism (q : Q) : MulAut C.carrier :=
  (C.action_extension_exists ρ hρ q).choose

theorem extendedAutomorphism_smooth (q : Q) :
    ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, C.carrier)) ∞
      (C.extendedAutomorphism ρ hρ q) :=
  (C.action_extension_exists ρ hρ q).choose_spec.1

theorem extendedAutomorphism_embed (q : Q) (g : G) :
    C.extendedAutomorphism ρ hρ q (C.embed g) = C.embed (ρ q g) :=
  (C.action_extension_exists ρ hρ q).choose_spec.2.2 g

def extendedAction : Q →* MulAut C.carrier where
  toFun := C.extendedAutomorphism ρ hρ
  map_one' := by
    apply MulEquiv.toMonoidHom_injective
    apply C.hom_ext C.carrier _ _ (C.extendedAutomorphism_smooth ρ hρ 1) contMDiff_id
    intro g
    rw [MulEquiv.coe_toMonoidHom, C.extendedAutomorphism_embed]
    simp only [map_one, MulAut.one_apply]
    rfl
  map_mul' q r := by
    apply MulEquiv.toMonoidHom_injective
    apply C.hom_ext C.carrier
      (C.extendedAutomorphism ρ hρ (q * r)).toMonoidHom
      ((C.extendedAutomorphism ρ hρ q) * (C.extendedAutomorphism ρ hρ r)).toMonoidHom
      (C.extendedAutomorphism_smooth ρ hρ (q * r))
      ((C.extendedAutomorphism_smooth ρ hρ q).comp
        (C.extendedAutomorphism_smooth ρ hρ r))
    intro g
    change C.extendedAutomorphism ρ hρ (q * r) (C.embed g) =
      C.extendedAutomorphism ρ hρ q (C.extendedAutomorphism ρ hρ r (C.embed g))
    rw [C.extendedAutomorphism_embed, C.extendedAutomorphism_embed,
      C.extendedAutomorphism_embed, map_mul]
    rfl

@[simp] theorem extendedAction_embed (q : Q) (g : G) :
    C.extendedAction ρ hρ q (C.embed g) = C.embed (ρ q g) :=
  C.extendedAutomorphism_embed ρ hρ q g

theorem extendedAction_smooth (q : Q) :
    ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, C.carrier)) ∞ (C.extendedAction ρ hρ q) :=
  C.extendedAutomorphism_smooth ρ hρ q

end NilpotentKernelCompletion
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Lattices_NilpotentExtensionLattice
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.derivationLieSpaceFiniteDimensional _root_.OAI.PolycyclicRecognition.derivationLieSpaceRealNormed _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform lattice after completing only the nilpotent kernel

The quotient is still discrete. This is an intermediate construction, not a
claim that the resulting group is connected.
-/

noncomputable section
namespace PolycyclicRecognition.NilpotentLatticeCoordinates
open Set
open scoped Manifold
variable {N G Q : Type} [Group N] [Group G] [Group Q]
  [TopologicalSpace Q] [DiscreteTopology Q]
  (C : NilpotentLatticeCoordinates N) (S : GroupExtension N G Q)
  (σ : S.Section) (hσ : σ 1 = 1)
attribute [local instance] factorExtensionTopology

def completedExtensionLattice : Subgroup (FactorExtension (C.extensionFactorSystem S σ hσ)) :=
  (C.extensionEmbedding S σ hσ).range

/-- The lattice is isomorphic to the original group, not a quotient by its center. -/
def completedExtensionLatticeEquiv : G ≃* C.completedExtensionLattice S σ hσ :=
  MonoidHom.ofInjective (C.extensionEmbedding_injective S σ hσ)

end PolycyclicRecognition.NilpotentLatticeCoordinates

end

end OAI
end


