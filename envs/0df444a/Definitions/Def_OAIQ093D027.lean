-- Prove2me | Definitions.Def_OAIQ093D027
-- name    : OAIQ093D027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-02T18:28:46.402637+00:00
-- url     : https://prove2.me/theorems/4487a15a-2396-47cf-acb0-e19608b5c26f
-- title:
--   Definitions bundle OAIQ093D027 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 40 declarations of OpenAI's Lean: 17 definitions, 3 inductive types or structures and 20 theorems. The definitions and types are `OAI.PolycyclicRecognition.CartanWordModel.ConeGroupMeasures`, `OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone`, `OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.kernelMeasure`, `OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.sectionMeasure`, `OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.withQuotientHaar`, `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeBoxData`, `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.sourceKernelCell`, `OAI.PolycyclicRecognition.CartanWordModel.adjointGroupAutomorphism`, `OAI.PolycyclicRecognition.CartanWordModel.coneAdjointAutomorphism`, `OAI.PolycyclicRecognition.CartanWordModel.coneCartanSubmodule`, `OAI.PolycyclicRecognition.CartanWordModel.coneIdealInnerAutomorphism`, `OAI.PolycyclicRecognition.CartanWordModel.coneIdealInnerDerivation`, `OAI.PolycyclicRecognition.CartanWordModel.coneIdealLetterAdjoint`, `OAI.PolycyclicRecognition.CartanWordModel.coneIdealLetterAutomorphism`, `OAI.PolycyclicRecognition.CartanWordModel.coneIdealLetterFlow`, `OAI.PolycyclicRecognition.CartanWordModel.groupWeightDilation`, `OAI.PolycyclicRecognition.CartanWordModel.sourceDilation`, `OAI.PolycyclicRecognition.ComplexTriangularAdjoint.kernelComponent`, `OAI.PolycyclicRecognition.ComplexWeightFactorModel.kernelParameter`, `OAI.PolycyclicRecognition.cartanIdealAdjointAutomorphism`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `PolycyclicRecognition_Algebra_CommonSemisimpleCentralizer`, `PolycyclicRecognition_Algebra_ComplexFactorLocalChart`, `PolycyclicRecognition_Algebra_ComplexFactorParameters`, `PolycyclicRecognition_Algebra_ConeIdealInnerAutomorphism`, `PolycyclicRecognition_Algebra_ConeIdealStrictWidth`, `PolycyclicRecognition_Algebra_ConeQuotientAutomorphism`, `PolycyclicRecognition_Algebra_ConeQuotientJacobian`, `PolycyclicRecognition_Algebra_MixedWordIdeal`, `PolycyclicRecognition_Algebra_UnconditionalNilpotentCoordinates`, `PolycyclicRecognition_Analysis_ConeIdealInnerHaar`, `PolycyclicRecognition_Analysis_ConeKernelHaar`, `PolycyclicRecognition_Analysis_MixedWordBoxModel`, `PolycyclicRecognition_Geometry_CartanActualConjugation`, `PolycyclicRecognition_Geometry_CartanAdjointAction`, `PolycyclicRecognition_Geometry_CartanBoxDilation`, `PolycyclicRecognition_Geometry_CartanConeGroup`, `PolycyclicRecognition_Geometry_CartanConeIdeal`, `PolycyclicRecognition_Geometry_CartanConeInvariance`, `PolycyclicRecognition_Geometry_CartanConeTrace`, `PolycyclicRecognition_Geometry_CartanMeasuredCone`, `PolycyclicRecognition_Geometry_CartanMeasuredConeCells`, `PolycyclicRecognition_Geometry_CartanMeasuredConeHaar`, `PolycyclicRecognition_Geometry_CartanSourceDilation`, `PolycyclicRecognition_Geometry_CartanTiledProbeBoxes`, `PolycyclicRecognition_Geometry_CartanTiledSourceCell`, `PolycyclicRecognition_Geometry_ConeIdealFlowTiling`, `PolycyclicRecognition_Geometry_ConeIdealInsideAdjoint`, `PolycyclicRecognition_Geometry_PolynomialExponentialCoordinates`.
--
--   **Imports.** It imports the published bundle `Def_PolycyclicRecognition`; the bundles `OAIQ093D017`, `OAIQ093D018` and `OAIQ093D019` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ093D021` and `OAIQ093D022`; the statements `OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.polar_offset_nonpos`, `OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.action_preserves_sectionMeasure`, `OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.exists_canonical_polar_samplers`, `OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.exists_uniform_polar_target_regions`, `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.measured_target_offset_nonpos`, `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.original_box_law_offset_nonpos`, `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.source_probability_data`, `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.source_section_rightInverse`, `OAI.PolycyclicRecognition.CartanWordModel.centered_ray_quotient_compact_limits`, `OAI.PolycyclicRecognition.CartanWordModel.continuous_bounded_ray_quotient_limits`, `OAI.PolycyclicRecognition.CartanWordModel.exists_boundary_family_with_compact_shadow`, `OAI_PolycyclicRecognition_CartanWordModel_exists_coarse_path_polynomial_packing`, `OAI.PolycyclicRecognition.CartanWordModel.exists_controlled_profile_quotient_restriction`, `OAI.PolycyclicRecognition.CartanWordModel.exists_invertible_height_factor_of_stationary_mean`, `OAI.PolycyclicRecognition.CartanWordModel.exists_metric_cartan_factor_bound`, `OAI.PolycyclicRecognition.CartanWordModel.exists_normalized_polar_samplers`, `OAI.PolycyclicRecognition.CartanWordModel.exists_one_cone_offset_threshold`, `OAI.PolycyclicRecognition.CartanWordModel.exists_polar_tiled_probe_chains_from_box`, `OAI_PolycyclicRecognition_CartanWordModel_exists_sequence_profile_endpoint_lifts`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_intrinsic_bridge_lifts`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_measured_probe_regions`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_polar_offset_threshold`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_profile_bridge_restrictions_of_basis`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_sequence_metric_factor_bounds`, `OAI.PolycyclicRecognition.CartanWordModel.ideal_fiber_quotient_difference_tendsto_one`, `OAI.PolycyclicRecognition.CartanWordModel.increments_tendsto_template_labels_of_invariant_probability`, `OAI.PolycyclicRecognition.CartanWordModel.negative_chain_quotient_difference_tendsto_one`, `OAI.PolycyclicRecognition.CartanWordModel.segmentSupport_le_of_stationary_mean` and `OAI.PolycyclicRecognition.CartanWordModel.templateSupport_le_of_stationary_height_factor`; the proofs of `OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.polar_offset_nonpos`, `OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.action_preserves_sectionMeasure`, `OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.exists_canonical_polar_samplers`, `OAI.PolycyclicRecognition.CartanWordModel.MeasuredCone.exists_uniform_polar_target_regions`, `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.count_le_offset_rate`, `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.measured_target_offset_nonpos`, `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.source_probability_data`, `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.source_section_rightInverse`, `OAI.PolycyclicRecognition.CartanWordModel.cartan_normal_occupation_error_tendsto_zero`, `OAI.PolycyclicRecognition.CartanWordModel.cartan_profile_increment_mem_template_sequence`, `OAI.PolycyclicRecognition.CartanWordModel.centered_ray_quotient_compact_limits`, `OAI.PolycyclicRecognition.CartanWordModel.continuous_bounded_ray_quotient_limits`, `OAI.PolycyclicRecognition.CartanWordModel.exists_boundary_family_with_compact_shadow`, `OAI_PolycyclicRecognition_CartanWordModel_exists_coarse_path_polynomial_packing`, `OAI.PolycyclicRecognition.CartanWordModel.exists_controlled_increment_volume`, `OAI.PolycyclicRecognition.CartanWordModel.exists_controlled_profile_quotient_restriction`, `OAI_PolycyclicRecognition_CartanWordModel_exists_coupled_target_tuples`, `OAI.PolycyclicRecognition.CartanWordModel.exists_invertible_height_factor_of_stationary_mean`, `OAI.PolycyclicRecognition.CartanWordModel.exists_metric_basepoint_sampling_geometry`, `OAI.PolycyclicRecognition.CartanWordModel.exists_metric_cartan_factor_bound`, `OAI.PolycyclicRecognition.CartanWordModel.exists_normalized_polar_samplers`, `OAI.PolycyclicRecognition.CartanWordModel.exists_polar_tiled_probe_chains_from_box`, `OAI.PolycyclicRecognition.CartanWordModel.exists_sequence_path_tuple_lifts`, `OAI_PolycyclicRecognition_CartanWordModel_exists_sequence_profile_endpoint_lifts`, `OAI.PolycyclicRecognition.CartanWordModel.exists_small_metric_log_chart_shift`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_intrinsic_bridge_lifts`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_measured_probe_regions`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_neighbor_label_threshold`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_polar_offset_threshold`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_profile_bridge_restrictions_of_basis`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_basepoint_comparison`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_sequence_metric_factor_bounds`, `OAI.PolycyclicRecognition.CartanWordModel.ideal_fiber_quotient_difference_tendsto_one`, `OAI.PolycyclicRecognition.CartanWordModel.increments_tendsto_template_labels_of_invariant_probability`, `OAI.PolycyclicRecognition.CartanWordModel.negative_chain_quotient_difference_tendsto_one`, `OAI.PolycyclicRecognition.CartanWordModel.segmentSupport_le_of_stationary_mean`, `OAI.PolycyclicRecognition.CartanWordModel.source_target_product_exponent_le`, `OAI.PolycyclicRecognition.CartanWordModel.templateSupport_le_of_recurrent_segment_cells_sequence`, `OAI.PolycyclicRecognition.CartanWordModel.templateSupport_le_of_stationary_height_factor`, `OAI.PolycyclicRecognition.CartanWordModel.terminal_product_exponent_le` and `OAI.PolycyclicRecognition.exists_uniform_sampled_contact_bridge`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D017
import Definitions.Def_OAIQ093D018
import Definitions.Def_OAIQ093D019

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PolynomialExponentialCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.analyticDerivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.derivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.groupAutomorphism_apply _root_.OAI.PolycyclicRecognition.abelianRealLatticeEquiv_apply _root_.OAI.PolycyclicRecognition.analyticDerivationExp_apply _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.polynomialCoordinateHom_apply _root_.OAI.PolycyclicRecognition.polynomialInnerLieEquiv_apply _root_.OAI.PolycyclicRecognition.polynomialModelLieEquiv_apply _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial group coordinates on a nilpotent algebra

Transport an existing model through its global exponential chart. The finite
BCH law makes the transported operations analytic. Its actual tangent bracket
is identified by differentiating the chart as a group homomorphism.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

attribute [instance] PolynomialExponentialCoordinates.group

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

theorem polynomialExponentialCoordinates_of_model
    (N : NilpotentLieModel L) (hnil : LieRing.IsNilpotent L)
    (dynkin : NilpotentDynkinExpansionInput N.modelSpace N.carrier) :
    Nonempty (PolynomialExponentialCoordinates L) := by
  let E := N.modelSpace
  let G := N.carrier
  let T := GroupLieAlgebra (𝓘(ℝ, E)) G
  let : NormedAddCommGroup T := by change NormedAddCommGroup E; exact inferInstance
  let : NormedSpace ℝ T := by change NormedSpace ℝ E; exact inferInstance
  let Exp : T → G := groupExponential
  have hExp : IsGroupExponential Exp := groupExponential_isGroupExponential
  have hn : LieRing.IsNilpotent T := N.tangent_nilpotent hnil
  obtain ⟨chart, hchart⟩ := nilpotentGlobalExponentialChart_of_dynkin dynkin Exp hExp hn
  let C : L ≃ₜ G := N.equiv.toLinearEquiv.toContinuousLinearEquiv.toHomeomorph.trans chart
  have hC (x : L) : C x = Exp (N.equiv x) := hchart _
  let : Group L := C.toEquiv.group
  have hmul (x y : L) : C (x * y) = C x * C y := C.apply_symm_apply _
  have hone : (1 : L) = 0 := by
    apply C.injective
    rw [show C 1 = (1 : G) from C.apply_symm_apply _]
    rw [hC, map_zero, hExp.map_zero]
  have hinv (x : L) : x⁻¹ = -x := by
    apply C.injective
    rw [show C (x⁻¹) = (C x)⁻¹ from C.apply_symm_apply _]
    rw [hC x, hC (-x), map_neg, hExp.map_neg]
  obtain ⟨c, hc⟩ := (LieModule.isNilpotent_iff ℝ T T).mp hn
  obtain ⟨coeff, _, hprod⟩ := dynkin Exp hExp c hc 2
  have hpoly (x y : L) : x * y = finiteDynkinPolynomial coeff ![x, y] := by
    apply C.injective
    rw [hmul, hC, hC, hC]
    have he := finiteDynkinPolynomial_map N.equiv.toLieHom coeff ![x, y]
    change N.equiv (finiteDynkinPolynomial coeff ![x, y]) = _ at he
    rw [he]
    have hX : (fun i => N.equiv.toLieHom (![x, y] i)) = ![N.equiv x, N.equiv y] := by
      funext i
      fin_cases i <;> rfl
    rw [hX]
    have hp := hprod ![N.equiv x, N.equiv y]
    simpa only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
      mul_one, Matrix.cons_val_zero, Matrix.cons_val_succ] using hp
  let : LieGroup (𝓘(ℝ, L)) ⊤ L :=
    { toIsManifold := inferInstance
      contMDiff_mul := by
        have hp : ContDiff ℝ ⊤ (fun p : L × L =>
            finiteDynkinPolynomial coeff ![p.1, p.2]) := by
          apply contDiff_normed_finiteDynkinPolynomial
          intro i
          fin_cases i
          · exact contDiff_fst
          · exact contDiff_snd
        have heq : (fun p : L × L => p.1 * p.2) =
            (fun p : L × L => finiteDynkinPolynomial coeff ![p.1, p.2]) := by
          funext p; exact hpoly _ _
        rw [heq]
        exact hp.comp_contMDiff (contMDiff_fst.prodMk_space contMDiff_snd)
      contMDiff_inv := by
        have heq : (fun x : L => x⁻¹) = fun x : L => -x := funext hinv
        rw [heq]
        exact contDiff_neg.contMDiff }
  have hidentity : IsGroupExponential (fun x : GroupLieAlgebra (𝓘(ℝ, L)) L => (x : L)) := by
    refine ⟨hone.symm, ?_, ?_⟩
    · intro v s t
      apply C.injective
      have hmap (w : L) (r u : ℝ) : C ((r + u) • w) = C (r • w * u • w) := by
        rw [hmul, hC, hC, hC, map_smul, map_smul, map_smul]
        exact hExp.map_add_smul _ _ _
      exact hmap (show L from v) s t
    · intro v
      have hd := ((hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const (show L from v)).hasMFDerivAt
      exact hd
  let φ : L →* G :=
    { C.toEquiv with
      map_one' := C.apply_symm_apply _
      map_mul' := hmul }
  have hcompat (v : L) : φ v = Exp (N.equiv v) := hC v
  have hφ := contMDiff_of_exponential_compatibility hidentity hExp φ C.continuous
    N.equiv.toLinearMap hcompat
  have hdiff (v : L) : homLieDifferential φ hφ v = N.equiv v :=
    mfderiv_eq_of_exponential_compatibility hidentity hExp φ
      (hφ.mdifferentiable (by simp)) N.equiv.toLinearMap hcompat v
  let f := N.equiv.symm.toLieHom.comp (homLieDifferential φ hφ)
  have hf (v : GroupLieAlgebra (𝓘(ℝ, L)) L) : f v = (v : L) := by
    change N.equiv.symm (homLieDifferential φ hφ v) = v
    exact (congrArg N.equiv.symm (hdiff (v : L))).trans (N.equiv.symm_apply_apply (v : L))
  let e := LieEquiv.ofBijective f
    ⟨fun x y h => by exact (hf x).symm.trans (h.trans (hf y)), fun y => ⟨y, hf y⟩⟩
  refine ⟨{ group := inferInstance
            lieGroup := inferInstance
            one_eq_zero := hone
            inv_eq_neg := hinv
            degree := c
            coefficients := coeff
            mul_eq := hpoly
            tangentEquiv := e.symm
            tangentEquiv_apply := ?_ }⟩
  intro x
  have he := e.apply_symm_apply x
  change f (e.symm x) = x at he
  exact (hf (e.symm x)).symm.trans he

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CommonSemisimpleCentralizer
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.starSubalgebraCommCStarAlgebra

namespace OAI

/-! # Common semisimple centralizers in the completed extension -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff IsMulCommutative
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q]

omit [LieRing.IsNilpotent L] in
theorem mem_semisimpleActionCentralizer_iff (E : GroupExtension L G Q)
    (S : L ≃ₗ⁅ℝ⁆ L) (g : G)
    (hg : ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)) :
    g ∈ semisimpleActionCentralizer E S ↔
      Commute S.toLinearMap (polynomialModelLieEquiv (E.conjAct g) hg).toLinearMap := by
  let B := polynomialModelLieEquiv (E.conjAct g) hg
  have hb (x : L) : B x = E.conjAct g x := polynomialModelLieEquiv_apply _ _ x
  change E.conjAct g ∈
    Subgroup.centralizer {PolynomialExponentialCoordinates.groupAutomorphism (P := C) S} ↔ _
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    have hh := congrArg (fun f : MulAut L => f x) h
    change E.conjAct g (S x) = S (E.conjAct g x) at hh
    change S (B x) = B (S x)
    rw [hb, hb]
    exact hh.symm
  · intro h
    apply DFunLike.ext
    intro x
    have hh : S (B x) = B (S x) := LinearMap.congr_fun h.eq x
    rw [hb, hb] at hh
    exact hh.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ComplexFactorParameters
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear parameters for the two actual complex-weight factors -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

namespace ComplexTriangularAdjoint

def kernelComponent : L →ₗ[ℝ] T.kernelIdeal :=
  (LinearMap.id - H.subtype.comp (T.cartanComponent H)).codRestrict
    T.kernelIdeal.toSubmodule (fun x => by
      change T.weightMap (x - (T.cartanComponent H x : L)) = 0
      rw [map_sub,T.cartanComponent_weight H,sub_self])

end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UnconditionalNilpotentCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.abelianRealCoordinates _root_.OAI.PolycyclicRecognition.abelianRealFiniteDimensional _root_.OAI.PolycyclicRecognition.abelianRealLieAbelian _root_.OAI.PolycyclicRecognition.abelianRealNormedLie _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.polynomialLieIdealSubgroup_normal _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial nilpotent models by dimension induction

At each successor step, the ideal already has polynomial coordinates. A
faithful representation of its semidirect extension proves that extension's
finite product law, from which its own exponential coordinates are constructed.
-/

noncomputable section
namespace PolycyclicRecognition

open Module

set_option backward.isDefEq.respectTransparency false in
theorem polynomialExponentialCoordinates_nilpotent
    (L : Type) [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
    (hnil : LieRing.IsNilpotent L) : Nonempty (PolynomialExponentialCoordinates L) := by
  have hmain : ∀ n : ℕ, ∀ (A : Type) [RealNormedLieAlgebra A] [FiniteDimensional ℝ A],
      finrank ℝ A = n → LieRing.IsNilpotent A → Nonempty (PolynomialExponentialCoordinates A) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A _ _ hdim hA
      let : LieRing.IsNilpotent A := hA
      by_cases hs : Subsingleton A
      · let := hs
        let N := abelianLieModel (V := A)
        let _ : CommGroup N.carrier := inferInstanceAs (CommGroup (Multiplicative A))
        exact polynomialExponentialCoordinates_of_model N hA
          (nilpotentDynkinExpansionInput_of_comm (E := N.modelSpace) (G := N.carrier))
      · let : Nontrivial A := not_subsingleton_iff_nontrivial.mp hs
        obtain ⟨C⟩ := exists_nilpotentCodimensionOneData (L := A)
        let := C.normedIdeal
        have hsmaller : finrank ℝ C.ideal < n := by
          rw [← hdim]
          exact C.finrank_ideal_lt
        obtain ⟨P⟩ := ih (finrank ℝ C.ideal) hsmaller C.ideal rfl C.ideal_nilpotent
        exact polynomialCoordinates_extend_ideal C P
  exact hmain (finrank ℝ L) L rfl hnil

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_MixedWordIdeal
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mixed-word ideal used by the cone quotients -/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- A derivation preserves the mixed-word ideal as soon as it sends each
outside generator into that ideal. This is the Cartan-invariance reduction. -/
theorem derivation_preserves_mixedWordIdeal
    (X : I → L) (outside : I → Prop)
    (hgen : LieSubalgebra.lieSpan ℝ L (range X) = ⊤)
    (D : L →ₗ[ℝ] L)
    (hD : ∀ x y, D ⁅x, y⁆ = ⁅D x, y⁆ + ⁅x, D y⁆)
    (hout : ∀ i, outside i → D (X i) ∈ mixedWordIdeal X outside hgen)
    (v : L) (hv : v ∈ mixedWordIdeal X outside hgen) :
    D v ∈ mixedWordIdeal X outside hgen := by
  let J := mixedWordIdeal X outside hgen
  change D v ∈ J.toSubmodule
  have hw (w : FreeMagma I) (hm : IsMixedWord outside w) : D (evalBracketWord X w) ∈ J := by
    induction w using FreeMagma.rec with
    | of i => exact hout i hm
    | mul u v hu hv =>
      change D ⁅evalBracketWord X u, evalBracketWord X v⁆ ∈ J
      rw [hD]
      rcases hm with hm | hm
      · exact J.add_mem (lie_mem_left ℝ L J _ _ (hu hm))
          (lie_mem_left ℝ L J _ _ (eval_mixed_mem_span X outside hm))
      · exact J.add_mem (J.lie_mem (eval_mixed_mem_span X outside hm))
          (J.lie_mem (hv hm))
  change v ∈ mixedWordSpan X outside at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w, hw', rfl⟩ := hv
    exact hw w hw'
  | zero => simpa only [map_zero] using J.toSubmodule.zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using J.add_mem hx hy
  | smul r x _ hx => simpa only [map_smul] using J.smul_mem r hx

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanConeIdeal
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mixed-word ideal contains every outside generalized weight space -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set

namespace CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

set_option maxHeartbeats 1000000 in
/-- Homogeneous word bases show that every generalized weight space outside
an additively closed cone is contained in the mixed-word ideal. -/
theorem outside_genWeightSpace_le_coneWordIdeal
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (φ : H →ₗ[ℝ] ℝ) (hφ : φ ∉ C) :
    (genWeightSpace (cartanRootIdeal H) φ).toSubmodule ≤ (M.coneWordIdeal C).toSubmodule := by
  classical
  by_cases hz : genWeightSpace (cartanRootIdeal H) φ = ⊥
  · rw [hz]
    exact bot_le
  let α : Weight ℝ H (cartanRootIdeal H) := ⟨φ, hz⟩
  let β : M.Bases := Classical.choice inferInstance
  let b := WordBasisSelections.basis M.letter M.wordList β
  let χ := fun i => (M.weight i : H →ₗ[ℝ] ℝ)
  have hm (j : Fin (finrank ℝ (cartanRootIdeal H))) :
      b j ∈ genWeightSpace (cartanRootIdeal H) (bracketWordWeight χ (β.val j)) := by
    rw [← WordBasisSelections.eval_words M.letter M.wordList β j]
    exact cartan_word_mem_genWeight H M.letter M.weight M.letter_root (β.val j)
  let ψ : Fin (finrank ℝ (cartanRootIdeal H)) → Weight ℝ H (cartanRootIdeal H) := fun j =>
    { toFun := bracketWordWeight χ (β.val j)
      genWeightSpace_ne_bot' := by
        intro hj
        have h := hm j
        rw [hj] at h
        exact b.ne_zero j h }
  have hψ j : (ψ j : H →ₗ[ℝ] ℝ) = bracketWordWeight χ (β.val j) := by ext h; rfl
  have ha : (α : H →ₗ[ℝ] ℝ) = φ := by ext h; rfl
  have hspan := genWeightSpace_le_span_basis_by_weight b ψ hm
    (fun γ => (γ : H →ₗ[ℝ] ℝ) ∉ C) α (by rwa [ha])
  apply hspan.trans
  apply Submodule.span_le.mpr
  rintro _ ⟨j, hj, rfl⟩
  have hmix : IsMixedWord (fun i => χ i ∉ C) (β.val j) := by
    by_contra hn
    have hc := bracketWordWeight_mem_of_pure χ C hadd (β.val j) hn
    exact hj (by rwa [hψ])
  rw [← WordBasisSelections.eval_words M.letter M.wordList β j]
  exact eval_mixed_mem_span M.letter (fun i => χ i ∉ C) hmix

set_option maxHeartbeats 1000000 in
/-- The mixed ideal is invariant under the full Cartan action, including
its generalized-eigenvector corrections. -/
theorem coneWordIdeal_cartan_invariant
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (h : H) (v : cartanRootIdeal H) (hv : v ∈ M.coneWordIdeal C) :
    ⁅h, v⁆ ∈ M.coneWordIdeal C := by
  let D := toEnd ℝ H (cartanRootIdeal H) h
  have hD (x y : cartanRootIdeal H) : D ⁅x, y⁆ = ⁅D x, y⁆ + ⁅x, D y⁆ := by
    apply Subtype.ext
    change ⁅(h : L), ⁅(x : L), (y : L)⁆⁆ =
      ⁅⁅(h : L), (x : L)⁆, (y : L)⁆ + ⁅(x : L), ⁅(h : L), (y : L)⁆⁆
    exact leibniz_lie _ _ _
  apply derivation_preserves_mixedWordIdeal M.letter
    (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) M.generates D hD ?_ v hv
  intro i hi
  have hm : M.letter i ∈ genWeightSpace (cartanRootIdeal H) (M.weight i) :=
    cartan_word_mem_genWeight H M.letter M.weight M.letter_root (FreeMagma.of i)
  exact M.outside_genWeightSpace_le_coneWordIdeal C hadd (M.weight i) hi
    ((genWeightSpace (cartanRootIdeal H) (M.weight i)).lie_mem hm)

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanConeTrace
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive trace character of a Cartan cone quotient

The coefficients come from an actual pure-word basis of the quotient.
The abelianization coordinates prove strict positivity for every inside
generator, including the extremal generators of a ray or a two-ray cone.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped BigOperators

namespace CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

set_option maxHeartbeats 1000000 in
/-- The same mixed ideal, viewed as a submodule for the actual Cartan action. -/
def coneCartanSubmodule (C : Set (H →ₗ[ℝ] ℝ))
    (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C) : LieSubmodule ℝ H (cartanRootIdeal H) :=
  { (M.coneWordIdeal C).toSubmodule with
    lie_mem := fun {h v} hv => M.coneWordIdeal_cartan_invariant C hadd h v hv }

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanConeGroup
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual simply connected groups for the Cartan cone quotients -/

noncomputable section
namespace PolycyclicRecognition
namespace CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold ContDiff

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

set_option maxHeartbeats 1000000 in
/-- Lie correspondence supplies the quotient group, while the actual
algebra projection supplies its surjective group map and compact lifts.
The kernel is precisely the exponential image of the mixed-word ideal. -/
theorem exists_cone_group_quotient
    (C : Set (H →ₗ[ℝ] ℝ))
    (N : NilpotentLieModel (cartanRootIdeal H))
    (ExpN : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier)
    (hExpN : IsGroupExponential ExpN)
    (haarN : NilpotentExponentialHaarInput N.modelSpace N.carrier)
    (existQ : NilpotentLieExistenceInput ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (haarQ : ∀ Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C),
      NilpotentExponentialHaarInput Q.modelSpace Q.carrier)
    (integrate : ∀ Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C),
      NilpotentLieIntegrationInput (EN := N.modelSpace) (N := N.carrier)
        (EG := Q.modelSpace) (G := Q.carrier)) :
    ∃ (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
      (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier),
      IsGroupExponential ExpQ ∧
      ∃ (π : N.carrier →* Q.carrier) (s : C(Q.carrier, N.carrier)),
        ContMDiff (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, Q.modelSpace)) ∞ π ∧
        (∀ x : cartanRootIdeal H,
          π (ExpN (N.equiv x)) = ExpQ (Q.equiv (M.coneProjection C x))) ∧
        (∀ y, π (s y) = y) ∧ Function.Surjective π ∧
        (π.ker : Set N.carrier) = ExpN '' (N.equiv '' (M.coneWordIdeal C : Set (cartanRootIdeal H))) ∧
        ∀ K : Set Q.carrier, IsCompact K →
          ∃ D : Set N.carrier, IsCompact D ∧ π '' D = K := by
  have hnilN : LieRing.IsNilpotent (cartanRootIdeal H) := LieModule.IsNilpotent.mk (cartanRootIdeal H) M.bound_zero
  obtain ⟨Q⟩ := existQ (M.coneQuotient_nilpotent C)
  obtain ⟨ExpQ, hExpQ, cQ, hcQ⟩ := Q.exists_exponential_chart (M.coneQuotient_nilpotent C) (haarQ Q)
  obtain ⟨cN, hcN⟩ := (haarN.2 ExpN hExpN (N.tangent_nilpotent hnilN)).1
  let j := Q.equiv.toLieHom.comp ((M.coneProjection C).comp N.equiv.symm.toLieHom)
  have hj : Function.Surjective j :=
    Q.equiv.surjective.comp ((M.coneProjection_surjective C).comp N.equiv.symm.surjective)
  obtain ⟨π, s, hsmooth, hπ, _hlog, hs, hsurj, hker, hlift⟩ :=
    exists_surjective_integration_with_section (integrate Q) (N.tangent_nilpotent hnilN)
      j hj ExpN ExpQ hExpN hExpQ cN hcN cQ hcQ
  refine ⟨Q, ExpQ, hExpQ, π, s, hsmooth, ?_, hs, hsurj, ?_, hlift⟩
  · intro x
    simpa [j] using hπ (N.equiv x)
  · rw [hker]
    ext n
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv' : M.coneProjection C (N.equiv.symm v) = 0 := by
        apply Q.equiv.injective
        simpa [j] using hv
      have hi : N.equiv.symm v ∈ M.coneWordIdeal C :=
        (Submodule.Quotient.mk_eq_zero (M.coneWordIdeal C).toSubmodule).mp hv'
      exact ⟨v, ⟨N.equiv.symm v, hi, N.equiv.apply_symm_apply v⟩, (hcN v).symm⟩
    · rintro ⟨v, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨N.equiv x, ?_, hcN _⟩
      change j (N.equiv x) = 0
      have hx' : M.coneProjection C x = 0 :=
        (Submodule.Quotient.mk_eq_zero (M.coneWordIdeal C).toSubmodule).mpr hx
      simp [j, hx']

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MixedWordBoxModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete nilpotent box model of a cone ideal

The finite mixed words generate the ideal even as a vector space. Using
them as an alphabet allows the existing box calculus to apply directly.
Flattening this alphabet retains the original word and its exact width.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule LieAlgebra
open scoped BigOperators

namespace CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

theorem coneIdealWordBound_zero (C : Set (H →ₗ[ℝ] ℝ)) :
    lowerCentralSeries ℝ (M.coneWordIdeal C) (M.coneWordIdeal C)
      (M.coneIdealWordBound C) = ⊥ := by
  let := M.coneIdeal_nilpotent C
  exact (LieModule.IsNilpotent.nilpotent ℝ (M.coneWordIdeal C)
    (M.coneWordIdeal C)).choose_spec

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoxDilation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact template shifts for actual Cartan boxes

The scalar action on generalized weight spaces is a genuine Lie automorphism.
It takes each scaled word basis to the basis for the translated template.
The finite Dynkin identity then integrates it to the needed group automorphism.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra
open scoped BigOperators Manifold

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

variable {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp) (dynkin : NilpotentDynkinExpansionInput EN N)

set_option maxHeartbeats 1000000 in
/-- Exact weight dilation in the actual nilpotent group. -/
def groupWeightDilation (w : W) (r : ℝ) : N ≃* N :=
  integrateNilpotentLieEquiv eN Exp hbij dynkin hExp M.bound_zero
    (cartanIdealWeightDilation T H (r • cartanHeightSection T H (eW.symm w)))

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ConeIdealInsideAdjoint
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform ideal-box bounds for an inside adjoint

An inside letter has width zero. Adjoining it to a mixed word leaves the
width unchanged, so maximizing-basis exchange bounds its adjoint uniformly
in every rescaled ideal box.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

def coneIdealLetterAdjoint (i : Fin M.letterCount) :
    Module.End ℝ (M.coneWordIdeal C) :=
  toEnd ℝ (cartanRootIdeal H) (M.coneWordIdeal C) (M.letter i)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConeIdealStrictWidth
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Strict width absorbs the inside-letter conjugation flow

The flow here is the finite exponential of the actual restricted adjoint.
No box inclusion is an input. A positive width gap absorbs its polynomial
growth uniformly over every point of the smaller box.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module Filter
open scoped Topology

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

def coneIdealLetterFlow (i : Fin M.letterCount) (t : ℝ) (v : M.coneWordIdeal C) :
    M.coneWordIdeal C := finiteEndFlow (M.coneIdealLetterAdjoint C i) M.bound t v

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanAdjointAction
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full exponential Cartan action

The scalar dilation and the polynomial residual automorphism together give
the exponential of the actual adjoint action on every nonzero root. In a
compatible faithful representation this is conjugation, not an independently
assumed action on the nilpotent ideal.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
/-- The full Cartan action, including its nonsemisimple part. -/
def cartanIdealAdjointAutomorphism (h : H) : cartanRootIdeal H ≃ₗ⁅ℝ⁆ cartanRootIdeal H :=
  (cartanIdealResidualAutomorphism T H h).trans (cartanIdealWeightDilation T H h)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConeIdealInnerAutomorphism
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.stationaryL2SMulComm _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ambient nilpotent inner action on the cone ideal

Every ambient adjoint restricts to a nilpotent derivation of the actual
ideal. Its finite exponential is a Lie automorphism with determinant one.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

def coneIdealInnerDerivation (x : cartanRootIdeal H) :
    LieDerivation ℝ (M.coneWordIdeal C) (M.coneWordIdeal C) where
  toLinearMap := toEnd ℝ (cartanRootIdeal H) (M.coneWordIdeal C) x
  leibniz' u v := by
    apply Subtype.ext
    change ⁅x, ⁅(u : cartanRootIdeal H), (v : cartanRootIdeal H)⁆⁆ =
      ⁅(u : cartanRootIdeal H), ⁅x, (v : cartanRootIdeal H)⁆⁆ -
        ⁅(v : cartanRootIdeal H), ⁅x, (u : cartanRootIdeal H)⁆⁆
    rw [leibniz_lie, ← lie_skew (v : cartanRootIdeal H) ⁅x, (u : cartanRootIdeal H)⁆]
    abel

theorem coneIdealInnerDerivation_pow_coe (x : cartanRootIdeal H) (k : ℕ)
    (v : M.coneWordIdeal C) :
    (((M.coneIdealInnerDerivation C x).toLinearMap ^ k) v : cartanRootIdeal H) =
      ((toEnd ℝ (cartanRootIdeal H) (cartanRootIdeal H) x) ^ k) v := by
  induction k with
  | zero => rfl
  | succ k hk =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    change ⁅x, (((M.coneIdealInnerDerivation C x).toLinearMap ^ k) v : cartanRootIdeal H)⁆ = _
    rw [hk]
    rfl

theorem coneIdealInnerDerivation_nilpotent (x : cartanRootIdeal H) :
    (M.coneIdealInnerDerivation C x).toLinearMap ^ M.bound = 0 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  rw [M.coneIdealInnerDerivation_pow_coe, Module.End.pow_apply]
  have hv := iterate_toEnd_mem_lowerCentralSeries ℝ (cartanRootIdeal H)
    (cartanRootIdeal H) x (v : cartanRootIdeal H) M.bound
  rw [M.bound_zero] at hv
  exact hv

def coneIdealInnerAutomorphism (x : cartanRootIdeal H) :
    M.coneWordIdeal C ≃ₗ⁅ℝ⁆ M.coneWordIdeal C := by
  letI : Module ℚ (M.coneWordIdeal C) := Module.compHom _ (algebraMap ℚ ℝ)
  letI : LieAlgebra ℚ (M.coneWordIdeal C) :=
    { lie_smul := fun t x y => lie_smul (algebraMap ℚ ℝ t) x y }
  exact (M.coneIdealInnerDerivation C x).exp
    ⟨M.bound, M.coneIdealInnerDerivation_nilpotent C x⟩

theorem coneIdealInnerAutomorphism_det (x : cartanRootIdeal H) :
    LinearMap.det (M.coneIdealInnerAutomorphism C x).toLinearEquiv.toLinearMap = 1 := by
  let : Module ℚ (M.coneWordIdeal C) := Module.compHom _ (algebraMap ℚ ℝ)
  letI : LieAlgebra ℚ (M.coneWordIdeal C) :=
    { lie_smul := fun t x y => lie_smul (algebraMap ℚ ℝ t) x y }
  exact det_nilpotent_exp (M.coneIdealInnerDerivation C x).toLinearMap
    ⟨M.bound, M.coneIdealInnerDerivation_nilpotent C x⟩

theorem coneIdealInnerAutomorphism_apply (x : cartanRootIdeal H)
    (v : M.coneWordIdeal C) :
    M.coneIdealInnerAutomorphism C x v =
      finiteEndFlow (M.coneIdealInnerDerivation C x).toLinearMap M.bound 1 v := by
  let : Module ℚ (M.coneWordIdeal C) := Module.compHom _ (algebraMap ℚ ℝ)
  letI : LieAlgebra ℚ (M.coneWordIdeal C) :=
    { lie_smul := fun t x y => lie_smul (algebraMap ℚ ℝ t) x y }
  change IsNilpotent.exp (M.coneIdealInnerDerivation C x).toLinearMap v = _
  rw [IsNilpotent.exp_eq_sum (M.coneIdealInnerDerivation_nilpotent C x)]
  simp only [finiteEndFlow, LinearMap.sum_apply, LinearMap.smul_apply, one_pow, mul_one]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Rat.cast_smul_eq_qsmul ℝ]
  simp only [Rat.cast_inv, Rat.cast_natCast]

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConeIdealInnerHaar
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One ideal Haar measure for both boxes and ambient conjugation -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra MeasureTheory
open scoped Manifold ENNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

section Haar

variable {E Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace Q] [ChartedSpace E Q] [Group Q]
  [LieGroup (𝓘(ℝ, E)) ⊤ Q] [T2Space Q] [SimplyConnectedSpace Q]
  [MeasurableSpace Q] [BorelSpace Q]
  (e : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) Q)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) Q → Q) (hExp : IsGroupExponential Exp)

include hExp in
theorem exists_coneIdeal_inner_invariant_haar
    (haar : NilpotentExponentialHaarInput E Q)
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C)) :
    ∃ (μ : Measure Q) (hbij : Function.Bijective Exp), μ.IsHaarMeasure ∧
      (∀ x : cartanRootIdeal H,
        MeasurePreserving (exponentialConjugate e Exp hbij (M.coneIdealInnerAutomorphism C x)) μ μ) ∧
      ∀ (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C) (r R : ℝ), 0 ≤ R →
        μ (M.coneIdealBox C (Exp ∘ e) s β r R) =
          ENNReal.ofReal |(columnBasisMatrix
            (wordListCoordinates (M.coneMixedVector C) (M.coneIdealWordList C) b₀) β.val).det| *
          ENNReal.ofReal (Real.exp (r * columnBasisWeight
            (fun w : M.coneIdealWordList C => M.coneIdealWordCost C s w) β.val)) *
          ENNReal.ofReal (2 * R) ^ finrank ℝ (M.coneWordIdeal C) := by
  have hnil := e.nilpotent_iff_equiv_nilpotent.mp (M.coneIdeal_nilpotent C)
  obtain ⟨⟨chart, hchart⟩, hhaar⟩ := haar.2 Exp hExp hnil
  have hbij : Function.Bijective Exp := by
    have heq : Exp = chart := funext fun x => (hchart x).symm
    rw [heq]
    exact chart.bijective
  let μ := Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume
  have hμ : μ.IsHaarMeasure := by
    have hf : ((Exp ∘ e) ∘ b₀.equivFun.symm) =
        Exp ∘ (b₀.map e.toLinearEquiv).equivFun.symm := by
      funext t
      rw [Basis.map_equivFun]
      rfl
    change (Measure.map _ volume).IsHaarMeasure
    rw [hf]
    exact hhaar _ _
  refine ⟨μ, hbij, hμ, ?_, ?_⟩
  · intro x
    exact exponentialConjugate_measurePreserving e Exp hbij chart hchart b₀
      (M.coneIdealInnerAutomorphism C x) (M.coneIdealInnerAutomorphism_det C x)
  · intro s β r R hR
    exact exponentialCoordinate_weighted_box_measure e Exp chart hchart b₀
      (M.coneMixedVector C) (M.coneIdealWordList C)
      (fun w => M.coneIdealWordCost C s w) β r R hR

end Haar

variable {G A : Type*} [Group G] [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

variable (ExpN : cartanRootIdeal H → G) (j : cartanRootIdeal H →ₗ⁅ℝ⁆ A)
  (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
  (hmatch : ∀ x, ρ (ExpN x) = algebraExpUnit (j x))

attribute [local instance] OAI.PolycyclicRecognition.CartanWordModel.innerHaarNormedAddCommGroup
attribute [local instance] OAI.PolycyclicRecognition.CartanWordModel.innerHaarNormedSpace
include hρ hmatch in
theorem coneIdealInnerAutomorphism_exp_conjugation (x : cartanRootIdeal H)
    (v : M.coneWordIdeal C) :
    ExpN (M.coneIdealInnerAutomorphism C x v : cartanRootIdeal H) =
      ExpN x * ExpN (v : cartanRootIdeal H) * (ExpN x)⁻¹ := by
  let D := toEnd ℝ (cartanRootIdeal H) (cartanRootIdeal H) x
  have hD : D ^ M.bound = 0 := by
    apply LinearMap.ext
    intro y
    rw [Module.End.pow_apply, LinearMap.zero_apply]
    have hy := iterate_toEnd_mem_lowerCentralSeries ℝ (cartanRootIdeal H)
      (cartanRootIdeal H) x y M.bound
    rw [M.bound_zero] at hy
    exact hy
  rw [M.coneIdealInnerAutomorphism_apply]
  have hm := finiteEndFlow_map (M.coneWordIdeal C).incl.toLinearMap
    (M.coneIdealInnerDerivation C x).toLinearMap D (fun _ => rfl) M.bound 1 v
  calc
    _ = ExpN (finiteEndFlow D M.bound 1 (v : cartanRootIdeal H)) := congrArg ExpN hm
    _ = _ := by
      rw [finiteEndFlow_eq_exp D hD]
      have hh := exp_ad_eq_group_conjugation ExpN j ρ hρ hmatch x v 1
      rw [one_smul, one_smul] at hh
      rw [one_smul]
      exact hh

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConeKernelHaar
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugation-invariant Haar measure on the actual cone kernel -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra MeasureTheory
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

variable {E I N Q A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace I] [ChartedSpace E I] [Group I]
  [LieGroup (𝓘(ℝ, E)) ⊤ I] [T2Space I] [SimplyConnectedSpace I]
  [MeasurableSpace I] [BorelSpace I]
  [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
  [MeasurableSpace N] [BorelSpace N] [Group Q]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] OAI.PolycyclicRecognition.CartanWordModel.kernelHaarNormedAddCommGroup
attribute [local instance] OAI.PolycyclicRecognition.CartanWordModel.kernelHaarNormedSpace
/-- The existing published exponential Haar input supplies an intrinsic
measure whose image on the actual kernel is Haar and invariant under every
ambient nilpotent conjugation. -/
theorem exists_cone_kernel_invariant_haar
    (e : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) I)
    (ExpI : GroupLieAlgebra (𝓘(ℝ, E)) I → I) (hExpI : IsGroupExponential ExpI)
    (haar : NilpotentExponentialHaarInput E I)
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (π : N →* Q) (ι : I →* N) (hι : Topology.IsClosedEmbedding ι)
    (hrange : Set.range ι = (π.ker : Set N))
    (ExpN : cartanRootIdeal H → N) (hsurj : Function.Surjective ExpN)
    (hcompat : ∀ v : M.coneWordIdeal C, ι (ExpI (e v)) = ExpN v)
    (j : cartanRootIdeal H →ₗ⁅ℝ⁆ A) (ρ : N →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (ExpN x) = algebraExpUnit (j x)) :
    ∃ μ : Measure I, μ.IsHaarMeasure ∧
      (Measure.map (kernelRealization π ι hι hrange) μ).IsHaarMeasure ∧
      (∀ n : N, MeasurePreserving (quotientKernelConjugate π n)
        (Measure.map (kernelRealization π ι hι hrange) μ)
        (Measure.map (kernelRealization π ι hι hrange) μ)) ∧
      (Measure.map (kernelRealization π ι hι hrange) μ).IsMulRightInvariant := by
  obtain ⟨μ, hbij, hμ, hinv, _hvol⟩ :=
    M.exists_coneIdeal_inner_invariant_haar C e ExpI hExpI haar b₀
  let : IsTopologicalGroup I := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : μ.IsHaarMeasure := hμ
  have hμk : (Measure.map (kernelRealization π ι hι hrange) μ).IsHaarMeasure :=
    (kernelRealization π ι hι hrange).toMulEquiv.isHaarMeasure_map μ
      (kernelRealization π ι hι hrange).continuous
      (kernelRealization π ι hι hrange).symm.continuous
  let : (Measure.map (kernelRealization π ι hι hrange) μ).IsHaarMeasure := hμk
  have hconj (n : N) : MeasurePreserving (quotientKernelConjugate π n)
      (Measure.map (kernelRealization π ι hι hrange) μ)
      (Measure.map (kernelRealization π ι hι hrange) μ) := by
    obtain ⟨x, rfl⟩ := hsurj n
    apply kernelRealization_conjugation_preserving π ι hι hrange μ (ExpN x)
      (exponentialConjugate e ExpI hbij (M.coneIdealInnerAutomorphism C x)) (hinv x)
    intro z
    obtain ⟨v, rfl⟩ := (hbij.comp e.bijective).surjective z
    change ι (exponentialConjugate e ExpI hbij (M.coneIdealInnerAutomorphism C x)
      (ExpI (e v))) = _
    rw [exponentialConjugate_apply_exp, hcompat]
    change ExpN _ = ExpN x * ι (ExpI (e v)) * _
    rw [hcompat]
    exact M.coneIdealInnerAutomorphism_exp_conjugation C ExpN j ρ hρ hmatch x v
  exact ⟨μ, hμ, hμk, hconj,
    kernel_measure_right_invariant π _ hconj⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanMeasuredCone
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual ideal, quotient and Haar measures for a fixed cone -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Set
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (C : Set (H →ₗ[ℝ] ℝ))

set_option maxHeartbeats 1000000 in
/-- Compatible Haar data; no profile, metric bound or offset is included. -/
structure ConeGroupMeasures
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (I : NilpotentLieModel (M.coneWordIdeal C)) (D : M.ConeGroupMaps F C Q I) where
  measureQ : Measure Q.carrier
  measureI : Measure I.carrier
  haarQ : measureQ.IsHaarMeasure
  haarI : measureI.IsHaarMeasure
  haarKernel : (Measure.map
    (kernelRealization D.quotient D.inclusion D.inclusion_closed D.inclusion_range) measureI).IsHaarMeasure
  conjugation_invariant : ∀ n : F.N.carrier,
    MeasurePreserving (quotientKernelConjugate D.quotient n)
      (Measure.map (kernelRealization D.quotient D.inclusion D.inclusion_closed D.inclusion_range) measureI)
      (Measure.map (kernelRealization D.quotient D.inclusion D.inclusion_closed D.inclusion_range) measureI)
  kernel_rightInvariant : (Measure.map
    (kernelRealization D.quotient D.inclusion D.inclusion_closed D.inclusion_range) measureI).IsMulRightInvariant

set_option maxHeartbeats 1000000 in
/-- The concrete groups, maps and compatible measures for one cone. -/
structure MeasuredCone where
  Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C)
  I : NilpotentLieModel (M.coneWordIdeal C)
  maps : M.ConeGroupMaps F C Q I
  measures : M.ConeGroupMeasures F C Q I maps

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanActualConjugation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual Cartan conjugation and shifted boxes

The full Lie action integrates to the nilpotent group. A faithful compatible
representation identifies this automorphism with ambient conjugation. The
resulting box estimate retains the polynomial residual factor and the exact
canonical-height translation.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp) (dynkin : NilpotentDynkinExpansionInput EN N)

set_option maxHeartbeats 1000000 in
/-- Integration of the complete adjoint action, including its residual part. -/
def adjointGroupAutomorphism (h : H) : N ≃* N :=
  integrateNilpotentLieEquiv eN Exp hbij dynkin hExp M.bound_zero
    (cartanIdealAdjointAutomorphism T H h)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ComplexFactorLocalChart
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanRealShadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth local coordinates from the complex-weight factors -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff Topology

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp)

def kernelParameter : E →L[ℝ] F.N.modelSpace :=
  (show E →ₗ[ℝ] F.N.modelSpace from
    F.N.equiv.toLinearMap.comp (T.kernelComponent H)).toContinuousLinearMap

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanConeInvariance
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Cartan automorphisms preserve the cone ideal -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set

set_option maxHeartbeats 1000000 in
theorem map_mixedWordIdeal_mem {I L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (X : I → L) (outside : I → Prop)
    (hgen : LieSubalgebra.lieSpan ℝ L (range X) = ⊤)
    (F : L →ₗ⁅ℝ⁆ L) (J : LieIdeal ℝ L)
    (hout : ∀ i, outside i → F (X i) ∈ J)
    (v : L) (hv : v ∈ mixedWordIdeal X outside hgen) : F v ∈ J := by
  change F v ∈ J.toSubmodule
  change v ∈ mixedWordSpan X outside at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    rw [evalBracketWord_map]
    exact eval_mixed_mem_ideal (fun i => F (X i)) outside J hout w hw
  | zero => simpa only [map_zero] using J.toSubmodule.zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using J.add_mem hx hy
  | smul r x _ hx => simpa only [map_smul] using J.smul_mem r hx

namespace CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)

set_option maxHeartbeats 1000000 in
theorem coneWordIdeal_adjoint_mem
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (h : H) (v : cartanRootIdeal H) (hv : v ∈ M.coneWordIdeal C) :
    cartanIdealAdjointAutomorphism T H h v ∈ M.coneWordIdeal C := by
  apply map_mixedWordIdeal_mem M.letter
    (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) M.generates
    (cartanIdealAdjointAutomorphism T H h).toLieHom (M.coneWordIdeal C) ?_ v hv
  intro i hi
  have hr := cartanIdealResidualAutomorphism_root_mem T H h (M.weight i)
    (M.letter i) (M.letter_root i)
  have he : cartanIdealAdjointAutomorphism T H h (M.letter i) =
      Real.exp (M.weight i h) • cartanIdealResidualAutomorphism T H h (M.letter i) := by
    apply Subtype.ext
    exact cartanWeightScale_apply_root T H h (M.weight i) hr
  apply M.outside_genWeightSpace_le_coneWordIdeal C hadd (M.weight i) hi
  let ι : cartanRootIdeal H →ₗ⁅ℝ,H⁆ L := ((cartanRootIdeal H).restr H).incl
  rw [← comap_genWeightSpace_eq_of_injective (f := ι)
    ((cartanRootIdeal H).restr H).injective_incl]
  change (cartanIdealAdjointAutomorphism T H h (M.letter i) : L) ∈ rootSpace H (M.weight i)
  rw [he]
  exact (rootSpace H (M.weight i)).smul_mem _ hr

set_option maxHeartbeats 1000000 in
theorem coneWordIdeal_adjoint_mem_iff
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (h : H) (v : cartanRootIdeal H) :
    cartanIdealAdjointAutomorphism T H h v ∈ M.coneWordIdeal C ↔ v ∈ M.coneWordIdeal C :=
  mem_submodule_equiv_iff_of_invariant (M.coneWordIdeal C).toSubmodule
    (cartanIdealAdjointAutomorphism T H h).toLinearEquiv
    (M.coneWordIdeal_adjoint_mem T C hadd h) v

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConeQuotientJacobian
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Jacobian of the induced Cartan action on a cone quotient -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped BigOperators

namespace CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)

theorem coneWordIdeal_dilation_mem (C : Set (H →ₗ[ℝ] ℝ))
    (h : H) (v : cartanRootIdeal H) (hv : v ∈ M.coneWordIdeal C) :
    cartanIdealWeightDilation T H h v ∈ M.coneWordIdeal C := by
  apply map_mixedWordIdeal_mem M.letter
    (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) M.generates
    (cartanIdealWeightDilation T H h).toLieHom (M.coneWordIdeal C) ?_ v hv
  intro i hi
  have he := M.idealWeightDilation_word T h (.of i)
  simp only [evalBracketWord_of, bracketWordExponent_of] at he
  change cartanIdealWeightDilation T H h (M.letter i) ∈ M.coneWordIdeal C
  rw [he]
  exact (M.coneWordIdeal C).smul_mem _
    (eval_mixed_mem_span M.letter (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) (w := .of i) hi)

theorem coneWordIdeal_residual_mem (C : Set (H →ₗ[ℝ] ℝ))
    (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (h : H) (v : cartanRootIdeal H) (hv : v ∈ M.coneWordIdeal C) :
    cartanIdealResidualAutomorphism T H h v ∈ M.coneWordIdeal C := by
  apply map_mixedWordIdeal_mem M.letter
    (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) M.generates
    (cartanIdealResidualAutomorphism T H h).toLieHom (M.coneWordIdeal C) ?_ v hv
  intro i hi
  apply M.outside_genWeightSpace_le_coneWordIdeal C hadd (M.weight i) hi
  let ι : cartanRootIdeal H →ₗ⁅ℝ,H⁆ L := ((cartanRootIdeal H).restr H).incl
  rw [← comap_genWeightSpace_eq_of_injective (f := ι)
    ((cartanRootIdeal H).restr H).injective_incl]
  exact cartanIdealResidualAutomorphism_root_mem T H h (M.weight i) (M.letter i) (M.letter_root i)

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConeQuotientAutomorphism
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quotient Lie automorphism and its exponential Haar multiplier -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set MeasureTheory
open scoped Manifold

namespace CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)

/-- The induced adjoint Lie automorphism on the cone quotient. -/
def coneAdjointAutomorphism (C : Set (H →ₗ[ℝ] ℝ))
    (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C) (h : H) :
    ((cartanRootIdeal H) ⧸ M.coneWordIdeal C) ≃ₗ⁅ℝ⁆
      ((cartanRootIdeal H) ⧸ M.coneWordIdeal C) :=
  lieQuotientAutomorphism (M.coneWordIdeal C) (cartanIdealAdjointAutomorphism T H h)
    (M.coneWordIdeal_adjoint_mem_iff T C hadd h)

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanMeasuredConeHaar
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Haar measure for the actual section used by the probe chains -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (C : Set (H →ₗ[ℝ] ℝ)) (D : M.MeasuredCone F C)

set_option maxHeartbeats 1000000 in
/-- The intrinsic ideal Haar measure transported to the exact kernel. -/
def MeasuredCone.kernelMeasure : Measure D.maps.quotient.ker :=
  Measure.map
    (kernelRealization D.maps.quotient D.maps.inclusion D.maps.inclusion_closed D.maps.inclusion_range) D.measures.measureI

set_option maxHeartbeats 1000000 in
/-- The original product measure for any prescribed continuous section. -/
def MeasuredCone.sectionMeasure
    (σ : ContinuousMap D.Q.carrier F.N.carrier) (hσ : ∀ q, D.maps.quotient (σ q) = q) :
    Measure F.N.carrier := by
  let : IsTopologicalGroup F.N.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  let : IsTopologicalGroup D.Q.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, D.Q.modelSpace)) ⊤
  exact Measure.map (quotientSectionHomeomorph D.maps.quotient D.maps.quotient_continuous σ hσ).symm
    (D.measures.measureQ.prod (D.kernelMeasure M F C))

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanMeasuredConeCells
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive compact probability cells for the actual cone models -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Set Metric TopologicalSpace
open scoped Manifold BigOperators

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (C : Set (H →ₗ[ℝ] ℝ)) (D : M.MeasuredCone F C)

set_option maxHeartbeats 1000000 in
/-- Replacing only the quotient Haar normalization leaves the intrinsic
kernel measure and its conjugation invariance intact. -/
def MeasuredCone.withQuotientHaar (μQ : Measure D.Q.carrier) (hμQ : μQ.IsHaarMeasure) :
    M.MeasuredCone F C where
  Q := D.Q
  I := D.I
  maps := D.maps
  measures := { D.measures with measureQ := μQ, haarQ := hμQ }

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSourceDilation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The same Cartan dilation in tiling, concentration, and source measure -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hbij : Function.Bijective F.ExpN)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ v, chartN v = F.ExpN v)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)

set_option maxHeartbeats 1000000 in
/-- The continuous source dilation integrates the same Lie automorphism as
the algebraic dilation used by the stored linked chains. -/
def sourceDilation (h : H) : F.N.carrier ≃ₜ* F.N.carrier :=
  integrateNilpotentLieEquivContinuous F.N.equiv F.ExpN hbij chartN hchartN
    dynkinN F.isExpN M.bound_zero (cartanIdealWeightDilation T H h)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanTiledProbeBoxes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual tiled probes in the three Cartan template boxes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric
open scoped Manifold Pointwise

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ)) {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N I : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  [MeasurableSpace N] [BorelSpace N] [SecondCountableTopology N]
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]

set_option maxHeartbeats 1000000 in
/-- Fixed source box data; packaging it keeps later three-chain applications
small when the ambient algebra is an actual tangent Lie algebra. -/
structure TiledProbeBoxData
    (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
    (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N)
    (ExpI : M.coneWordIdeal C → I) (ι : I →* N)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (β : Fin 3 → M.ConeIdealBases C) where
  bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
    ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)
  lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
    cartanRootIdeal H
  γ : Fin 3 → M.Bases
  R₀ : ℝ
  lifts : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j
  radius_nonneg : 0 ≤ R₀
  maximizing : ∀ j, IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
    (M.boxCost T hunimod eW (E j)) (γ j).val
  select : ∀ r : ℝ, 0 ≤ r → ∀ R : ℝ, 0 ≤ R →
      let U := M.coneIdealBox C ExpI
        ((M.supportIn T hunimod eW).weightSupport (E 0)) (β 0) r 1
      let Banchor := M.coneIdealBox C ExpI
        ((M.supportIn T hunimod eW).weightSupport (E 1)) (β 1) r 1
      let Bsmall := M.coneIdealBox C ExpI
        ((M.supportIn T hunimod eW).weightSupport (E 2)) (β 2) r R
      let Z := closedBall (0 : Fin (finrank ℝ
        (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1
      let σ : Z → N := fun q => ExpN (eN
        (quotientLinearSection (M.coneWordIdeal C) bQ lift (bQ.equivFun.symm q.val)))
      ∀ (φ : I ≃ₜ* I) (k : N), (∀ z, ι (φ z) = k * ι z * k⁻¹) →
      ∀ (m : ℕ) (anchor : Fin m → I) (tile : Fin m → Set I),
      (∀ j, MeasurableSet (tile j)) →
      Pairwise (fun j l => Disjoint (tile j) (tile l)) → (⋃ j, tile j) = U →
      (∀ j, φ.symm (anchor j) ∈ Banchor) →
      (∀ j, tile j ⊆ anchor j • (φ '' Bsmall)) →
      ∃ (index : U → Fin m) (probe : Fin 3 → Z × U → N),
        Measurable index ∧ (∀ j, Measurable (probe j)) ∧
        (∀ j y, probe j y ∈ M.groupBox T hunimod eW (ExpN ∘ eN)
          (E j) (γ j) r (![R₀, 1, R] j)) ∧
        (∀ y, probe 0 y = ι y.2.val * σ y.1) ∧
        (∀ y, probe 1 y = ι (φ.symm (anchor (index y.2)))) ∧
        ∀ y, probe 2 y = ι (φ.symm ((anchor (index y.2))⁻¹ * y.2.val))

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


variable (ExpI : M.coneWordIdeal C → I)
  (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
  (E : Fin 3 → Set W)
  (β : Fin 3 → M.ConeIdealBases C)
  (ambient : M.Bases)
  (t : Fin M.letterCount → ℝ)
  (scale : ℕ → ℝ)
  (φ : ℕ → I ≃ₜ* I)
  (ι : I →* F.N.carrier)
  (tiles : ℕ → ℕ)
  (anchor : ∀ n, Fin (tiles n) → I)
  (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
  (πQ : F.N.carrier →* Q.carrier)
  (hι : Topology.IsClosedEmbedding ι)
  (hrange : range ι = (πQ.ker : Set F.N.carrier))

set_option maxHeartbeats 1000000 in
/-- The scale-dependent kernel part of the original source cell. -/
def TiledProbeChainData.sourceKernelCell (n : ℕ) : Set πQ.ker :=
  kernelRealization πQ ι hι hrange ''
    M.coneIdealBox C ExpI ((M.supportIn T hunimod eW).weightSupport (E 0))
      (β 0) (scale n) 1

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ConeIdealFlowTiling
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual inside-letter automorphism in strict-width tilings -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule MeasureTheory Set Filter
open scoped Manifold Topology Pointwise

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  (e : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
  (hbij : Function.Bijective Exp)
  (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
  (dynkin : NilpotentDynkinExpansionInput E G)

def coneIdealLetterAutomorphism (i : Fin M.letterCount) (t : ℝ) : G ≃ₜ* G :=
  integrateNilpotentLieEquivContinuous e Exp hbij chart hchart dynkin hExp
    (M.coneIdealWordBound_zero C) (M.coneIdealInnerAutomorphism C (t • M.letter i))

end PolycyclicRecognition.CartanWordModel

end

end OAI
end


