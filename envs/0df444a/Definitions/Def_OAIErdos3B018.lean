-- Prove2me | Definitions.Def_OAIErdos3B018
-- name    : OAIErdos3B018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T12:48:24.800229+00:00
-- url     : https://prove2.me/theorems/625fe5e5-7159-4e40-8611-57a3d4e65b96
-- title:
--   OpenAI Erdős-3 split, definitions bundle 19 of 90
-- statement:
--   Definitions bundle 19 of 90 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B017`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 19 available.
--
--   Modules: `OAI.Erdos3.BoundedFreeWord`, `OAI.Erdos3.MultidegreeLieFiltration.realLayer`, `OAI.Erdos3.MultidegreeLieFiltration.realLayer_antitone`, `OAI.Erdos3.MultidegreeLieFiltration.realLayer_degree_eq`, `OAI.Erdos3.MultidegreeLieFiltration.realLayer_lie_mem`, `OAI.Erdos3.MultidegreeLieFiltration.realLayer_terminal`, `OAI.Erdos3.MultidegreeLieFiltration.realLayer_zero`, `OAI.Erdos3.MultidegreeLieFiltration.realification`, `OAI.Erdos3.NilpotentLieBCHGroup.basisChart_mem_source`, `OAI.Erdos3.NilpotentLieBCHGroup.basisChartedSpace`, `OAI.Erdos3.NilpotentLieBCHGroup.basisCoordinateMap_rightTranslate`, `OAI.Erdos3.NilpotentLieBCHGroup.basisHomeomorph`, `OAI.Erdos3.NilpotentLieBCHGroup.basisHomeomorph_apply`, `OAI.Erdos3.NilpotentLieBCHGroup.basisHomeomorph_pow`, `OAI.Erdos3.NilpotentLieBCHGroup.basisHomeomorph_zpow`, `OAI.Erdos3.NilpotentLieBCHGroup.basisQuotientDist`, `OAI.Erdos3.NilpotentLieBCHGroup.basisQuotientDist_change_le`, `OAI.Erdos3.NilpotentLieBCHGroup.basisQuotientDist_mapReal_le`, `OAI.Erdos3.NilpotentLieBCHGroup.basis_extChartAt_apply`, `OAI.Erdos3.NilpotentLieBCHGroup.basis_extChartAt_symm_apply`, `OAI.Erdos3.NilpotentLieBCHGroup.basis_tangentCoordChange`, `OAI.Erdos3.NilpotentLieBCHGroup.basis_tangent_symmL`, `OAI.Erdos3.NilpotentLieBCHGroup.changeStep`, `OAI.Erdos3.NilpotentLieBCHGroup.changeStep_coord`, `OAI.Erdos3.NilpotentLieBCHGroup.closed_discrete_subgroup_of_grid`, `OAI.Erdos3.NilpotentLieBCHGroup.conjugationLinearMap`, `OAI.Erdos3.NilpotentLieBCHGroup.conjugationLinearMap_basis`, `OAI.Erdos3.NilpotentLieBCHGroup.conjugationLinearMap_coordinates`, `OAI.Erdos3.NilpotentLieBCHGroup.contDiff_conjugationCoordinates`, `OAI.Erdos3.NilpotentLieBCHGroup.contDiff_rightInnerForm`, `OAI.Erdos3.NilpotentLieBCHGroup.contDiff_rightTranslate`, `OAI.Erdos3.NilpotentLieBCHGroup.contDiff_rightVelocity`, `OAI.Erdos3.NilpotentLieBCHGroup.contMDiff_basisHomeomorph`, `OAI.Erdos3.NilpotentLieBCHGroup.contMDiff_basisHomeomorph_symm`, `OAI.Erdos3.NilpotentLieBCHGroup.contMDiff_coordinateLine`, `OAI.Erdos3.NilpotentLieBCHGroup.contMDiff_linear_hom`, `OAI.Erdos3.NilpotentLieBCHGroup.contMDiff_mapReal`, `OAI.Erdos3.NilpotentLieBCHGroup.contMDiff_rightInnerForm`, `OAI.Erdos3.NilpotentLieBCHGroup.continuous_conjugation`, `OAI.Erdos3.NilpotentLieBCHGroup.continuous_coord`, `OAI.Erdos3.NilpotentLieBCHGroup.continuous_mk`, `OAI.Erdos3.NilpotentLieBCHGroup.coordHomeomorph`, `OAI.Erdos3.NilpotentLieBCHGroup.coordinateBox`, `OAI.Erdos3.NilpotentLieBCHGroup.coordinateLine`, `OAI.Erdos3.NilpotentLieBCHGroup.coordinateLine_one`, `OAI.Erdos3.NilpotentLieBCHGroup.coordinateLine_zero`, `OAI.Erdos3.NilpotentLieBCHGroup.coordinate_norm_le_rightVelocity`, `OAI.Erdos3.NilpotentLieBCHGroup.dist_coordinates_le_of_near_box`, `OAI.Erdos3.NilpotentLieBCHGroup.edist_coordinates_le_of_near_one`, `OAI.Erdos3.NilpotentLieBCHGroup.enorm_mfderiv_mul_right`, `OAI.Erdos3.NilpotentLieBCHGroup.eq_one_of_subgroup_grid_of_small_coordinates`, `OAI.Erdos3.NilpotentLieBCHGroup.exists_realificationMap_lipschitz_exp_bound`, `OAI.Erdos3.NilpotentLieBCHGroup.exists_realificationMap_quotient_lipschitz_exp_bound`, `OAI.Erdos3.NilpotentLieBCHGroup.exists_uniform_lattice_image_gap`, `OAI.Erdos3.NilpotentLieBCHGroup.homCoordinates`, `OAI.Erdos3.NilpotentLieBCHGroup.homCoordinates_apply`, `OAI.Erdos3.NilpotentLieBCHGroup.homCoordinates_conjugation_eq`, `OAI.Erdos3.NilpotentLieBCHGroup.homCoordinates_continuous`, `OAI.Erdos3.NilpotentLieBCHGroup.homCoordinates_eq_fderiv`, `OAI.Erdos3.NilpotentLieBCHGroup.homCoordinates_intCast_smul`, `OAI.Erdos3.NilpotentLieBCHGroup.homCoordinates_natCast_smul`, `OAI.Erdos3.NilpotentLieBCHGroup.homCoordinates_nsmul`, `OAI.Erdos3.NilpotentLieBCHGroup.homCoordinates_ratCast_smul`, `OAI.Erdos3.NilpotentLieBCHGroup.homCoordinates_rightTranslate`, `OAI.Erdos3.NilpotentLieBCHGroup.homCoordinates_smul`, `OAI.Erdos3.NilpotentLieBCHGroup.homCoordinates_zero`, `OAI.Erdos3.NilpotentLieBCHGroup.homCoordinates_zsmul`, `OAI.Erdos3.NilpotentLieBCHGroup.instContractibleSpace`, `OAI.Erdos3.NilpotentLieBCHGroup.instIsTopologicalGroup`, `OAI.Erdos3.NilpotentLieBCHGroup.instT2Space`, `OAI.Erdos3.NilpotentLieBCHGroup.instTopologicalSpace`, `OAI.Erdos3.NilpotentLieBCHGroup.isManifold_basis`, `OAI.Erdos3.NilpotentLieBCHGroup.isTopologicalGroup_of_continuous_lie`, `OAI.Erdos3.NilpotentLieBCHGroup.lattice_translate_mem_of_small_dist`, `OAI.Erdos3.NilpotentLieBCHGroup.lieGroup_basis`, `OAI.Erdos3.NilpotentLieBCHGroup.linear_hom_basisHomeomorph`, `OAI.Erdos3.NilpotentLieBCHGroup.lipschitzOn_rightTranslate_box`, `OAI.Erdos3.NilpotentLieBCHGroup.lipschitz_changeStep`, `OAI.Erdos3.NilpotentLieBCHGroup.lipschitz_conjugation_of_basis_bound`, `OAI.Erdos3.NilpotentLieBCHGroup.lipschitz_linear_hom`, `OAI.Erdos3.NilpotentLieBCHGroup.lipschitz_mapReal_of_coordinate_bound`, `OAI.Erdos3.NilpotentLieBCHGroup.lipschitz_mapReal_of_entry_bound`, `OAI.Erdos3.NilpotentLieBCHGroup.lipschitz_mapReal_of_rational_height`, `OAI.Erdos3.NilpotentLieBCHGroup.lipschitz_mul_left_of_basis_bound`, `OAI.Erdos3.NilpotentLieBCHGroup.lipschitz_quotient_mapReal_of_entry_bound`, `OAI.Erdos3.NilpotentLieBCHGroup.lipschitz_realificationMap`, `OAI.Erdos3.NilpotentLieBCHGroup.lipschitz_realificationMap_quotient`, `OAI.Erdos3.NilpotentLieBCHGroup.mapOfSteps`, `OAI.Erdos3.NilpotentLieBCHGroup.mapOfSteps_coord`, `OAI.Erdos3.NilpotentLieBCHGroup.mapOfSteps_injective`, `OAI.Erdos3.NilpotentLieBCHGroup.mapReal`, `OAI.Erdos3.NilpotentLieBCHGroup.mapReal_basisHomeomorph`, `OAI.Erdos3.NilpotentLieBCHGroup.mapReal_basisHomeomorph_symm`, `OAI.Erdos3.NilpotentLieBCHGroup.mapReal_id`, `OAI.Erdos3.NilpotentLieBCHGroup.mfderiv_basisHomeomorph_coordinates`, `OAI.Erdos3.NilpotentLieBCHGroup.mfderiv_coordinateLine`, `OAI.Erdos3.NilpotentLieBCHGroup.mfderiv_linear_hom_coordinates`, `OAI.Erdos3.NilpotentLieBCHGroup.mfderiv_mapReal_coordinates`, `OAI.Erdos3.NilpotentLieBCHGroup.mfderiv_mul_right_coordinates`, `OAI.Erdos3.NilpotentLieBCHGroup.norm_coordinates_le_of_near_one`, `OAI.Erdos3.NilpotentLieBCHGroup.norm_fderiv_rightTranslate_zero_le`, `OAI.Erdos3.NilpotentLieBCHGroup.norm_mfderiv_basisHomeomorph_le`, `OAI.Erdos3.NilpotentLieBCHGroup.norm_mfderiv_linear_hom_le`, `OAI.Erdos3.NilpotentLieBCHGroup.norm_mfderiv_mapReal_le`, `OAI.Erdos3.NilpotentLieBCHGroup.norm_tangent_eq_coordinateL2Norm`, `OAI.Erdos3.NilpotentLieBCHGroup.quotientMetricSpace`, `OAI.Erdos3.NilpotentLieBCHGroup.quotientMetricSpace_edist_mk`, `OAI.Erdos3.NilpotentLieBCHGroup.quotientMetricSpace_lipschitz_mk`, `OAI.Erdos3.NilpotentLieBCHGroup.quotient_coordinate_injOn_of_radius`, `OAI.Erdos3.NilpotentLieBCHGroup.rational_kernel_of_near_bounded_point`, `OAI.Erdos3.NilpotentLieBCHGroup.realLieSubgroup`, `OAI.Erdos3.NilpotentLieBCHGroup.realificationHom`, `OAI.Erdos3.NilpotentLieBCHGroup.realificationHom_coord`, `OAI.Erdos3.NilpotentLieBCHGroup.realificationHom_coordinates`, `OAI.Erdos3.NilpotentLieBCHGroup.realificationMap`, `OAI.Erdos3.NilpotentLieBCHGroup.realificationMap_coord`, `OAI.Erdos3.NilpotentLieBCHGroup.realificationMap_realificationHom`, `OAI.Erdos3.NilpotentLieBCHGroup.realificationMap_realificationHom_ofSteps`, `OAI.Erdos3.NilpotentLieBCHGroup.realificationMap_subgroup`, `OAI.Erdos3.NilpotentLieBCHGroup.realification_subgroup_closed_discrete`, `OAI.Erdos3.NilpotentLieBCHGroup.realification_subgroup_grid`, `OAI.Erdos3.NilpotentLieBCHGroup.riemannianEDist_mul_right`, `OAI.Erdos3.NilpotentLieBCHGroup.riemannianEDist_mul_right_le`, `OAI.Erdos3.NilpotentLieBCHGroup.rightEMetricSpace`, `OAI.Erdos3.NilpotentLieBCHGroup.rightInnerForm`, `OAI.Erdos3.NilpotentLieBCHGroup.rightInnerForm_apply`, `OAI.Erdos3.NilpotentLieBCHGroup.rightInnerForm_isVonNBounded`, `OAI.Erdos3.NilpotentLieBCHGroup.rightInnerForm_one`, `OAI.Erdos3.NilpotentLieBCHGroup.rightInnerForm_pos`, `OAI.Erdos3.NilpotentLieBCHGroup.rightInnerForm_right_invariant`, `OAI.Erdos3.NilpotentLieBCHGroup.rightInnerForm_symm`, `OAI.Erdos3.NilpotentLieBCHGroup.rightMetricSpace`, `OAI.Erdos3.NilpotentLieBCHGroup.rightMetricSpace_isIsometricSMul`, `OAI.Erdos3.NilpotentLieBCHGroup.rightMetricSpace_isometry_mul_right`, `OAI.Erdos3.NilpotentLieBCHGroup.rightRiemannianBundle`, `OAI.Erdos3.NilpotentLieBCHGroup.rightRiemannianBundle_continuous`, `OAI.Erdos3.NilpotentLieBCHGroup.rightRiemannianMetric`, `OAI.Erdos3.NilpotentLieBCHGroup.rightSmoothRiemannianMetric`, `OAI.Erdos3.NilpotentLieBCHGroup.rightTranslate`, `OAI.Erdos3.NilpotentLieBCHGroup.rightTranslate_comp`, `OAI.Erdos3.NilpotentLieBCHGroup.rightTranslate_coordinateLine_inv`, `OAI.Erdos3.NilpotentLieBCHGroup.rightTranslate_coordinates`, `OAI.Erdos3.NilpotentLieBCHGroup.rightTranslate_fderiv_injective`, `OAI.Erdos3.NilpotentLieBCHGroup.rightTranslate_fderiv_leftInverse`, `OAI.Erdos3.NilpotentLieBCHGroup.rightTranslate_fderiv_zero_rightVelocity`, `OAI.Erdos3.NilpotentLieBCHGroup.rightTranslate_one`, `OAI.Erdos3.NilpotentLieBCHGroup.rightVelocity`, `OAI.Erdos3.NilpotentLieBCHGroup.rightVelocity_coordinateLine`, `OAI.Erdos3.NilpotentLieBCHGroup.rightVelocity_injective`, `OAI.Erdos3.NilpotentLieBCHGroup.rightVelocity_linear_hom`, `OAI.Erdos3.NilpotentLieBCHGroup.rightVelocity_mapReal`, `OAI.Erdos3.NilpotentLieBCHGroup.rightVelocity_mul`, `OAI.Erdos3.NilpotentLieBCHGroup.rightVelocity_one`, `OAI.Erdos3.NilpotentLieFiltration.lie_realLayer_le`, `OAI.Erdos3.NilpotentLieFiltration.rational_inclusion_mem_realLayer`, `OAI.Erdos3.NilpotentLieFiltration.realLayer`, `OAI.Erdos3.NilpotentLieFiltration.realLayer_antitone`, `OAI.Erdos3.NilpotentLieFiltration.realLayer_lie_mem`, `OAI.Erdos3.NilpotentLieFiltration.realLayer_one`, `OAI.Erdos3.NilpotentLieFiltration.realLayer_terminal`, `OAI.Erdos3.NilpotentLieFiltration.realification`, `OAI.Erdos3.RealSubquotient`, `OAI.Erdos3.basisCoordinateMap`, `OAI.Erdos3.basisCoordinateMap_L2_bound`, `OAI.Erdos3.basisCoordinateMap_apply`, `OAI.Erdos3.basisCoordinateMap_apply_eq_sum`, `OAI.Erdos3.bchInverseBoxConstant`, `OAI.Erdos3.bchLatticeSeparationRadius`, `OAI.Erdos3.bchLogMetricConstant`, `OAI.Erdos3.bchLogMetricConstant_pos`, `OAI.Erdos3.bchProductBracketSupport_card_le`, `OAI.Erdos3.bchSubgroupCoordinates_comap_of_steps`, `OAI.Erdos3.boundedFreeWordCode`, `OAI.Erdos3.boundedFreeWordCode_injective`, `OAI.Erdos3.boundedFreeWordFintype`, `OAI.Erdos3.boundedFreeWord_card_le`, `OAI.Erdos3.contDiff_bilinearComp_self`, `OAI.Erdos3.coordinateDotForm`, `OAI.Erdos3.coordinateDotForm_apply`, `OAI.Erdos3.coordinateLipschitzBound`, `OAI.Erdos3.coordinateLipschitzBound_le_exp`, `OAI.Erdos3.coordinateLipschitzBound_pos`, `OAI.Erdos3.cosetImage_local_lifts`, `OAI.Erdos3.cosetMap`, `OAI.Erdos3.cosetMap_mk`, `OAI.Erdos3.edist_ne_top_of_preconnected`, `OAI.Erdos3.exists_ambient_image_reconstruction`, `OAI.Erdos3.exists_bchSubgroup_comap_grid_of_steps`, `OAI.Erdos3.exists_lipschitz_cosetImage_reconstruction`, `OAI.Erdos3.exists_lipschitz_observable_reconstruction`, `OAI.Erdos3.exists_representative_factors_of_reductions`, `OAI.Erdos3.freeWordSet_card_le`, `OAI.Erdos3.lieBCH_eq_of_nilpotent_steps`, `OAI.Erdos3.lieBCH_eq_of_step_le`, `OAI.Erdos3.lieBCH_right_coordinates_sub_bound`, `OAI.Erdos3.lipschitz_cosetMap`, `OAI.Erdos3.map_lieBCH_of_nilpotent_steps`, `OAI.Erdos3.one_tmul_mem_real_baseChange_iff`, `OAI.Erdos3.quotientRightEDist_image_eball`, `OAI.Erdos3.quotientRightEDist_map_le`, `OAI.Erdos3.quotientRightEDist_nhds_basis`, `OAI.Erdos3.quotient_local_lifts_of_identity_lifts`, `OAI.Erdos3.rationalLieInclusion`, `OAI.Erdos3.rationalLieInclusion_apply`, `OAI.Erdos3.rationalLieInclusion_coordinates`, `OAI.Erdos3.rationalLieInclusion_injective`, `OAI.Erdos3.rationalLieInclusion_integer_combination`, `OAI.Erdos3.realLieBasis_structure`, `OAI.Erdos3.realLieHomToRat`, `OAI.Erdos3.realLieSubalgebraOverRat`, `OAI.Erdos3.realSubquotientEquiv`, `OAI.Erdos3.realSubquotientEquiv_project`, `OAI.Erdos3.realSubquotientProjection`, `OAI.Erdos3.realSubquotientProjection_ker`, `OAI.Erdos3.realSubquotientProjection_surjective`, `OAI.Erdos3.real_baseChange_iSup`, `OAI.Erdos3.real_restrictScalars_iSup`, `OAI.Erdos3.real_span_family_coordinates`, `OAI.Erdos3.real_span_family_mem_iff_coordinates`, `OAI.Erdos3.real_span_rational_family`, `OAI.Erdos3.real_span_sum_family`, `OAI.Erdos3.realificationLieHom`, `OAI.Erdos3.realificationLieHom_basis`, `OAI.Erdos3.realificationLieHom_tmul`, `OAI.Erdos3.realificationQuotientMetricSpace`, `OAI.Erdos3.realificationSubmoduleEquiv`, `OAI.Erdos3.realificationSubmoduleEquiv_coe`, `OAI.Erdos3.realificationSubmoduleEquiv_tmul`, `OAI.Erdos3.realification_comap`, `OAI.Erdos3.realification_ker`, `OAI.Erdos3.realification_layer_eq_span`, `OAI.Erdos3.realification_layer_reduction_in_cell`, `OAI.Erdos3.realification_lowerCentralSeries_eq_bot`, `OAI.Erdos3.realification_mkQ_eq_zero_iff`, `OAI.Erdos3.realification_prod`, `OAI.Erdos3.realification_prod_eq_zero_iff`, `OAI.Erdos3.realification_subtype_injective`, `OAI.Erdos3.rightCosetEDist_map_le`, `OAI.Erdos3.rightCosetEMetricSpace`, `OAI.Erdos3.rightCosetMetricSpace`, `OAI.Erdos3.rightCosetMetricSpace_edist_mk`, `OAI.Erdos3.rightCosetMetricSpace_exists_lift`, `OAI.Erdos3.rightCosetMetricSpace_image_ball`, `OAI.Erdos3.rightCosetMetricSpace_lipschitz_mk`, `OAI.Erdos3.rightCosetPseudoEMetricSpace`, `OAI.Erdos3.span_conditional_basis`, `OAI.Erdos3.span_submodule_basis`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B015

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RightCosetMetricMap
namespace OAI

section

namespace Erdos3

open _root_.Set
open scoped ENNReal Topology

variable {G : Type*} [Group G] [PseudoEMetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G]

theorem quotientRightEDist_image_eball (Γ : Subgroup G) (x : G) (r : ℝ≥0∞) :
    (QuotientGroup.mk : G → G ⧸ Γ) '' Metric.eball x r =
      {y | quotientRightEDist Γ (QuotientGroup.mk x) y < r} := by
  ext y
  induction y using Quotient.inductionOn with
  | h y =>
    constructor
    · rintro ⟨w, hw, hwq⟩
      change (QuotientGroup.mk w : G ⧸ Γ) = QuotientGroup.mk y at hwq
      change quotientRightEDist Γ (QuotientGroup.mk x) (QuotientGroup.mk y) < r
      rw [← hwq]
      apply (quotientRightEDist_mk_le Γ x w).trans_lt
      simpa only [Metric.mem_eball, edist_comm] using hw
    · intro hy
      change (⨅ γ : Γ, edist x (y * γ)) < r at hy
      obtain ⟨γ, hγ⟩ := iInf_lt_iff.mp hy
      refine ⟨y * γ, ?_, quotient_mk_mul_mem Γ y γ⟩
      simpa only [Metric.mem_eball, edist_comm] using hγ

variable [IsTopologicalGroup G]

theorem quotientRightEDist_nhds_basis (Γ : Subgroup G) (x : G ⧸ Γ) :
    (𝓝 x).HasBasis (fun r : ℝ≥0∞ => 0 < r) (fun r => {y | quotientRightEDist Γ x y < r}) := by
  induction x using Quotient.inductionOn with
  | h x =>
    rw [QuotientGroup.nhds_eq]
    simpa only [quotientRightEDist_image_eball] using
      (Metric.nhds_basis_eball (x := x)).map (QuotientGroup.mk : G → G ⧸ Γ)

@[instance_reducible]
noncomputable def rightCosetPseudoEMetricSpace (Γ : Subgroup G) : PseudoEMetricSpace (G ⧸ Γ) :=
  PseudoEMetricSpace.ofEDistOfTopology (quotientRightEDist Γ)
    (quotientRightEDist_self Γ) (quotientRightEDist_comm Γ) (quotientRightEDist_triangle Γ)
    (quotientRightEDist_nhds_basis Γ)

@[instance_reducible]
noncomputable def rightCosetEMetricSpace (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G)) :
    EMetricSpace (G ⧸ Γ) := by
  letI := rightCosetPseudoEMetricSpace Γ
  letI := hΓ
  exact EMetricSpace.ofT0PseudoEMetricSpace (G ⧸ Γ)

end Erdos3

namespace Erdos3

open _root_.Set

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G]

@[instance_reducible]
noncomputable def rightCosetMetricSpace (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G)) :
    MetricSpace (G ⧸ Γ) := by
  letI := rightCosetEMetricSpace Γ hΓ
  apply EMetricSpace.toMetricSpace
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      exact ne_top_of_le_ne_top (edist_ne_top x y) (quotientRightEDist_mk_le Γ x y)

theorem rightCosetMetricSpace_edist_mk (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G)) (x y : G) :
    letI := rightCosetMetricSpace Γ hΓ
    edist (QuotientGroup.mk x : G ⧸ Γ) (QuotientGroup.mk y) = ⨅ γ : Γ, edist x (y * γ) := rfl

theorem rightCosetMetricSpace_lipschitz_mk (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G)) :
    letI := rightCosetMetricSpace Γ hΓ
    LipschitzWith 1 (QuotientGroup.mk : G → G ⧸ Γ) := by
  let := rightCosetMetricSpace Γ hΓ
  intro x y
  change quotientRightEDist Γ (QuotientGroup.mk x) (QuotientGroup.mk y) ≤ 1 * edist x y
  simpa only [one_mul] using quotientRightEDist_mk_le Γ x y

end Erdos3

end

section

namespace Erdos3

open scoped NNReal ENNReal

variable {G H : Type*} [Group G] [Group H]

def cosetMap (Γ : Subgroup G) (Λ : Subgroup H) (φ : G →* H) (hφ : Γ ≤ Λ.comap φ) :
    (G ⧸ Γ) → (H ⧸ Λ) :=
  Quotient.map φ (fun {a b} h => by
    apply QuotientGroup.leftRel_apply.mpr
    have hm := hφ (QuotientGroup.leftRel_apply.mp h)
    simpa only [Subgroup.mem_comap, map_mul, map_inv] using hm)

@[simp] theorem cosetMap_mk (Γ : Subgroup G) (Λ : Subgroup H) (φ : G →* H)
    (hφ : Γ ≤ Λ.comap φ) (x : G) :
    cosetMap Γ Λ φ hφ (QuotientGroup.mk x) = QuotientGroup.mk (φ x) := rfl

variable [PseudoEMetricSpace G] [PseudoEMetricSpace H]

theorem rightCosetEDist_map_le (Γ : Subgroup G) (Λ : Subgroup H) (φ : G →* H)
    (hφ : Γ ≤ Λ.comap φ) {C : ℝ≥0} (hLip : LipschitzWith C φ) (x y : G) :
    rightCosetEDist Λ (φ x) (φ y) ≤ C * rightCosetEDist Γ x y := by
  unfold rightCosetEDist
  rw [ENNReal.mul_iInf (by simp)]
  apply le_iInf
  intro γ
  let δ : Λ := ⟨φ γ, hφ γ.property⟩
  calc
    (⨅ a : Λ, edist (φ x) (φ y * a)) ≤ edist (φ x) (φ y * δ) := iInf_le _ δ
    _ = edist (φ x) (φ (y * γ)) := by simp only [δ, map_mul]
    _ ≤ C * edist x (y * γ) := hLip x (y * γ)

variable [IsIsometricSMul Gᵐᵒᵖ G] [IsIsometricSMul Hᵐᵒᵖ H]

theorem quotientRightEDist_map_le (Γ : Subgroup G) (Λ : Subgroup H) (φ : G →* H)
    (hφ : Γ ≤ Λ.comap φ) {C : ℝ≥0} (hLip : LipschitzWith C φ) (x y : G ⧸ Γ) :
    quotientRightEDist Λ (cosetMap Γ Λ φ hφ x) (cosetMap Γ Λ φ hφ y) ≤
      C * quotientRightEDist Γ x y :=
  Quotient.inductionOn₂ x y (rightCosetEDist_map_le Γ Λ φ hφ hLip)

end Erdos3

namespace Erdos3

open scoped NNReal

variable {G H : Type*} [Group G] [Group H] [MetricSpace G] [MetricSpace H]
  [IsIsometricSMul Gᵐᵒᵖ G] [IsIsometricSMul Hᵐᵒᵖ H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]

theorem lipschitz_cosetMap (Γ : Subgroup G) (Λ : Subgroup H)
    (hΓ : IsClosed (Γ : Set G)) (hΛ : IsClosed (Λ : Set H))
    (φ : G →* H) (hφ : Γ ≤ Λ.comap φ) {C : ℝ≥0} (hLip : LipschitzWith C φ) :
    letI := rightCosetMetricSpace Γ hΓ
    letI := rightCosetMetricSpace Λ hΛ
    LipschitzWith C (cosetMap Γ Λ φ hφ) := by
  let := rightCosetMetricSpace Γ hΓ
  let := rightCosetMetricSpace Λ hΛ
  intro x y
  exact quotientRightEDist_map_le Γ Λ φ hφ hLip x y

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AmbientImageExtension
namespace OAI

section

namespace Erdos3

open _root_.Set

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G]
  [IsTopologicalGroup G]

theorem rightCosetMetricSpace_image_ball (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G))
    (g : G) (r : ℝ) :
    letI := rightCosetMetricSpace Γ hΓ
    (QuotientGroup.mk : G → G ⧸ Γ) '' Metric.ball g r =
      Metric.ball (QuotientGroup.mk g) r := by
  let := rightCosetMetricSpace Γ hΓ
  have h := quotientRightEDist_image_eball Γ g (ENNReal.ofReal r)
  change (QuotientGroup.mk : G → G ⧸ Γ) '' Metric.eball g (ENNReal.ofReal r) =
    {y | edist (QuotientGroup.mk g : G ⧸ Γ) y < ENNReal.ofReal r} at h
  have h' : (QuotientGroup.mk : G → G ⧸ Γ) '' Metric.eball g (ENNReal.ofReal r) =
      Metric.eball (QuotientGroup.mk g) (ENNReal.ofReal r) := h.trans (by
    ext y
    simp only [mem_ofPred_eq, Metric.mem_eball, edist_comm])
  simpa only [Metric.eball_ofReal] using h'

theorem rightCosetMetricSpace_exists_lift (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G))
    (g : G) (r : ℝ) :
    letI := rightCosetMetricSpace Γ hΓ
    ∀ x : G ⧸ Γ, dist x (QuotientGroup.mk g) < r →
      ∃ h : G, dist h g < r ∧ (QuotientGroup.mk h : G ⧸ Γ) = x := by
  let := rightCosetMetricSpace Γ hΓ
  intro x hx
  have hx' : x ∈ Metric.ball (QuotientGroup.mk g : G ⧸ Γ) r := hx
  rw [← rightCosetMetricSpace_image_ball Γ hΓ g r] at hx'
  exact hx'

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {H G E : Type*} [Group H] [Group G] [MetricSpace H] [MetricSpace G]
  [IsIsometricSMul Hᵐᵒᵖ H] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G]
  [NormedAddCommGroup E]

theorem cosetImage_local_lifts (φ : H →* G) (Λ : Subgroup G)
    (hΛ : IsClosed (Λ : Set G)) (S : Set G) (K δ ε : ℝ≥0)
    (hrep : ∀ y : CosetImage φ Λ, ∃ x : H, projectToCosetImage φ Λ x = y ∧ φ x ∈ S)
    (hgap : ∀ a ∈ S, ∀ b ∈ S, ∀ γ ∈ Λ, dist a (b * γ) < ε → γ ∈ φ.range)
    (hlift : ∀ g ∈ φ.range, dist 1 g < δ → ∃ h : H, φ h = g ∧ dist 1 h ≤ K * dist 1 g) :
    letI := rightCosetMetricSpace Λ hΛ
    ∀ y z : CosetImage φ Λ, dist y z < min δ ε / 2 →
      ∃ x x' : H, projectToCosetImage φ Λ x = y ∧ projectToCosetImage φ Λ x' = z ∧
        dist x x' ≤ (2 * K) * dist y z := by
  let := rightCosetMetricSpace Λ hΛ
  intro y z hyz
  obtain ⟨x, hx, hxS⟩ := hrep y
  obtain ⟨w, hw, hwS⟩ := hrep z
  by_cases heq : y = z
  · refine ⟨x, x, hx, hx.trans heq, ?_⟩
    simp only [heq, dist_self, mul_zero, le_refl]
  have hd : 0 < dist y z := dist_pos.mpr heq
  have hqx : (QuotientGroup.mk (φ x) : G ⧸ Λ) = y.val := congrArg Subtype.val hx
  have hqw : (QuotientGroup.mk (φ w) : G ⧸ Λ) = z.val := congrArg Subtype.val hw
  obtain ⟨b, hb, hbq⟩ := rightCosetMetricSpace_exists_lift Λ hΛ (φ x) (2 * dist y z) z.val (by
    rw [hqx, dist_comm]
    change dist y z < 2 * dist y z
    linarith)
  let γ := (φ w)⁻¹ * b
  have hγ : γ ∈ Λ := QuotientGroup.eq.mp (hqw.trans hbq.symm)
  have hprod : φ w * γ = b := by simp only [γ, mul_inv_cancel_left]
  have hγrange : γ ∈ φ.range := by
    apply hgap (φ x) hxS (φ w) hwS γ hγ
    rw [hprod, dist_comm]
    have hmin : (min δ ε : ℝ≥0) ≤ ε := min_le_right _ _
    have hminr : ((min δ ε : ℝ≥0) : ℝ) ≤ ε := hmin
    linarith
  have hbrange : b ∈ φ.range := by
    rw [← hprod]
    exact φ.range.mul_mem ⟨w, rfl⟩ hγrange
  let g := b * (φ x)⁻¹
  have hgrange : g ∈ φ.range := φ.range.mul_mem hbrange (φ.range.inv_mem ⟨x, rfl⟩)
  have hgdist : dist 1 g = dist b (φ x) := by
    simpa only [g, mul_inv_cancel, dist_comm] using dist_mul_right (φ x) b (φ x)⁻¹
  have hgnear : dist 1 g < δ := by
    rw [hgdist]
    have hmin : (min δ ε : ℝ≥0) ≤ δ := min_le_left _ _
    have hminr : ((min δ ε : ℝ≥0) : ℝ) ≤ δ := hmin
    linarith
  obtain ⟨u, hu, hudist⟩ := hlift g hgrange hgnear
  refine ⟨x, u * x, hx, ?_, ?_⟩
  · apply Subtype.ext
    change (QuotientGroup.mk (φ (u * x)) : G ⧸ Λ) = z.val
    rw [map_mul, hu]
    simpa only [g, inv_mul_cancel_right] using hbq
  · have hdist : dist x (u * x) = dist 1 u := by
      simpa only [one_mul] using dist_mul_right (1 : H) u x
    rw [hdist]
    calc
      dist 1 u ≤ (K : ℝ) * dist 1 g := hudist
      _ ≤ K * (2 * dist y z) := mul_le_mul_of_nonneg_left (by rw [hgdist]; exact hb.le) K.coe_nonneg
      _ = (2 * K) * dist y z := by ring

theorem exists_lipschitz_cosetImage_reconstruction (φ : H →* G)
    (Γ : Subgroup H) (Λ : Subgroup G) (hΛ : IsClosed (Λ : Set G))
    (hcover : Λ ⊓ φ.range ≤ Γ.map φ) (f : H → E)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (k * x) = f x)
    (hΓ : ∀ γ ∈ Γ, ∀ x, f (x * γ) = f x)
    (S : Set G) (L K B δ ε : ℝ≥0) (hδ : 0 < δ) (hε : 0 < ε)
    (hf : LipschitzWith L f) (hbound : ∀ x, ‖f x‖ ≤ B)
    (hrep : ∀ y : CosetImage φ Λ, ∃ x : H, projectToCosetImage φ Λ x = y ∧ φ x ∈ S)
    (hgap : ∀ a ∈ S, ∀ b ∈ S, ∀ γ ∈ Λ, dist a (b * γ) < ε → γ ∈ φ.range)
    (hlift : ∀ g ∈ φ.range, dist 1 g < δ → ∃ h : H, φ h = g ∧ dist 1 h ≤ K * dist 1 g) :
    letI := rightCosetMetricSpace Λ hΛ
    ∃ F : CosetImage φ Λ → E,
      (∀ x, F (projectToCosetImage φ Λ x) = f x) ∧
      LipschitzWith (max (L * (2 * K)) (2 * B / (min δ ε / 2))) F ∧ ∀ y, ‖F y‖ ≤ B := by
  let := rightCosetMetricSpace Λ hΛ
  obtain ⟨F, hF, _⟩ := exists_unique_cosetImage_reconstruction φ Γ Λ hcover f hker hΓ
  have hπ := projectToCosetImage_surjective φ Λ
  refine ⟨F, hF, ?_, reconstruction_norm_le _ hπ f F hF hbound⟩
  apply lipschitz_reconstruction_of_local_lifts (projectToCosetImage φ Λ) hπ f F hF
    L (2 * K) B (min δ ε / 2) (by positivity) hf hbound
  exact cosetImage_local_lifts φ Λ hΛ S K δ ε hrep hgap hlift

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {H G E : Type*} [Group H] [Group G] [MetricSpace H] [MetricSpace G]
  [IsIsometricSMul Hᵐᵒᵖ H] [IsIsometricSMul Gᵐᵒᵖ G]
  [IsTopologicalGroup H] [IsTopologicalGroup G] [NormedAddCommGroup E]

omit [IsTopologicalGroup H] in

theorem quotient_local_lifts_of_identity_lifts (φ : H →* G)
    (hφ : Function.Surjective φ) (Λ : Subgroup G) (hΛ : IsClosed (Λ : Set G))
    (K δ : ℝ≥0) (_hδ : 0 < δ)
    (hlift : ∀ g : G, dist 1 g < δ → ∃ h : H, φ h = g ∧ dist 1 h ≤ K * dist 1 g) :
    letI := rightCosetMetricSpace Λ hΛ
    ∀ y z : G ⧸ Λ, dist y z < δ / 2 →
      ∃ x x' : H, (QuotientGroup.mk (φ x) : G ⧸ Λ) = y ∧
        (QuotientGroup.mk (φ x') : G ⧸ Λ) = z ∧ dist x x' ≤ (2 * K) * dist y z := by
  let := rightCosetMetricSpace Λ hΛ
  intro y z hyz
  have hπ : Function.Surjective (fun x : H => (QuotientGroup.mk (φ x) : G ⧸ Λ)) :=
    QuotientGroup.mk_surjective.comp hφ
  obtain ⟨x, hx⟩ := hπ y
  change (QuotientGroup.mk (φ x) : G ⧸ Λ) = y at hx
  by_cases heq : y = z
  · refine ⟨x, x, hx, hx.trans heq, ?_⟩
    simp only [dist_self, heq, mul_zero, le_refl]
  have hd : 0 < dist y z := dist_pos.mpr heq
  obtain ⟨b, hb, hbq⟩ := rightCosetMetricSpace_exists_lift Λ hΛ (φ x) (2 * dist y z) z (by
    rw [hx, dist_comm]
    linarith)
  let g := b * (φ x)⁻¹
  have hgdist : dist 1 g = dist b (φ x) := by
    simpa only [g, mul_inv_cancel, dist_comm] using
      (dist_mul_right (φ x) b (φ x)⁻¹)
  have hgnear : dist 1 g < δ := by rw [hgdist]; linarith
  obtain ⟨u, hu, hudist⟩ := hlift g hgnear
  refine ⟨x, u * x, hx, ?_, ?_⟩
  · rw [map_mul, hu]
    simpa only [g, inv_mul_cancel_right] using hbq
  · have hdist : dist x (u * x) = dist 1 u := by
      simpa only [one_mul] using dist_mul_right (1 : H) u x
    rw [hdist]
    calc
      dist 1 u ≤ (K : ℝ) * dist 1 g := hudist
      _ ≤ K * (2 * dist y z) := mul_le_mul_of_nonneg_left (by rw [hgdist]; exact hb.le) K.coe_nonneg
      _ = (2 * K) * dist y z := by ring

theorem exists_lipschitz_observable_reconstruction (φ : H →* G)
    (hφ : Function.Surjective φ) (Γ : Subgroup H) (Λ : Subgroup G)
    (hΓ : IsClosed (Γ : Set H)) (hΛ : IsClosed (Λ : Set G))
    (hcover : Λ ≤ Γ.map φ) (f : H ⧸ Γ → E)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (QuotientGroup.mk (k * x)) = f (QuotientGroup.mk x))
    (L K B δ : ℝ≥0) (hδ : 0 < δ)
    (hf : letI := rightCosetMetricSpace Γ hΓ; LipschitzWith L f)
    (hbound : ∀ x, ‖f x‖ ≤ B)
    (hlift : ∀ g : G, dist 1 g < δ → ∃ h : H, φ h = g ∧ dist 1 h ≤ K * dist 1 g) :
    letI := rightCosetMetricSpace Λ hΛ
    ∃ F : G ⧸ Λ → E,
      (∀ x, F (QuotientGroup.mk (φ x)) = f (QuotientGroup.mk x)) ∧
      LipschitzWith (max (L * (2 * K)) (2 * B / (δ / 2))) F ∧ ∀ y, ‖F y‖ ≤ B := by
  let := rightCosetMetricSpace Γ hΓ
  let := rightCosetMetricSpace Λ hΛ
  obtain ⟨F, hF, _⟩ := exists_unique_observable_reconstruction φ hφ Γ Λ hcover f hker
  let π : H → G ⧸ Λ := fun x => QuotientGroup.mk (φ x)
  have hπ : Function.Surjective π := QuotientGroup.mk_surjective.comp hφ
  have hf' : LipschitzWith L (fun x : H => f (QuotientGroup.mk x)) := by
    simpa only [mul_one, Function.comp_def] using hf.comp (rightCosetMetricSpace_lipschitz_mk Γ hΓ)
  refine ⟨F, hF, ?_, reconstruction_norm_le π hπ _ F hF (fun x => hbound _)⟩
  apply lipschitz_reconstruction_of_local_lifts π hπ _ F hF L (2 * K) B (δ / 2)
    (by positivity) hf' (fun x => hbound _)
  exact quotient_local_lifts_of_identity_lifts φ hφ Λ hΛ K δ hδ hlift

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {H G : Type*} [Group H] [Group G] [MetricSpace H] [MetricSpace G]
  [IsIsometricSMul Hᵐᵒᵖ H] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G]

theorem exists_ambient_image_reconstruction (φ : H →* G)
    (Γ : Subgroup H) (Λ : Subgroup G) (hΛ : IsClosed (Λ : Set G))
    (hcover : Λ ⊓ φ.range ≤ Γ.map φ) (f : H → ℂ)
    (hker : ∀ k ∈ φ.ker, ∀ x, f (k * x) = f x)
    (hΓ : ∀ γ ∈ Γ, ∀ x, f (x * γ) = f x)
    (S : Set G) (L K B δ ε : ℝ≥0) (hδ : 0 < δ) (hε : 0 < ε)
    (hf : LipschitzWith L f) (hbound : ∀ x, ‖f x‖ ≤ B)
    (hrep : ∀ y : CosetImage φ Λ, ∃ x : H, projectToCosetImage φ Λ x = y ∧ φ x ∈ S)
    (hgap : ∀ a ∈ S, ∀ b ∈ S, ∀ γ ∈ Λ, dist a (b * γ) < ε → γ ∈ φ.range)
    (hlift : ∀ g ∈ φ.range, dist 1 g < δ → ∃ h : H, φ h = g ∧ dist 1 h ≤ K * dist 1 g) :
    letI := rightCosetMetricSpace Λ hΛ
    ∃ F : G ⧸ Λ → ℂ,
      (∀ x, F (QuotientGroup.mk (φ x)) = f x) ∧
      LipschitzWith (2 * max (L * (2 * K)) (2 * B / (min δ ε / 2))) F ∧
      ∀ y, ‖F y‖ ≤ 2 * B := by
  let := rightCosetMetricSpace Λ hΛ
  obtain ⟨F, hF, hLip, hb⟩ := exists_lipschitz_cosetImage_reconstruction φ Γ Λ hΛ hcover
    f hker hΓ S L K B δ ε hδ hε hf hbound hrep hgap hlift
  obtain ⟨u, hu, heq, hub⟩ := exists_complex_extension_from_subset (CosetImage φ Λ) F
    (max (L * (2 * K)) (2 * B / (min δ ε / 2))) B hLip hb
  exact ⟨u, fun x => (heq (projectToCosetImage φ Λ x)).trans (hF x), hu, hub⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedFreeWords
namespace OAI

section

namespace Erdos3

variable {X : Type*} [Fintype X]

theorem freeWordSet_card_le (t : Finset (FreeMonoid X)) (s : ℕ)
    (ht : ∀ w ∈ t, w.length ≤ s) :
    t.card ≤ (s + 1) * (Fintype.card X + 1) ^ s := by
  classical
  let code : t → (Σ n : Fin (s + 1), Fin n.val → X) := fun w =>
    ⟨⟨w.val.toList.length, Nat.lt_succ_of_le (ht w w.property)⟩, w.val.toList.get⟩
  have hinj : Function.Injective code := by
    intro u v huv
    have hl := congrArg (fun z : Σ n : Fin (s + 1), Fin n.val → X => List.ofFn z.2) huv
    change List.ofFn u.val.toList.get = List.ofFn v.val.toList.get at hl
    rw [List.ofFn_get, List.ofFn_get] at hl
    exact Subtype.ext (congrArg FreeMonoid.ofList hl)
  have hcard := Fintype.card_le_of_injective code hinj
  simp only [Fintype.card_coe, Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin] at hcard
  calc
    t.card ≤ ∑ n : Fin (s + 1), Fintype.card X ^ n.val := hcard
    _ ≤ ∑ _n : Fin (s + 1), (Fintype.card X + 1) ^ s := by
      apply Finset.sum_le_sum
      intro n _
      exact (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
        (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ n.isLt))
    _ = _ := by simp

theorem bchProductBracketSupport_card_le (s : ℕ) (xs : List X) :
    (bchProductBracketSupport s xs).card ≤ (s + 1) * (Fintype.card X + 1) ^ s := by
  classical
  let t := (bchProductBracketSupport s xs).image FreeSemigroup.toFreeMonoid
  have h := freeWordSet_card_le t s (by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    simpa only [freeSemigroup_toFreeMonoid_length] using bchProductBracketSupport_length s xs hv)
  simpa only [t, Finset.card_image_of_injective _ FreeSemigroup.toFreeMonoid_injective] using h

end Erdos3

end

section

namespace Erdos3

def BoundedFreeWord (X : Type*) (s : ℕ) := {w : FreeSemigroup X // w.length ≤ s}

variable {X : Type*} {s : ℕ}

def boundedFreeWordCode (w : BoundedFreeWord X s) : Σ n : Fin (s + 1), Fin n.val → X :=
  ⟨⟨w.val.toFreeMonoid.toList.length, by
      exact Nat.lt_succ_of_le ((freeSemigroup_toFreeMonoid_length w.val).le.trans w.property)⟩,
    w.val.toFreeMonoid.toList.get⟩

theorem boundedFreeWordCode_injective : Function.Injective (boundedFreeWordCode (X := X) (s := s)) := by
  intro u v huv
  have he := congrArg (fun z : Σ n : Fin (s + 1), Fin n.val → X => List.ofFn z.2) huv
  change List.ofFn u.val.toFreeMonoid.toList.get = List.ofFn v.val.toFreeMonoid.toList.get at he
  rw [List.ofFn_get, List.ofFn_get] at he
  apply Subtype.ext
  apply FreeSemigroup.toFreeMonoid_injective
  exact congrArg FreeMonoid.ofList he

noncomputable instance boundedFreeWordFintype [Fintype X] : Fintype (BoundedFreeWord X s) :=
  Fintype.ofInjective boundedFreeWordCode boundedFreeWordCode_injective

theorem boundedFreeWord_card_le [Fintype X] :
    Fintype.card (BoundedFreeWord X s) ≤ (s + 1) * (Fintype.card X + 1) ^ s := by
  have hc := Fintype.card_le_of_injective (boundedFreeWordCode (X := X) (s := s))
    boundedFreeWordCode_injective
  simp only [Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin] at hc
  calc
    _ ≤ ∑ n : Fin (s + 1), Fintype.card X ^ n.val := hc
    _ ≤ ∑ _n : Fin (s + 1), (Fintype.card X + 1) ^ s := by
      apply Finset.sum_le_sum
      intro n _
      exact (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
        (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ n.isLt))
    _ = _ := by simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GroupReductionFactors
namespace OAI

section

namespace Erdos3

open scoped Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end Erdos3

end

section

namespace Erdos3

variable {G : Type*} [Group G]

theorem exists_representative_factors_of_reductions (Γ : Subgroup G)
    (H : ℕ → Subgroup G) (s : ℕ) (P : G → Prop)
    (hzero : H 0 = ⊤) (hterminal : H s = ⊥)
    (hstep : ∀ i < s, ∀ g ∈ H i,
      ∃ r, P r ∧ ∃ w ∈ Γ, r⁻¹ * g * w⁻¹ ∈ H (i + 1)) :
    ∀ g : G, ∃ rs : List G, rs.length = s ∧ (∀ r ∈ rs, P r) ∧
      ∃ γ ∈ Γ, g = rs.prod * γ := by
  have haux (n : ℕ) : ∀ i, i + n = s → ∀ g ∈ H i,
      ∃ rs : List G, rs.length = n ∧ (∀ r ∈ rs, P r) ∧
        ∃ γ ∈ Γ, g = rs.prod * γ := by
    induction n with
    | zero =>
      intro i hi g hg
      have his : i = s := by omega
      subst i
      have hg1 : g = 1 := by simpa only [hterminal, Subgroup.mem_bot] using hg
      exact ⟨[], rfl, by simp, 1, Γ.one_mem, by simpa using hg1⟩
    | succ n ih =>
      intro i hi g hg
      obtain ⟨r, hr, w, hw, hrem⟩ := hstep i (by omega) g hg
      obtain ⟨rs, hlen, hP, γ, hγ, heq⟩ := ih (i + 1) (by omega) _ hrem
      refine ⟨r :: rs, by simp [hlen], ?_, γ * w, Γ.mul_mem hγ hw, ?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hr
        · exact hP a ha
      · calc
          g = r * (r⁻¹ * g * w⁻¹) * w := by group
          _ = (r :: rs).prod * (γ * w) := by rw [heq, List.prod_cons]; group
  intro g
  exact haux s 0 (by omega) g (by simp [hzero])

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSubquotientEquiv
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem one_tmul_mem_real_baseChange_iff {V : Type*} [AddCommGroup V] [Module ℚ V]
    (S : Submodule ℚ V) (v : V) : (1 : ℝ) ⊗ₜ[ℚ] v ∈ S.baseChange ℝ ↔ v ∈ S := by
  constructor
  · intro hv
    let : Module.Free ℚ (V ⧸ S) := Module.Free.of_divisionRing ℚ (V ⧸ S)
    have hker : S.baseChange ℝ ≤ LinearMap.ker (S.mkQ.baseChange ℝ) := by
      rw [Submodule.baseChange_eq_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨x, hx, rfl⟩
      change S.mkQ.baseChange ℝ ((1 : ℝ) ⊗ₜ[ℚ] x) = 0
      rw [LinearMap.baseChange_tmul]
      have hxq : S.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hx
      rw [hxq, TensorProduct.tmul_zero]
    have hz : (1 : ℝ) ⊗ₜ[ℚ] S.mkQ v = 0 := hker hv
    have hinj := Module.Flat.tensorProduct_mk_injective (R := ℚ) (S := ℝ) (M := V ⧸ S)
    have hvq : S.mkQ v = 0 := hinj (by simpa only [TensorProduct.mk_apply, map_zero] using hz)
    exact (Submodule.Quotient.mk_eq_zero S).mp hvq
  · exact Submodule.tmul_mem_baseChange_of_mem 1

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

theorem real_baseChange_iSup {I : Sort*} {L : Type*} [AddCommGroup L] [Module ℚ L]
    (P : I → Submodule ℚ L) :
    (⨆ i, P i).baseChange ℝ = ⨆ i, (P i).baseChange ℝ := by
  apply le_antisymm
  · rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro x ⟨y, hy, rfl⟩
    apply Submodule.iSup_induction P hy
      (motive := fun y => (1 : ℝ) ⊗ₜ[ℚ] y ∈ ⨆ i, (P i).baseChange ℝ)
    · intro i y hy
      exact Submodule.mem_iSup_of_mem i (Submodule.tmul_mem_baseChange_of_mem 1 hy)
    · simp only [TensorProduct.tmul_zero, Submodule.zero_mem]
    · intro y z hy hz
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ hy hz
  · apply iSup_le
    intro i
    exact Submodule.baseChange_mono ℝ (le_iSup P i)

theorem real_restrictScalars_iSup {I : Sort*} {L : Type*} [AddCommGroup L]
    [Module ℚ L] [Module ℝ L] [IsScalarTower ℚ ℝ L] (P : I → Submodule ℝ L) :
    (⨆ i, P i).restrictScalars ℚ = ⨆ i, (P i).restrictScalars ℚ := by
  apply le_antisymm
  · intro x hx
    change x ∈ ⨆ i, P i at hx
    apply Submodule.iSup_induction P hx
      (motive := fun y => y ∈ ⨆ i, (P i).restrictScalars ℚ)
    · intro i y hy
      exact Submodule.mem_iSup_of_mem i hy
    · exact Submodule.zero_mem _
    · intro y z hy hz
      exact Submodule.add_mem _ hy hz
  · apply iSup_le
    intro i x hx
    exact Submodule.mem_iSup_of_mem i hx

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem realification_subtype_injective (P : Submodule ℚ V) :
    Function.Injective (P.subtype.baseChange ℝ) := by
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ) P.subtype
    (fun _ _ h => Subtype.ext h)

noncomputable def realificationSubmoduleEquiv (P : Submodule ℚ V) :
    (ℝ ⊗[ℚ] P) ≃ₗ[ℝ] P.baseChange ℝ :=
  LinearEquiv.ofInjective (P.subtype.baseChange ℝ) (realification_subtype_injective P)

@[simp] theorem realificationSubmoduleEquiv_coe (P : Submodule ℚ V) (x : ℝ ⊗[ℚ] P) :
    (realificationSubmoduleEquiv P x : ℝ ⊗[ℚ] V) = P.subtype.baseChange ℝ x := rfl

@[simp] theorem realificationSubmoduleEquiv_tmul (P : Submodule ℚ V) (r : ℝ) (x : P) :
    (realificationSubmoduleEquiv P (r ⊗ₜ[ℚ] x) : ℝ ⊗[ℚ] V) = r ⊗ₜ[ℚ] (x : V) := rfl

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {V W Z : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] [AddCommGroup Z] [Module ℚ Z]

theorem realification_ker (f : V →ₗ[ℚ] W) :
    (LinearMap.ker f).baseChange ℝ = LinearMap.ker (f.baseChange ℝ) := by
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  have h : Function.Exact ((LinearMap.ker f).subtype.baseChange ℝ) (f.baseChange ℝ) :=
    Module.Flat.lTensor_exact ℝ f.exact_subtype_ker_map
  exact (LinearMap.exact_iff.mp h).symm

theorem realification_comap (P : Submodule ℚ W) (f : V →ₗ[ℚ] W) :
    (P.comap f).baseChange ℝ = (P.baseChange ℝ).comap (f.baseChange ℝ) := by
  have he : P.comap f = LinearMap.ker (P.mkQ.comp f) := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  rw [he, realification_ker, LinearMap.baseChange_comp, LinearMap.ker_comp,
    ← realification_ker, Submodule.ker_mkQ]

theorem realification_mkQ_eq_zero_iff (P : Submodule ℚ V) (x : ℝ ⊗[ℚ] V) :
    P.mkQ.baseChange ℝ x = 0 ↔ x ∈ P.baseChange ℝ := by
  change x ∈ LinearMap.ker (P.mkQ.baseChange ℝ) ↔ _
  rw [← realification_ker, Submodule.ker_mkQ]

theorem realification_prod (f : V →ₗ[ℚ] W) (g : V →ₗ[ℚ] Z) (x : ℝ ⊗[ℚ] V) :
    TensorProduct.prodRight ℚ ℝ ℝ W Z ((f.prod g).baseChange ℝ x) =
      (f.baseChange ℝ x, g.baseChange ℝ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp <;> rfl
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]; rfl

theorem realification_prod_eq_zero_iff (f : V →ₗ[ℚ] W) (g : V →ₗ[ℚ] Z)
    (x : ℝ ⊗[ℚ] V) :
    (f.prod g).baseChange ℝ x = 0 ↔ f.baseChange ℝ x = 0 ∧ g.baseChange ℝ x = 0 := by
  constructor
  · intro h
    have he := congrArg (TensorProduct.prodRight ℚ ℝ ℝ W Z) h
    rw [realification_prod, map_zero] at he
    exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
  · intro h
    apply (TensorProduct.prodRight ℚ ℝ ℝ W Z).injective
    rw [realification_prod, map_zero, h.1, h.2]
    rfl

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {E : Type*} [AddCommGroup E] [Module ℚ E] (P Q : Submodule ℚ E)

abbrev RealSubquotient :=
  @HasQuotient.Quotient (P.baseChange ℝ) (Submodule ℝ (P.baseChange ℝ))
    (@Submodule.hasQuotient ℝ (P.baseChange ℝ) _ _ _)
    ((Q.baseChange ℝ).comap (P.baseChange ℝ).subtype)

noncomputable def realSubquotientProjection : P.baseChange ℝ →ₗ[ℝ] (ℝ ⊗[ℚ] (P ⧸ Q.comap P.subtype)) :=
  ((Q.comap P.subtype).mkQ.baseChange ℝ).comp (realificationSubmoduleEquiv P).symm.toLinearMap

theorem realSubquotientProjection_surjective : Function.Surjective (realSubquotientProjection P Q) := by
  have hq : Function.Surjective ((Q.comap P.subtype).mkQ.baseChange ℝ) :=
    LinearMap.lTensor_surjective ℝ (Q.comap P.subtype).mkQ_surjective
  exact hq.comp (realificationSubmoduleEquiv P).symm.surjective

theorem realSubquotientProjection_ker :
    LinearMap.ker (realSubquotientProjection P Q) =
      (Q.baseChange ℝ).comap (P.baseChange ℝ).subtype := by
  ext x
  change (Q.comap P.subtype).mkQ.baseChange ℝ ((realificationSubmoduleEquiv P).symm x) = 0 ↔
    x.val ∈ Q.baseChange ℝ
  rw [realification_mkQ_eq_zero_iff, realification_comap]
  change P.subtype.baseChange ℝ ((realificationSubmoduleEquiv P).symm x) ∈ Q.baseChange ℝ ↔ _
  have he := congrArg Subtype.val ((realificationSubmoduleEquiv P).apply_symm_apply x)
  rw [← realificationSubmoduleEquiv_coe, he]

noncomputable def realSubquotientEquiv :
    (ℝ ⊗[ℚ] (P ⧸ Q.comap P.subtype)) ≃ₗ[ℝ]
      RealSubquotient P Q :=
  (realSubquotientProjection P Q).quotKerEquivOfSurjective (realSubquotientProjection_surjective P Q) |>.symm |>.trans
    (Submodule.quotEquivOfEq _ _ (realSubquotientProjection_ker P Q))

theorem realSubquotientEquiv_project (x : ℝ ⊗[ℚ] P) :
    realSubquotientEquiv P Q ((Q.comap P.subtype).mkQ.baseChange ℝ x) =
      ((Q.baseChange ℝ).comap (P.baseChange ℝ).subtype).mkQ (realificationSubmoduleEquiv P x) := by
  have hx : (Q.comap P.subtype).mkQ.baseChange ℝ x =
      realSubquotientProjection P Q (realificationSubmoduleEquiv P x) := by
    simp only [realSubquotientProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  rw [hx]
  dsimp only [realSubquotientEquiv, LinearEquiv.trans_apply]
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedMultidegree
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def rationalLieInclusion : L →ₗ⁅ℚ⁆ (ℝ ⊗[ℚ] L) where
  toLinearMap := TensorProduct.mk ℚ ℝ L 1
  map_lie' {x y} := by simp [LieAlgebra.ExtendScalars.bracket_tmul]

@[simp]
theorem rationalLieInclusion_apply (x : L) : rationalLieInclusion x = (1 : ℝ) ⊗ₜ[ℚ] x := rfl

theorem rationalLieInclusion_coordinates (e : Basis ι ℚ L) (x : L) (i : ι) :
    (e.baseChange ℝ).repr (rationalLieInclusion x) i = (e.repr x i : ℝ) := by
  simp [Basis.baseChange_repr_tmul, Algebra.smul_def]

theorem rationalLieInclusion_injective (e : Basis ι ℚ L) :
    Function.Injective (rationalLieInclusion : L →ₗ⁅ℚ⁆ (ℝ ⊗[ℚ] L)) := by
  intro x y h
  apply e.repr.injective
  ext i
  have hi := congrArg (fun z => (e.baseChange ℝ).repr z i) h
  rw [rationalLieInclusion_coordinates, rationalLieInclusion_coordinates] at hi
  exact_mod_cast hi

theorem realLieBasis_structure (e : Basis ι ℚ L) (i j k : ι) :
    (e.baseChange ℝ).repr ⁅e.baseChange ℝ i, e.baseChange ℝ j⁆ k =
      (lieStructureConstants e i j k : ℝ) := by
  simp [Basis.baseChange_apply, LieAlgebra.ExtendScalars.bracket_tmul,
    Basis.baseChange_repr_tmul, Algebra.smul_def, lieStructureConstants]

theorem realification_lowerCentralSeries_eq_bot {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :
    LieModule.lowerCentralSeries ℚ (ℝ ⊗[ℚ] L) (ℝ ⊗[ℚ] L) s = ⊥ := by
  have hreal : LieModule.lowerCentralSeries ℝ (ℝ ⊗[ℚ] L) (ℝ ⊗[ℚ] L) s = ⊥ := by
    rw [LieSubmodule.lowerCentralSeries_tensor_eq_baseChange, hnil, LieSubmodule.baseChange_bot]
  apply SetLike.coe_injective
  change (LieModule.lowerCentralSeries ℚ (ℝ ⊗[ℚ] L) (ℝ ⊗[ℚ] L) s : Set (ℝ ⊗[ℚ] L)) = {0}
  rw [LieModule.coe_lowerCentralSeries_eq_int,
    ← LieModule.coe_lowerCentralSeries_eq_int ℝ (ℝ ⊗[ℚ] L) (ℝ ⊗[ℚ] L) s, hreal]
  rfl

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def realificationHom :
    NilpotentLieBCHGroup L s hnil →*
      NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil) :=
  map rationalLieInclusion

@[simp]
theorem realificationHom_coord (g : NilpotentLieBCHGroup L s hnil) :
    (realificationHom g).coord = rationalLieInclusion g.coord := rfl

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def realLayer (i : ℕ) : LieIdeal ℝ (ℝ ⊗[ℚ] L) := (F.layerIdeal i).baseChange ℝ

theorem realLayer_antitone : Antitone F.realLayer := by
  intro i j hij
  exact Submodule.baseChange_mono ℝ (F.antitone hij)

theorem realLayer_one : F.realLayer 1 = ⊤ := by
  have h : F.layerIdeal 1 = ⊤ := by
    ext a
    change a ∈ F.layer 1 ↔ a ∈ (⊤ : Submodule ℚ L)
    rw [F.one_eq_top]
  simp only [realLayer, h, LieSubmodule.baseChange_top]

theorem realLayer_terminal : F.realLayer (s + 1) = ⊥ := by
  have h : F.layerIdeal (s + 1) = ⊥ := by
    ext a
    change a ∈ F.layer (s + 1) ↔ a ∈ (⊥ : Submodule ℚ L)
    rw [F.terminal]
  simp only [realLayer, h, LieSubmodule.baseChange_bot]

theorem lie_realLayer_le (i j : ℕ) : ⁅F.realLayer i, F.realLayer j⁆ ≤ F.realLayer (i + j) := by
  have h : ⁅F.layerIdeal i, F.layerIdeal j⁆ ≤ F.layerIdeal (i + j) := by
    rw [LieSubmodule.lie_le_iff]
    exact fun a ha b hb => F.lie_mem ha hb
  rw [realLayer, realLayer, ← LieSubmodule.lie_baseChange]
  exact Submodule.baseChange_mono ℝ h

theorem realLayer_lie_mem {i j : ℕ} {a b : ℝ ⊗[ℚ] L}
    (ha : a ∈ F.realLayer i) (hb : b ∈ F.realLayer j) : ⁅a, b⁆ ∈ F.realLayer (i + j) :=
  F.lie_realLayer_le i j (LieSubmodule.lie_mem_lie ha hb)

noncomputable def realification : NilpotentLieFiltration (ℝ ⊗[ℚ] L) s where
  layer i := (F.realLayer i).toSubmodule.restrictScalars ℚ
  antitone := F.realLayer_antitone
  one_eq_top := by rw [F.realLayer_one]; rfl
  lie_mem := F.realLayer_lie_mem
  terminal := by rw [F.realLayer_terminal]; rfl

theorem rational_inclusion_mem_realLayer {i : ℕ} {a : L} (ha : a ∈ F.layer i) :
    rationalLieInclusion a ∈ F.realLayer i :=
  LieSubmodule.tmul_mem_baseChange_of_mem 1 ha

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def realLayer (a : σ → ℕ) : LieIdeal ℝ (ℝ ⊗[ℚ] L) := (F.layerIdeal a).baseChange ℝ

theorem realLayer_antitone : Antitone F.realLayer :=
  fun _ _ h => Submodule.baseChange_mono ℝ (F.antitone h)

theorem realLayer_zero : F.realLayer 0 = ⊤ := by
  have h : F.layerIdeal 0 = ⊤ := by
    ext x
    change x ∈ F.layer 0 ↔ x ∈ (⊤ : Submodule ℚ L)
    rw [F.zero_eq_top]
  simp only [realLayer, h, LieSubmodule.baseChange_top]

theorem realLayer_terminal (a : σ → ℕ) (ha : ¬a ≤ bound) : F.realLayer a = ⊥ := by
  have h : F.layerIdeal a = ⊥ := by
    ext x
    change x ∈ F.layer a ↔ x ∈ (⊥ : Submodule ℚ L)
    rw [F.terminal a ha]
  simp only [realLayer, h, LieSubmodule.baseChange_bot]

theorem realLayer_lie_mem {a b : σ → ℕ} {x y : ℝ ⊗[ℚ] L}
    (hx : x ∈ F.realLayer a) (hy : y ∈ F.realLayer b) : ⁅x, y⁆ ∈ F.realLayer (a + b) := by
  have h : ⁅F.layerIdeal a, F.layerIdeal b⁆ ≤ F.layerIdeal (a + b) := by
    rw [LieSubmodule.lie_le_iff]
    exact fun x hx y hy => F.lie_mem hx hy
  have hreal : ⁅F.realLayer a, F.realLayer b⁆ ≤ F.realLayer (a + b) := by
    rw [realLayer, realLayer, ← LieSubmodule.lie_baseChange]
    exact Submodule.baseChange_mono ℝ h
  exact hreal (LieSubmodule.lie_mem_lie hx hy)

theorem realLayer_degree_eq (n : ℕ) :
    (F.ordinary.realLayer n).toSubmodule =
      ⨆ (a : σ → ℕ) (_ha : n ≤ ∑ i, a i), (F.realLayer a).toSubmodule := by
  change (F.ordinary.layer n).baseChange ℝ =
    ⨆ (a : σ → ℕ) (_ha : n ≤ ∑ i, a i), (F.layer a).baseChange ℝ
  rw [F.degree_eq]
  simp only [real_baseChange_iSup]

noncomputable def realification : MultidegreeLieFiltration σ (ℝ ⊗[ℚ] L) s bound where
  ordinary := F.ordinary.realification
  layer a := (F.realLayer a).toSubmodule.restrictScalars ℚ
  antitone := F.realLayer_antitone
  zero_eq_top := by rw [F.realLayer_zero]; rfl
  lie_mem := F.realLayer_lie_mem
  terminal a ha := by rw [F.realLayer_terminal a ha]; rfl
  degree_eq n := by
    change (F.ordinary.realLayer n).toSubmodule.restrictScalars ℚ = _
    rw [F.realLayer_degree_eq]
    simp only [real_restrictScalars_iSup]

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalSpanCoordinates
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem span_submodule_basis (P : Submodule ℚ L) (b : Basis κ ℚ P) :
    Submodule.span ℚ (Set.range (fun j => (b j : L))) = P := by
  change Submodule.span ℚ (Set.range (P.subtype ∘ b)) = P
  rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem real_span_rational_family (P : Submodule ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = P) :
    Submodule.span ℝ (Set.range (fun j => rationalLieInclusion (v j))) = P.baseChange ℝ := by
  rw [← hspan, Submodule.baseChange_span, ← Set.range_comp]
  rfl

theorem realification_layer_eq_span (n : ℕ) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = (LieModule.lowerCentralSeries ℚ L L n).toSubmodule) :
    (LieModule.lowerCentralSeries ℚ (ℝ ⊗[ℚ] L) (ℝ ⊗[ℚ] L) n : Set (ℝ ⊗[ℚ] L)) =
      (Submodule.span ℝ (Set.range (fun j => rationalLieInclusion (v j))) : Set (ℝ ⊗[ℚ] L)) := by
  calc
    _ = (LieModule.lowerCentralSeries ℝ (ℝ ⊗[ℚ] L) (ℝ ⊗[ℚ] L) n : Set (ℝ ⊗[ℚ] L)) := by
      rw [LieModule.coe_lowerCentralSeries_eq_int ℚ,
        LieModule.coe_lowerCentralSeries_eq_int ℝ]
    _ = ((LieModule.lowerCentralSeries ℚ L L n).baseChange ℝ : Set (ℝ ⊗[ℚ] L)) := by
      rw [LieSubmodule.lowerCentralSeries_tensor_eq_baseChange]
    _ = ((LieModule.lowerCentralSeries ℚ L L n).toSubmodule.baseChange ℝ : Set (ℝ ⊗[ℚ] L)) := rfl
    _ = _ := congrArg (fun P : Submodule ℝ (ℝ ⊗[ℚ] L) => (P : Set (ℝ ⊗[ℚ] L)))
      (real_span_rational_family _ v hspan).symm

theorem rationalLieInclusion_integer_combination [Fintype κ] (v : κ → L) (z : κ → ℤ) (m : ℕ) :
    rationalLieInclusion (∑ j, ((z j : ℚ) * (m : ℚ)) • v j) =
      ∑ j, ((z j : ℝ) * (m : ℝ)) • rationalLieInclusion (v j) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  rw [← algebraMap_smul ℝ ((z j : ℚ) * (m : ℚ))]
  simp only [map_mul, map_intCast, map_natCast]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ η L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem real_span_family_coordinates (e : Basis ι ℚ L) (v : κ → L) :
    (Submodule.span ℝ (Set.range (fun j => rationalLieInclusion (v j)))).map
        (e.baseChange ℝ).equivFun.toLinearMap =
      Submodule.span ℝ (Set.range (fun j i => (e.repr (v j) i : ℝ))) := by
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext j i
  exact rationalLieInclusion_coordinates e (v j) i

theorem real_span_family_mem_iff_coordinates (e : Basis ι ℚ L) (v : κ → L)
    (x : ℝ ⊗[ℚ] L) :
    x ∈ Submodule.span ℝ (Set.range (fun j => rationalLieInclusion (v j))) ↔
      (e.baseChange ℝ).equivFun x ∈
        Submodule.span ℝ (Set.range (fun j i => (e.repr (v j) i : ℝ))) := by
  rw [← real_span_family_coordinates e v, Submodule.mem_map_equiv,
    LinearEquiv.symm_apply_apply]

theorem real_span_sum_family (v : κ → L) (w : η → L) :
    Submodule.span ℝ (Set.range (fun j => rationalLieInclusion (Sum.elim v w j))) =
      Submodule.span ℝ (Set.range (fun j => rationalLieInclusion (v j))) ⊔
        Submodule.span ℝ (Set.range (fun j => rationalLieInclusion (w j))) := by
  have heq : (fun j => rationalLieInclusion (Sum.elim v w j)) =
      Sum.elim (fun j => rationalLieInclusion (v j)) (fun j => rationalLieInclusion (w j)) := by
    funext j
    cases j <;> rfl
  rw [heq, Set.Sum.elim_range, Submodule.span_union]

omit [Fintype ι] in
theorem span_conditional_basis (e : Basis ι ℚ L) (S : Set ι) [DecidablePred (· ∈ S)] :
    Submodule.span ℚ (Set.range (fun i => if i ∈ S then e i else 0)) =
      Submodule.span ℚ (e '' S) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (if i ∈ S then e i else 0) ∈ _
    split_ifs with h
    · exact Submodule.subset_span ⟨i, h, rfl⟩
    · exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    apply Submodule.subset_span
    exact ⟨i, by simp only [hi, ↓reduceIte]⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHChartCutoffSmooth
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥} [TopologicalSpace L]

instance : TopologicalSpace (NilpotentLieBCHGroup L s hnil) :=
  TopologicalSpace.induced coord inferInstance

@[fun_prop]
theorem continuous_coord : Continuous (coord : NilpotentLieBCHGroup L s hnil → L) :=
  continuous_induced_dom

@[fun_prop]
theorem continuous_mk : Continuous (fun x : L => (⟨x⟩ : NilpotentLieBCHGroup L s hnil)) :=
  continuous_induced_rng.mpr continuous_id

def coordHomeomorph : NilpotentLieBCHGroup L s hnil ≃ₜ L where
  toFun := coord
  invFun x := ⟨x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_coord
  continuous_invFun := continuous_mk

instance [T2Space L] : T2Space (NilpotentLieBCHGroup L s hnil) :=
  (coordHomeomorph (hnil := hnil)).isEmbedding.t2Space

instance [ContractibleSpace L] : ContractibleSpace (NilpotentLieBCHGroup L s hnil) :=
  (coordHomeomorph (hnil := hnil)).contractibleSpace

theorem isTopologicalGroup_of_continuous_lie [IsTopologicalAddGroup L] [ContinuousConstSMul ℚ L]
    (hlie : Continuous (fun z : L × L => ⁅z.1, z.2⁆)) :
    IsTopologicalGroup (NilpotentLieBCHGroup L s hnil) where
  continuous_mul := by
    change Continuous (fun z : NilpotentLieBCHGroup L s hnil × NilpotentLieBCHGroup L s hnil =>
      (⟨lieBCH s z.1.coord z.2.coord⟩ : NilpotentLieBCHGroup L s hnil))
    have hcoords : Continuous
        (fun z : NilpotentLieBCHGroup L s hnil × NilpotentLieBCHGroup L s hnil =>
          (z.1.coord, z.2.coord)) :=
      (continuous_coord.comp continuous_fst).prodMk (continuous_coord.comp continuous_snd)
    have hbch : Continuous
        (fun z : NilpotentLieBCHGroup L s hnil × NilpotentLieBCHGroup L s hnil =>
          lieBCH s z.1.coord z.2.coord) :=
      Continuous.comp
        (g := fun z : L × L => lieBCH s z.1 z.2)
        (f := fun z : NilpotentLieBCHGroup L s hnil × NilpotentLieBCHGroup L s hnil =>
          (z.1.coord, z.2.coord))
        (continuous_lieBCH (L := L) hlie s) hcoords
    exact (continuous_mk (hnil := hnil)).comp hbch
  continuous_inv := by
    change Continuous (fun z : NilpotentLieBCHGroup L s hnil =>
      (⟨-z.coord⟩ : NilpotentLieBCHGroup L s hnil))
    exact (continuous_mk (hnil := hnil)).comp (continuous_coord (hnil := hnil)).neg

section Real

variable [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L] [FiniteDimensional ℝ L]

instance : IsTopologicalGroup (NilpotentLieBCHGroup L s hnil) := by
  let : ContinuousConstSMul ℚ L := ⟨fun q => by
    simpa only [algebraMap_smul] using
      (continuous_const_smul (algebraMap ℚ ℝ q) : Continuous (fun x : L => algebraMap ℚ ℝ q • x))⟩
  exact isTopologicalGroup_of_continuous_lie continuous_lie_finiteDimensional

end Real

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Topology

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def basisHomeomorph (e : Basis ι ℝ L) :
    NilpotentLieBCHGroup L s hnil ≃ₜ (ι → ℝ) :=
  (coordHomeomorph (hnil := hnil)).trans e.equivFunL.toHomeomorph

@[simp]
theorem basisHomeomorph_apply (e : Basis ι ℝ L) (g : NilpotentLieBCHGroup L s hnil) :
    basisHomeomorph e g = e.equivFun g.coord := rfl

theorem closed_discrete_subgroup_of_grid (e : Basis ι ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l) :
    IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)) ∧
      IsDiscrete (Γ : Set (NilpotentLieBCHGroup L s hnil)) := by
  let f := basisHomeomorph (hnil := hnil) e
  have hsub : (Γ : Set (NilpotentLieBCHGroup L s hnil)) ⊆ f ⁻¹' realDenominatorGrid l :=
    fun g hg => hgrid g hg
  have hd : IsDiscrete (f ⁻¹' realDenominatorGrid l) :=
    (isDiscrete_realDenominatorGrid l hl).preimage f.continuous.continuousOn f.injective
  have hc : IsClosed (f ⁻¹' realDenominatorGrid l) :=
    (isClosed_realDenominatorGrid l).preimage f.continuous
  exact ⟨isClosed_of_subset_discrete_closed hsub hd hc, hd.mono hsub⟩

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]

noncomputable def realLieSubalgebraOverRat (K : LieSubalgebra ℝ L) : LieSubalgebra ℚ L :=
  { K.toSubmodule.restrictScalars ℚ with lie_mem' := K.lie_mem }

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def realLieSubgroup (K : LieSubalgebra ℝ L) : Subgroup (NilpotentLieBCHGroup L s hnil) :=
  subgroup (realLieSubalgebraOverRat K)

variable [TopologicalSpace L]

variable [IsTopologicalAddGroup L] [ContinuousSMul ℝ L]

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

def coordinateBox (e : Basis ι ℝ L) (B : ℝ) : Set (NilpotentLieBCHGroup L s hnil) :=
  {g | ∀ i, |e.repr g.coord i| ≤ B}

variable [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

@[instance_reducible]
noncomputable def basisChartedSpace (e : Basis ι ℝ L) :
    ChartedSpace (ι → ℝ) (NilpotentLieBCHGroup L s hnil) :=
  (basisHomeomorph (hnil := hnil) e).isOpenEmbedding.singletonChartedSpace

variable (e : Basis ι ℝ L)

theorem isManifold_basis (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    IsManifold 𝓘(ℝ, ι → ℝ) n (NilpotentLieBCHGroup L s hnil) :=
  (basisHomeomorph e).isOpenEmbedding.isManifold_singleton

theorem contMDiff_basisHomeomorph (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) n (basisHomeomorph (hnil := hnil) e) :=
  contMDiff_isOpenEmbedding (basisHomeomorph e).isOpenEmbedding

theorem contMDiff_basisHomeomorph_symm (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) n (basisHomeomorph (hnil := hnil) e).symm := by
  let := basisChartedSpace (hnil := hnil) e
  apply ContMDiff.of_comp_isOpenEmbedding (basisHomeomorph e).isOpenEmbedding
  have heq : (basisHomeomorph (hnil := hnil) e) ∘ (basisHomeomorph e).symm = id :=
    funext (fun x => (basisHomeomorph e).apply_symm_apply x)
  rw [heq]
  exact contMDiff_id

variable [IsScalarTower ℚ ℝ L]

theorem lieGroup_basis (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    LieGroup 𝓘(ℝ, ι → ℝ) n (NilpotentLieBCHGroup L s hnil) := by
  let := basisChartedSpace (hnil := hnil) e
  refine
    { __ := isManifold_basis (hnil := hnil) e n
      contMDiff_mul := ?_
      contMDiff_inv := ?_ }
  · apply ContMDiff.of_comp_isOpenEmbedding (basisHomeomorph e).isOpenEmbedding
    have hcoords : ContMDiff (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ))
        𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) n
        (fun z : NilpotentLieBCHGroup L s hnil × NilpotentLieBCHGroup L s hnil =>
          (basisHomeomorph e z.1, basisHomeomorph e z.2)) :=
      ((contMDiff_basisHomeomorph e n).comp contMDiff_fst).prodMk_space
        ((contMDiff_basisHomeomorph e n).comp contMDiff_snd)
    have hbch := (contDiff_coordinateBCH (n := n) e s).contMDiff.comp hcoords
    have he : (basisHomeomorph e) ∘ (fun p : NilpotentLieBCHGroup L s hnil ×
          NilpotentLieBCHGroup L s hnil => p.1 * p.2) =
        ((fun z => e.equivFun (lieBCH s (e.equivFun.symm z.1) (e.equivFun.symm z.2))) ∘ fun z =>
          ((basisHomeomorph e) z.1, (basisHomeomorph e) z.2)) := by
      funext z
      simp only [Function.comp_apply, basisHomeomorph_apply, LinearEquiv.symm_apply_apply]
      rfl
    rw [he]
    exact hbch
  · apply ContMDiff.of_comp_isOpenEmbedding (basisHomeomorph e).isOpenEmbedding
    have hneg := (contDiff_neg (𝕜 := ℝ) (F := ι → ℝ) (n := n)).contMDiff.comp
      (contMDiff_basisHomeomorph (hnil := hnil) e n)
    have heq : (basisHomeomorph (hnil := hnil) e) ∘ (fun z => z⁻¹) =
        (fun z => -z) ∘ (basisHomeomorph e) := by
      funext z i
      change e.equivFun (-z.coord) i = -(e.equivFun z.coord i)
      simp only [map_neg, Pi.neg_apply]
    rw [heq]
    exact hneg

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]

local notation "E" => ℝ ⊗[ℚ] L
local notation "G" => NilpotentLieBCHGroup E s (realification_lowerCentralSeries_eq_bot hnil)

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] in

theorem realification_layer_reduction_in_cell {κ : Type*} [Fintype κ] (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ) (n : ℕ) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = (LieModule.lowerCentralSeries ℚ L L n).toSubmodule) :
    ∀ g : G, g.coord ∈ LieModule.lowerCentralSeries ℚ E E n →
      ∃ r ∈ (fun x : E => (⟨x⟩ : G)) ''
        boundedSpanCell (fun j => rationalLieInclusion (v j)) (rationalSpanGridStep e v l : ℝ),
      ∃ w ∈ Γ.map NilpotentLieBCHGroup.realificationHom,
        (r⁻¹ * g * w⁻¹).coord ∈ LieModule.lowerCentralSeries ℚ E E (n + 1) := by
  classical
  let m := rationalSpanGridStep e v l
  have hm : 0 < m := rationalSpanGridStep_pos e v l hl
  let vR : κ → E := fun j => rationalLieInclusion (v j)
  intro g hg
  have hspanreal : (LieModule.lowerCentralSeries ℚ E E n : Set E) =
      (Submodule.span ℝ (Set.range vR) : Set E) := realification_layer_eq_span n v hspan
  have hgspan : g.coord ∈ Submodule.span ℝ (Set.range vR) :=
    (Set.ext_iff.mp hspanreal g.coord).mp hg
  obtain ⟨r, hr, z, hdecomp⟩ := exists_bounded_span_remainder vR (m : ℝ)
    (by exact_mod_cast hm) g.coord hgspan
  let wQ : L := ∑ j, ((z j : ℚ) * (m : ℚ)) • v j
  have hwQ : (⟨wQ⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ := by
    have h := hinner (rationalSpanGridStep_combination e v l z)
    change (⟨e.equivFun.symm (e.equivFun wQ)⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ at h
    simpa only [LinearEquiv.symm_apply_apply] using h
  have hdecomp' : g.coord = r + rationalLieInclusion wQ := by
    change g.coord = r + rationalLieInclusion (∑ j, ((z j : ℚ) * (m : ℚ)) • v j)
    rw [rationalLieInclusion_integer_combination v z m]
    exact hdecomp
  have hrLayer : r ∈ LieModule.lowerCentralSeries ℚ E E n :=
    (Set.ext_iff.mp hspanreal r).mpr (boundedSpanCell_subset_span vR (m : ℝ) hr)
  have hwLayer : rationalLieInclusion wQ ∈ LieModule.lowerCentralSeries ℚ E E n := by
    have h := (LieModule.lowerCentralSeries ℚ E E n).sub_mem hg hrLayer
    rwa [hdecomp', add_sub_cancel_left] at h
  have hbracket : ⁅r, rationalLieInclusion wQ⁆ ∈ LieModule.lowerCentralSeries ℚ E E (n + 1) := by
    rw [LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (by simp) hwLayer
  refine ⟨⟨r⟩, ⟨r, hr, rfl⟩, NilpotentLieBCHGroup.realificationHom ⟨wQ⟩,
    Subgroup.mem_map.mpr ⟨⟨wQ⟩, hwQ, rfl⟩, ?_⟩
  have hg' : g = (⟨r + rationalLieInclusion wQ⟩ : G) := NilpotentLieBCHGroup.ext hdecomp'
  rw [hg']
  exact NilpotentLieBCHGroup.additive_remainder_mem (realification_lowerCentralSeries_eq_bot hnil)
    (LieModule.lowerCentralSeries ℚ E E (n + 1)) r (rationalLieInclusion wQ) hbracket

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem realificationHom_coordinates (e : Basis ι ℚ L) (g : NilpotentLieBCHGroup L s hnil) :
    (e.baseChange ℝ).equivFun (realificationHom g).coord = fun i => (e.repr g.coord i : ℝ) := by
  funext i
  exact rationalLieInclusion_coordinates e g.coord i

theorem realification_subgroup_grid (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    ∀ g ∈ Γ.map realificationHom,
      (e.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid l := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
  rw [realificationHom_coordinates, real_cast_mem_denominatorGrid_iff]
  apply hgrid
  change (⟨e.equivFun.symm (e.equivFun a.coord)⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ
  simpa only [LinearEquiv.symm_apply_apply] using ha

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem realification_subgroup_closed_discrete (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    IsClosed (Γ.map realificationHom : Set
      (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))) ∧
    IsDiscrete (Γ.map realificationHom : Set
      (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))) :=
  closed_discrete_subgroup_of_grid (e.baseChange ℝ) (Γ.map realificationHom) l hl
    (realification_subgroup_grid e Γ l hgrid)

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module _root_.Set Manifold
open scoped Manifold ContDiff Topology

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module _root_.Set Manifold
open scoped Manifold ContDiff Topology

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHConjugationLinear
namespace OAI

section

namespace Erdos3

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ}

attribute [local instance] LieRing.ofAssociativeRing

theorem lieBCH_eq_of_step_le (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (hst : s ≤ t) (a b : L) : lieBCH t a b = lieBCH s a b := by
  let x : Fin 2 → FreeLieAlgebra ℚ (Fin 2) := FreeLieAlgebra.of ℚ
  let F := truncatedSeriesFiltration (A := FreeAlgebra ℚ (Fin 2)) s
  have hx (i : Fin 2) : scaledFreeGenerator s i ∈ F.layer 1 := scaledFreeGenerator_mem_layer s i
  have h : scaledFreeLieEval s (lieBCH t (x 0) (x 1)) =
      scaledFreeLieEval s (lieBCH s (x 0) (x 1)) := by
    simp only [map_lieBCH, x, scaledFreeLieEval_of]
    rw [(F.extend hst).lieBCH_eq (hx 0) (hx 1), F.lieBCH_eq (hx 0) (hx 1)]
  have he := lie_lift_eq_of_scaledFreeLieEval_eq ![a, b] hnil h
  simpa only [map_lieBCH, x, FreeLieAlgebra.lift_of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] using he

theorem lieBCH_eq_of_nilpotent_steps (hs : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (ht : LieModule.lowerCentralSeries ℚ L L t = ⊥) (a b : L) : lieBCH s a b = lieBCH t a b := by
  rcases le_total s t with hst | hts
  · exact (lieBCH_eq_of_step_le hs hst a b).symm
  · exact lieBCH_eq_of_step_le ht hts a b

theorem map_lieBCH_of_nilpotent_steps (φ : L →ₗ⁅ℚ⁆ M)
    (hs : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (ht : LieModule.lowerCentralSeries ℚ M M t = ⊥) (a b : L) :
    φ (lieBCH s a b) = lieBCH t (φ a) (φ b) := by
  rcases le_total s t with hst | hts
  · rw [← lieBCH_eq_of_step_le hs hst, map_lieBCH]
  · rw [map_lieBCH, lieBCH_eq_of_step_le ht hts]

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L M N : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [LieRing N] [LieAlgebra ℚ N] {s t u : ℕ}
  {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}
  {hN : LieModule.lowerCentralSeries ℚ N N u = ⊥}

noncomputable def mapOfSteps (φ : L →ₗ⁅ℚ⁆ M) :
    NilpotentLieBCHGroup L s hL →* NilpotentLieBCHGroup M t hM where
  toFun g := ⟨φ g.coord⟩
  map_one' := ext (map_zero φ)
  map_mul' g h := ext (map_lieBCH_of_nilpotent_steps φ hL hM g.coord h.coord)

@[simp] theorem mapOfSteps_coord (φ : L →ₗ⁅ℚ⁆ M) (g : NilpotentLieBCHGroup L s hL) :
    (mapOfSteps (hM := hM) φ g).coord = φ g.coord := rfl

theorem mapOfSteps_injective (φ : L →ₗ⁅ℚ⁆ M) (hφ : Function.Injective φ) :
    Function.Injective (mapOfSteps (hL := hL) (hM := hM) φ) := by
  intro g h heq
  exact ext (hφ (congrArg coord heq))

noncomputable def changeStep (hs : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (ht : LieModule.lowerCentralSeries ℚ L L t = ⊥) :
    NilpotentLieBCHGroup L s hs ≃* NilpotentLieBCHGroup L t ht where
  toFun g := ⟨g.coord⟩
  invFun g := ⟨g.coord⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' g h := ext (lieBCH_eq_of_nilpotent_steps hs ht g.coord h.coord)

@[simp] theorem changeStep_coord (hs : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (ht : LieModule.lowerCentralSeries ℚ L L t = ⊥) (g : NilpotentLieBCHGroup L s hs) :
    (changeStep hs ht g).coord = g.coord := rfl

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

theorem bchSubgroupCoordinates_comap_of_steps [DecidableEq κ]
    (b : Basis κ ℚ M) (e : Basis ι ℚ L)
    (φ : M →ₗ⁅ℚ⁆ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) :
    bchSubgroupCoordinates b (Γ.comap (NilpotentLieBCHGroup.mapOfSteps (hL := hM) φ)) =
      (LinearMap.toMatrix b e φ.toLinearMap).mulVec ⁻¹' bchSubgroupCoordinates e Γ := by
  ext x
  change ((⟨φ (b.equivFun.symm x)⟩ : NilpotentLieBCHGroup L s hL) ∈ Γ) ↔
    ((⟨e.equivFun.symm (LinearMap.toMatrix b e φ.toLinearMap *ᵥ x)⟩ :
      NilpotentLieBCHGroup L s hL) ∈ Γ)
  rw [basisMatrix_mulVec, LinearEquiv.symm_apply_apply]
  rfl

theorem exists_bchSubgroup_comap_grid_of_steps [DecidableEq ι] [DecidableEq κ]
    (b : Basis κ ℚ M) (e : Basis ι ℚ L) (φ : M →ₗ⁅ℚ⁆ L) (hφ : Function.Injective φ)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) {H l : ℕ} (hHpos : 1 ≤ H) (hlpos : 0 < l)
    (hB : ∀ i j, RationalHeightLE (LinearMap.toMatrix b e φ.toLinearMap i j) H)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p) (hr : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b
        (Γ.comap (NilpotentLieBCHGroup.mapOfSteps (hL := hM) φ)) ∧
      bchSubgroupCoordinates b
        (Γ.comap (NilpotentLieBCHGroup.mapOfSteps (hL := hM) φ)) ⊆ denominatorGrid N := by
  rw [bchSubgroupCoordinates_comap_of_steps b e φ Γ]
  exact exists_preimage_grid_exp_bound (LinearMap.toMatrix b e φ.toLinearMap)
    (Matrix.mulVec_injective_iff.mp (basisMatrix_injective b e φ.toLinearMap hφ))
    hHpos hlpos hB _ hinner houter hp hd hr hH hl

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L)

noncomputable def rightTranslate (g : NilpotentLieBCHGroup L s hnil) (x : ι → ℝ) : ι → ℝ :=
  basisHomeomorph e ((basisHomeomorph e).symm x * g)

@[simp] theorem rightTranslate_coordinates (g h : NilpotentLieBCHGroup L s hnil) :
    rightTranslate e h (basisHomeomorph e g) = basisHomeomorph e (g * h) := by
  simp only [rightTranslate, Homeomorph.symm_apply_apply]

@[simp] theorem rightTranslate_one : rightTranslate (hnil := hnil) e 1 = id := by
  funext x
  simp only [rightTranslate, mul_one, Homeomorph.apply_symm_apply, id_eq]

theorem rightTranslate_comp (g h : NilpotentLieBCHGroup L s hnil) :
    rightTranslate e h ∘ rightTranslate e g = rightTranslate e (g * h) := by
  funext x
  simp only [Function.comp_apply, rightTranslate, Homeomorph.symm_apply_apply, mul_assoc]

variable [IsScalarTower ℚ ℝ L]

theorem contDiff_rightTranslate (g : NilpotentLieBCHGroup L s hnil) (n : ℕ∞ω) :
    ContDiff ℝ n (rightTranslate e g) := by
  let := basisChartedSpace (hnil := hnil) e
  let := lieGroup_basis (hnil := hnil) e n
  exact ((contMDiff_basisHomeomorph e n).comp
    ((contMDiff_basisHomeomorph_symm e n).mul contMDiff_const)).contDiff

theorem rightTranslate_fderiv_leftInverse (g : NilpotentLieBCHGroup L s hnil) (x : ι → ℝ) :
    (fderiv ℝ (rightTranslate e g⁻¹) (rightTranslate e g x)).comp
      (fderiv ℝ (rightTranslate e g) x) = ContinuousLinearMap.id ℝ (ι → ℝ) := by
  have hg := (contDiff_rightTranslate e g 1).differentiable (by decide)
  have hi := (contDiff_rightTranslate e g⁻¹ 1).differentiable (by decide)
  rw [← fderiv_comp x hi.differentiableAt hg.differentiableAt,
    rightTranslate_comp, mul_inv_cancel, rightTranslate_one, fderiv_id]

theorem rightTranslate_fderiv_injective (g : NilpotentLieBCHGroup L s hnil) (x : ι → ℝ) :
    Function.Injective (fderiv ℝ (rightTranslate e g) x) := by
  intro v w hvw
  have h := congrArg (fderiv ℝ (rightTranslate e g⁻¹) (rightTranslate e g x)) hvw
  simpa only [← ContinuousLinearMap.comp_apply, rightTranslate_fderiv_leftInverse,
    ContinuousLinearMap.id_apply] using h

noncomputable def rightVelocity (g : NilpotentLieBCHGroup L s hnil) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  fderiv ℝ (rightTranslate e g⁻¹) (basisHomeomorph e g)

theorem rightVelocity_injective (g : NilpotentLieBCHGroup L s hnil) :
    Function.Injective (rightVelocity e g) :=
  rightTranslate_fderiv_injective e g⁻¹ (basisHomeomorph e g)

omit [IsScalarTower ℚ ℝ L] in
@[simp] theorem rightVelocity_one :
    rightVelocity (hnil := hnil) e 1 = ContinuousLinearMap.id ℝ (ι → ℝ) := by
  simp only [rightVelocity, inv_one, rightTranslate_one, fderiv_id]

theorem rightVelocity_mul (g h : NilpotentLieBCHGroup L s hnil) :
    (rightVelocity e (g * h)).comp (fderiv ℝ (rightTranslate e h) (basisHomeomorph e g)) =
      rightVelocity e g := by
  have hh := (contDiff_rightTranslate e h 1).differentiable (by decide)
  have hi := (contDiff_rightTranslate e (g * h)⁻¹ 1).differentiable (by decide)
  unfold rightVelocity
  rw [← rightTranslate_coordinates e g h, ← fderiv_comp _ hi.differentiableAt hh.differentiableAt,
    rightTranslate_comp]
  simp only [mul_inv_rev, mul_inv_cancel_left]

theorem contDiff_rightVelocity :
    ContDiff ℝ ∞ (fun x : ι → ℝ => rightVelocity (hnil := hnil) e ((basisHomeomorph e).symm x)) := by
  have h : ContDiff ℝ ∞ (fun p : (ι → ℝ) × (ι → ℝ) =>
      e.equivFun (lieBCH s (e.equivFun.symm p.2) (e.equivFun.symm (-p.1)))) :=
    ContDiff.comp
      (g := fun z : (ι → ℝ) × (ι → ℝ) =>
        e.equivFun (lieBCH s (e.equivFun.symm z.1) (e.equivFun.symm z.2)))
      (f := fun p : (ι → ℝ) × (ι → ℝ) => (p.2, -p.1))
      (contDiff_coordinateBCH (n := ∞) e s) (contDiff_snd.prodMk contDiff_fst.neg)
  have hd : ContDiff ℝ ∞ (fun x : ι → ℝ =>
      fderiv ℝ (fun y => e.equivFun (lieBCH s (e.equivFun.symm y) (e.equivFun.symm (-x)))) x) :=
    h.fderiv contDiff_id (by simp)
  convert hd using 1
  funext x
  unfold rightVelocity
  rw [Homeomorph.apply_symm_apply]
  apply congrArg (fun f : (ι → ℝ) → (ι → ℝ) => fderiv ℝ f x)
  funext y
  change e.equivFun (lieBCH s (e.equivFun.symm y) (-e.equivFun.symm x)) = _
  rw [map_neg]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open scoped ContDiff

noncomputable def coordinateDotForm {ι : Type*} [Fintype ι] :
    (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
    (ContinuousLinearMap.proj i) (ContinuousLinearMap.proj i)

@[simp] theorem coordinateDotForm_apply {ι : Type*} [Fintype ι] (v w : ι → ℝ) :
    coordinateDotForm v w = ∑ i, v i * w i := by
  simp [coordinateDotForm]

theorem contDiff_bilinearComp_self {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω}
    (B : F →L[ℝ] F →L[ℝ] ℝ) (T : E → F →L[ℝ] F) (hT : ContDiff ℝ n T) :
    ContDiff ℝ n (fun x => B.bilinearComp (T x) (T x)) := by
  have hflip : ContDiff ℝ n (fun A : F →L[ℝ] F →L[ℝ] ℝ => A.flip) :=
    (show IsBoundedLinearMap ℝ (fun A : F →L[ℝ] F →L[ℝ] ℝ => A.flip) from
      { map_add := ContinuousLinearMap.flip_add
        map_smul := ContinuousLinearMap.flip_smul
        bound := ⟨1, zero_lt_one, fun A => by simp only [one_mul, ContinuousLinearMap.opNorm_flip, le_refl]⟩ }).contDiff
  exact hflip.comp ((hflip.comp (contDiff_const.clm_comp hT)).clm_comp hT)

end Erdos3

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L)

noncomputable def rightInnerForm (g : NilpotentLieBCHGroup L s hnil) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ :=
  coordinateDotForm.bilinearComp (rightVelocity e g) (rightVelocity e g)

theorem rightInnerForm_apply (g : NilpotentLieBCHGroup L s hnil) (v w : ι → ℝ) :
    rightInnerForm e g v w = ∑ i, rightVelocity e g v i * rightVelocity e g w i := by
  simp only [rightInnerForm, ContinuousLinearMap.bilinearComp_apply, coordinateDotForm_apply]

theorem rightInnerForm_symm (g : NilpotentLieBCHGroup L s hnil) (v w : ι → ℝ) :
    rightInnerForm e g v w = rightInnerForm e g w v := by
  simp only [rightInnerForm_apply, mul_comm]

@[simp] theorem rightInnerForm_one : rightInnerForm (hnil := hnil) e 1 = coordinateDotForm := by
  ext v w
  simp only [rightInnerForm, rightVelocity_one, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.id_apply]

variable [IsScalarTower ℚ ℝ L]

theorem rightInnerForm_pos (g : NilpotentLieBCHGroup L s hnil) (v : ι → ℝ) (hv : v ≠ 0) :
    0 < rightInnerForm e g v v := by
  have hne : rightVelocity e g v ≠ 0 := by
    intro h
    apply hv
    exact (rightVelocity_injective e g) (h.trans (map_zero _).symm)
  obtain ⟨i, hi⟩ : ∃ i, rightVelocity e g v i ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  rw [rightInnerForm_apply]
  exact (Finset.sum_pos_iff_of_nonneg (fun j _ => mul_self_nonneg _)).mpr
    ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

theorem rightInnerForm_right_invariant (g h : NilpotentLieBCHGroup L s hnil) (v w : ι → ℝ) :
    rightInnerForm e (g * h)
      (fderiv ℝ (rightTranslate e h) (basisHomeomorph e g) v)
      (fderiv ℝ (rightTranslate e h) (basisHomeomorph e g) w) = rightInnerForm e g v w := by
  have hv := congrArg (fun T : (ι → ℝ) →L[ℝ] (ι → ℝ) => T v) (rightVelocity_mul e g h)
  have hw := congrArg (fun T : (ι → ℝ) →L[ℝ] (ι → ℝ) => T w) (rightVelocity_mul e g h)
  simp only [ContinuousLinearMap.comp_apply] at hv hw
  simp only [rightInnerForm_apply, hv, hw]

theorem contDiff_rightInnerForm :
    ContDiff ℝ ∞ (fun x : ι → ℝ => rightInnerForm (hnil := hnil) e ((basisHomeomorph e).symm x)) :=
  contDiff_bilinearComp_self (E := ι → ℝ) (F := ι → ℝ) (n := ∞) coordinateDotForm
    (fun x => rightVelocity (hnil := hnil) e ((basisHomeomorph e).symm x))
    (contDiff_rightVelocity (hnil := hnil) e)

theorem rightInnerForm_isVonNBounded (g : NilpotentLieBCHGroup L s hnil) :
    Bornology.IsVonNBounded ℝ {v : ι → ℝ | rightInnerForm e g v v < 1} := by
  let A := fderiv ℝ (rightTranslate e g)
    (rightTranslate e g⁻¹ (basisHomeomorph e g))
  have hleft : A.comp (rightVelocity e g) = ContinuousLinearMap.id ℝ (ι → ℝ) := by
    simpa only [inv_inv, A, rightVelocity] using
      rightTranslate_fderiv_leftInverse e g⁻¹ (basisHomeomorph e g)
  apply (NormedSpace.isVonNBounded_iff' ℝ).mpr
  refine ⟨‖A‖, ?_⟩
  intro v hv
  change rightInnerForm e g v v < 1 at hv
  have hTv : ‖rightVelocity e g v‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    have hi : rightVelocity e g v i * rightVelocity e g v i ≤ rightInnerForm e g v v := by
      rw [rightInnerForm_apply]
      exact Finset.single_le_sum (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> nlinarith
  have heq : A (rightVelocity e g v) = v := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun T : (ι → ℝ) →L[ℝ] (ι → ℝ) => T v) hleft
  calc
    ‖v‖ = ‖A (rightVelocity e g v)‖ := congrArg norm heq.symm
    _ ≤ ‖A‖ * ‖rightVelocity e g v‖ := A.le_opNorm _
    _ ≤ ‖A‖ := mul_le_of_le_one_right (norm_nonneg _) hTv

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module _root_.MvPolynomial
open scoped NNReal Topology

theorem lieBCH_right_coordinates_sub_bound {ι L : Type*} [Fintype ι]
    [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) {H s : ℕ}
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (x y z : L) {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hx : ∀ i, |e.repr x i| ≤ B) (hy : ∀ i, |e.repr y i| ≤ B)
    (hz : ∀ i, |e.repr z i| ≤ B) (hxy : ∀ i, |e.repr x i - e.repr y i| ≤ δ) (k : ι) :
    |e.repr (lieBCH s x z) k - e.repr (lieBCH s y z) k| ≤
      bchBoxCoordinateBound s (Fintype.card ι) H B * δ := by
  classical
  let P := bchCoordinatePolynomial c s k
  let v : Fin 2 × ι → ℝ := fun i => e.repr (![x, z] i.1) i.2
  let w : Fin 2 × ι → ℝ := fun i => e.repr (![y, z] i.1) i.2
  have hdegree : P.totalDegree ≤ s := bchCoordinatePolynomial_totalDegree c s k
  have hv (i : Fin 2 × ι) : |v i| ≤ B := by
    rcases i with ⟨j, i⟩
    fin_cases j
    · exact hx i
    · exact hz i
  have hw (i : Fin 2 × ι) : |w i| ≤ B := by
    rcases i with ⟨j, i⟩
    fin_cases j
    · exact hy i
    · exact hz i
  have hvw (i : Fin 2 × ι) : |v i - w i| ≤ δ := by
    rcases i with ⟨j, i⟩
    fin_cases j
    · exact hxy i
    · simpa [v, w] using hδ
  have hcoeff (m) : |((P.coeff m : ℚ) : ℝ)| ≤ bchCoordinateHeight s (Fintype.card ι) H :=
    (bchCoordinatePolynomial_height c hc s k m).abs_real_le
  have h := abs_aeval_sub_aeval_box_bound P v w (Nat.cast_nonneg _) hB hδ hcoeff hv hw hvw hdegree
  have hevalv : aeval v P = e.repr (lieBCH s x z) k :=
    bchCoordinatePolynomial_eval_over e c hstructure s x z k
  have hevalw : aeval w P = e.repr (lieBCH s y z) k :=
    bchCoordinatePolynomial_eval_over e c hstructure s y z k
  rw [hevalv, hevalw] at h
  have hcard := polynomial_support_card_le P hdegree
  apply h.trans
  dsimp only [bchBoxCoordinateBound]
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
  gcongr
  exact_mod_cast hcard

namespace NilpotentLieBCHGroup

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem lipschitzOn_rightTranslate_box (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (g : NilpotentLieBCHGroup L s hnil) (B : ℝ) (hB : 1 ≤ B)
    (hg : ∀ i, |e.repr g.coord i| ≤ B) :
    LipschitzOnWith ⟨bchBoxCoordinateBound s (Fintype.card ι) H B,
      bchBoxCoordinateBound_nonneg _ _ _ (by linarith)⟩
      (rightTranslate e g) {v | ∀ i, |v i| ≤ B} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv w hw
  change ∀ i, |v i| ≤ B at hv
  change ∀ i, |w i| ≤ B at hw
  apply (dist_pi_le_iff (mul_nonneg
    (bchBoxCoordinateBound_nonneg _ _ _ (by linarith : 0 ≤ B)) dist_nonneg)).mpr
  intro k
  rw [Real.dist_eq]
  change |e.equivFun (lieBCH s (e.equivFun.symm v) g.coord) k -
    e.equivFun (lieBCH s (e.equivFun.symm w) g.coord) k| ≤ _
  simp only [Basis.equivFun_apply]
  apply lieBCH_right_coordinates_sub_bound e c hstructure hc _ _ _ hB dist_nonneg
  · simpa only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using hv
  · simpa only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using hw
  · exact hg
  · intro i
    simpa only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply, Real.dist_eq] using
      dist_le_pi_dist v w i

theorem norm_fderiv_rightTranslate_zero_le (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (g : NilpotentLieBCHGroup L s hnil) (B : ℝ) (hB : 1 ≤ B)
    (hg : ∀ i, |e.repr g.coord i| ≤ B) :
    ‖fderiv ℝ (rightTranslate e g) 0‖ ≤ bchBoxCoordinateBound s (Fintype.card ι) H B := by
  apply norm_fderiv_le_of_lipschitzOn ℝ ?_ (lipschitzOn_rightTranslate_box e c hstructure hc g B hB hg)
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ι → ℝ) (by linarith : 0 < B))
  intro v hv i
  have hi := norm_le_pi_norm v i
  rw [Metric.mem_ball, dist_zero_right] at hv
  exact (show |v i| ≤ ‖v‖ by simpa only [Real.norm_eq_abs] using hi).trans hv.le

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Bundle
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L)

noncomputable def rightRiemannianMetric :
    letI := basisChartedSpace (hnil := hnil) e
    RiemannianMetric (fun g : NilpotentLieBCHGroup L s hnil => TangentSpace 𝓘(ℝ, ι → ℝ) g) := by
  letI := basisChartedSpace (hnil := hnil) e
  refine
    { inner := fun g => ?_
      symm := ?_
      pos := ?_
      continuousAt := ?_
      isVonNBounded := ?_ }
  · exact rightInnerForm e g
  · intro g v w
    exact rightInnerForm_symm e g v w
  · intro g v hv
    exact rightInnerForm_pos e g v hv
  · intro g
    exact ((rightInnerForm e g).continuous.clm_apply continuous_id).continuousAt
  · intro g
    exact rightInnerForm_isVonNBounded e g

omit [IsScalarTower ℚ ℝ L] in
theorem basisChart_mem_source (x y : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    y ∈ (chartAt (ι → ℝ) x).source := by
  let := basisChartedSpace (hnil := hnil) e
  change y ∈ ((basisHomeomorph e).isOpenEmbedding.toOpenPartialHomeomorph (basisHomeomorph e)).source
  simp

omit [IsScalarTower ℚ ℝ L] in
theorem basis_tangentCoordChange (x y z : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := isManifold_basis (hnil := hnil) e 1
    tangentCoordChange 𝓘(ℝ, ι → ℝ) x y z = ContinuousLinearMap.id ℝ (ι → ℝ) := by
  let := basisChartedSpace (hnil := hnil) e
  let := isManifold_basis (hnil := hnil) e 1
  apply ContinuousLinearMap.ext
  intro v
  change tangentCoordChange 𝓘(ℝ, ι → ℝ) x x z v = v
  apply tangentCoordChange_self
  rw [extChartAt_source]
  exact basisChart_mem_source e x z

omit [IsScalarTower ℚ ℝ L] in
theorem basis_tangent_symmL (x y : NilpotentLieBCHGroup L s hnil) (v : ι → ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := isManifold_basis (hnil := hnil) e 1
    (trivializationAt (ι → ℝ) (TangentSpace 𝓘(ℝ, ι → ℝ)) x).symmL ℝ y v = v := by
  let := basisChartedSpace (hnil := hnil) e
  let := isManifold_basis (hnil := hnil) e 1
  rw [TangentBundle.symmL_trivializationAt_eq_core (basisChart_mem_source e x y)]
  change tangentCoordChange 𝓘(ℝ, ι → ℝ) x y y v = v
  rw [basis_tangentCoordChange]
  rfl

theorem contMDiff_rightInnerForm :
    letI := basisChartedSpace (hnil := hnil) e
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ) ∞
      (rightInnerForm (hnil := hnil) e) := by
  let := basisChartedSpace (hnil := hnil) e
  have h := (contDiff_rightInnerForm (hnil := hnil) e).contMDiff.comp
    (contMDiff_basisHomeomorph (hnil := hnil) e ∞)
  simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using h

noncomputable def rightSmoothRiemannianMetric :
    letI := basisChartedSpace (hnil := hnil) e
    letI := isManifold_basis (hnil := hnil) e ∞
    ContMDiffRiemannianMetric 𝓘(ℝ, ι → ℝ) ∞ (ι → ℝ)
      (fun g : NilpotentLieBCHGroup L s hnil => TangentSpace 𝓘(ℝ, ι → ℝ) g) := by
  letI := basisChartedSpace (hnil := hnil) e
  letI := isManifold_basis (hnil := hnil) e ∞
  refine
    { __ := rightRiemannianMetric (hnil := hnil) e
      contMDiff := ?_ }
  intro x
  rw [contMDiffAt_section]
  convert (contMDiff_rightInnerForm (hnil := hnil) e).contMDiffAt (x := x) using 1; try rfl
  funext y
  ext v w
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    rightRiemannianMetric, Trivialization.continuousLinearMapAt_apply]
  have hy : y ∈ (trivializationAt (ι → ℝ) (TangentSpace 𝓘(ℝ, ι → ℝ)) x).baseSet :=
    basisChart_mem_source e x y
  have hw : (trivializationAt (ι → ℝ) (TangentSpace 𝓘(ℝ, ι → ℝ)) x).symm y w = w :=
    (Trivialization.symmL_apply (R := ℝ) _ hy w).symm.trans (basis_tangent_symmL e x y w)
  change rightInnerForm e y
    ((trivializationAt (ι → ℝ) (TangentSpace 𝓘(ℝ, ι → ℝ)) x).symmL ℝ y v)
    ((trivializationAt (ι → ℝ) (TangentSpace 𝓘(ℝ, ι → ℝ)) x).symm y w) = rightInnerForm e y v w
  exact congrArg₂ (fun a b : ι → ℝ => rightInnerForm e y a b)
    (basis_tangent_symmL e x y v) hw

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open _root_.Set
open scoped ENNReal Topology

theorem edist_ne_top_of_preconnected {X : Type*} [PseudoEMetricSpace X] [PreconnectedSpace X]
    (x y : X) : edist x y ≠ ⊤ := by
  have ho : IsOpen (Metric.eball x ⊤)ᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    apply Filter.mem_of_superset (Metric.eball_mem_nhds z zero_lt_one)
    intro w hw hfin
    apply hz
    change edist z x < ⊤
    have hzw : edist z w < ⊤ := by
      have hw' : edist w z < 1 := hw
      rw [edist_comm]
      exact hw'.trans (by simp)
    exact (edist_triangle z w x).trans_lt (ENNReal.add_lt_top.mpr ⟨hzw, hfin⟩)
  have hall : Metric.eball x ⊤ = univ :=
    (show IsClopen (Metric.eball x ⊤) from ⟨isOpen_compl_iff.mp ho, Metric.isOpen_eball⟩).eq_univ
      ⟨x, by simp⟩
  have hy : y ∈ Metric.eball x ⊤ := by rw [hall]; trivial
  have hxy : edist y x < ⊤ := hy
  exact (by simpa only [edist_comm] using hxy.ne)

end Erdos3

namespace Erdos3.NilpotentLieBCHGroup

open Module Bundle
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L)

@[instance_reducible]
noncomputable def rightRiemannianBundle :
    letI := basisChartedSpace (hnil := hnil) e
    RiemannianBundle (fun g : NilpotentLieBCHGroup L s hnil => TangentSpace 𝓘(ℝ, ι → ℝ) g) := by
  letI := basisChartedSpace (hnil := hnil) e
  letI := isManifold_basis (hnil := hnil) e ∞
  exact ⟨(rightSmoothRiemannianMetric (hnil := hnil) e).toRiemannianMetric⟩

theorem rightRiemannianBundle_continuous :
    letI := basisChartedSpace (hnil := hnil) e
    letI := isManifold_basis (hnil := hnil) e ∞
    letI := rightRiemannianBundle (hnil := hnil) e
    IsContinuousRiemannianBundle (ι → ℝ)
      (fun g : NilpotentLieBCHGroup L s hnil => TangentSpace 𝓘(ℝ, ι → ℝ) g) := by
  let := basisChartedSpace (hnil := hnil) e
  let := isManifold_basis (hnil := hnil) e ∞
  let := rightRiemannianBundle (hnil := hnil) e
  exact ⟨(rightSmoothRiemannianMetric e).inner,
    (rightSmoothRiemannianMetric e).contMDiff.continuous, fun _ _ _ => rfl⟩

@[instance_reducible]
noncomputable def rightEMetricSpace : EMetricSpace (NilpotentLieBCHGroup L s hnil) := by
  letI := basisChartedSpace (hnil := hnil) e
  letI := isManifold_basis (hnil := hnil) e ∞
  letI := rightRiemannianBundle (hnil := hnil) e
  letI := rightRiemannianBundle_continuous (hnil := hnil) e
  letI : T3Space (NilpotentLieBCHGroup L s hnil) := (basisHomeomorph e).isEmbedding.t3Space
  exact EMetricSpace.ofRiemannianMetric 𝓘(ℝ, ι → ℝ) (NilpotentLieBCHGroup L s hnil)

@[instance_reducible]
noncomputable def rightMetricSpace : MetricSpace (NilpotentLieBCHGroup L s hnil) := by
  letI := rightEMetricSpace (hnil := hnil) e
  exact EMetricSpace.toMetricSpace edist_ne_top_of_preconnected

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Bundle Manifold
open scoped Manifold ContDiff Bundle

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L)

theorem basis_extChartAt_apply (g x : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    extChartAt 𝓘(ℝ, ι → ℝ) g x = basisHomeomorph e x := rfl

theorem basis_extChartAt_symm_apply (g : NilpotentLieBCHGroup L s hnil) (x : ι → ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    (extChartAt 𝓘(ℝ, ι → ℝ) g).symm x = (basisHomeomorph e).symm x := by
  let := basisChartedSpace (hnil := hnil) e
  have hs : (basisHomeomorph e).symm x ∈ (extChartAt 𝓘(ℝ, ι → ℝ) g).source := by
    rw [extChartAt_source]
    exact basisChart_mem_source e g _
  have h := (extChartAt 𝓘(ℝ, ι → ℝ) g).left_inv hs
  rw [basis_extChartAt_apply, Homeomorph.apply_symm_apply] at h
  exact h

variable [IsScalarTower ℚ ℝ L]

theorem mfderiv_mul_right_coordinates (g h : NilpotentLieBCHGroup L s hnil) (v : ι → ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (fun x => x * h) g v =
      fderiv ℝ (rightTranslate e h) (basisHomeomorph e g) v := by
  let := basisChartedSpace (hnil := hnil) e
  let := lieGroup_basis (hnil := hnil) e 1
  have hm : MDifferentiableAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (fun x => x * h) g :=
    contMDiff_mul_right.mdifferentiableAt one_ne_zero
  rw [hm.mfderiv]
  simp only [writtenInExtChartAt, Function.comp_def, basis_extChartAt_apply,
    basis_extChartAt_symm_apply, modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ]
  rfl

theorem enorm_mfderiv_mul_right (g h : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hnil) e
    ∀ v : TangentSpace 𝓘(ℝ, ι → ℝ) g,
      ‖mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (fun x => x * h) g v‖ₑ = ‖v‖ₑ := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  intro v
  have hn : ‖mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (fun x => x * h) g v‖ = ‖v‖ := by
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
    congr 1
    change rightInnerForm e (g * h)
      (mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (fun x => x * h) g v)
      (mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (fun x => x * h) g v) = rightInnerForm e g v v
    have hv := mfderiv_mul_right_coordinates e g h v
    exact (congrArg₂ (fun a b : ι → ℝ => rightInnerForm e (g * h) a b) hv hv).trans
      (rightInnerForm_right_invariant e g h v v)
  exact enorm_eq_iff_norm_eq.mpr hn

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Bundle Manifold
open scoped Manifold ContDiff Bundle

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L)

theorem riemannianEDist_mul_right_le (x y h : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hnil) e
    riemannianEDist 𝓘(ℝ, ι → ℝ) (x * h) (y * h) ≤ riemannianEDist 𝓘(ℝ, ι → ℝ) x y := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  let := lieGroup_basis (hnil := hnil) e 1
  exact riemannianEDist_le_of_mfderiv_norm_le contMDiff_mul_right
    (fun z v => (enorm_mfderiv_mul_right e z h v).le) x y

theorem riemannianEDist_mul_right (x y h : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hnil) e
    riemannianEDist 𝓘(ℝ, ι → ℝ) (x * h) (y * h) = riemannianEDist 𝓘(ℝ, ι → ℝ) x y := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  apply le_antisymm (riemannianEDist_mul_right_le e x y h)
  simpa only [mul_inv_cancel_right] using riemannianEDist_mul_right_le e (x * h) (y * h) h⁻¹

theorem rightMetricSpace_isometry_mul_right (h : NilpotentLieBCHGroup L s hnil) :
    letI := rightMetricSpace (hnil := hnil) e
    Isometry (fun x => x * h) := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  let := rightMetricSpace (hnil := hnil) e
  intro x y
  exact riemannianEDist_mul_right e x y h

theorem rightMetricSpace_isIsometricSMul :
    letI := rightMetricSpace (hnil := hnil) e
    IsIsometricSMul (NilpotentLieBCHGroup L s hnil)ᵐᵒᵖ (NilpotentLieBCHGroup L s hnil) := by
  let := rightMetricSpace (hnil := hnil) e
  exact ⟨fun h => rightMetricSpace_isometry_mul_right e h.unop⟩

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module

noncomputable def basisCoordinateMap {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup L] [Module ℝ L] [AddCommGroup M] [Module ℝ M]
    (e : Basis ι ℝ L) (f : Basis κ ℝ M) (φ : L →ₗ[ℝ] M) : (ι → ℝ) →L[ℝ] (κ → ℝ) :=
  LinearMap.toContinuousLinearMap
    (f.equivFun.toLinearMap.comp (φ.comp e.equivFun.symm.toLinearMap))

@[simp] theorem basisCoordinateMap_apply {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup L] [Module ℝ L] [AddCommGroup M] [Module ℝ M]
    (e : Basis ι ℝ L) (f : Basis κ ℝ M) (φ : L →ₗ[ℝ] M) (x : ι → ℝ) :
    basisCoordinateMap e f φ x = f.equivFun (φ (e.equivFun.symm x)) := rfl

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]

def realLieHomToRat (φ : L →ₗ⁅ℝ⁆ M) : L →ₗ⁅ℚ⁆ M where
  toLinearMap := φ.toLinearMap.restrictScalars ℚ
  map_lie' {x y} := φ.map_lie x y

namespace NilpotentLieBCHGroup

variable {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

noncomputable def mapReal (φ : L →ₗ⁅ℝ⁆ M) :
    NilpotentLieBCHGroup L s hnil →* NilpotentLieBCHGroup M t hM :=
  mapOfSteps (realLieHomToRat φ)

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]

open scoped Manifold ContDiff

variable (e : Basis ι ℝ L) (f : Basis κ ℝ M) (φ : L →ₗ⁅ℝ⁆ M)

theorem mapReal_basisHomeomorph (g : NilpotentLieBCHGroup L s hnil) :
    basisHomeomorph f (mapReal (hM := hM) φ g) =
      basisCoordinateMap e f φ.toLinearMap (basisHomeomorph e g) := by
  change f.equivFun (φ g.coord) = f.equivFun (φ (e.equivFun.symm (e.equivFun g.coord)))
  rw [LinearEquiv.symm_apply_apply]

theorem mapReal_basisHomeomorph_symm (x : ι → ℝ) :
    mapReal (hnil := hnil) (hM := hM) φ ((basisHomeomorph e).symm x) =
      (basisHomeomorph f).symm (basisCoordinateMap e f φ.toLinearMap x) := by
  apply (basisHomeomorph f).injective
  rw [mapReal_basisHomeomorph e f, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

theorem contMDiff_mapReal (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := basisChartedSpace (hnil := hM) f
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) n (mapReal (hnil := hnil) (hM := hM) φ) := by
  let := basisChartedSpace (hnil := hnil) e
  let := basisChartedSpace (hnil := hM) f
  apply ContMDiff.of_comp_isOpenEmbedding (basisHomeomorph f).isOpenEmbedding
  have hc := (basisCoordinateMap e f φ.toLinearMap).contDiff.contMDiff.comp
    (contMDiff_basisHomeomorph (hnil := hnil) e n)
  have he : (basisHomeomorph f) ∘ mapReal (hnil := hnil) (hM := hM) φ =
      basisCoordinateMap e f φ.toLinearMap ∘ basisHomeomorph e :=
    funext (mapReal_basisHomeomorph e f φ)
  rw [he]
  exact hc

theorem mfderiv_mapReal_coordinates (g : NilpotentLieBCHGroup L s hnil) (v : ι → ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := basisChartedSpace (hnil := hM) f
    mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) (mapReal (hnil := hnil) (hM := hM) φ) g v =
      basisCoordinateMap e f φ.toLinearMap v := by
  let := basisChartedSpace (hnil := hnil) e
  let := basisChartedSpace (hnil := hM) f
  have hm := (contMDiff_mapReal (hnil := hnil) (hM := hM) e f φ 1).mdifferentiableAt
    (x := g) one_ne_zero
  have heq : writtenInExtChartAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) g (mapReal (hM := hM) φ) =
      basisCoordinateMap e f φ.toLinearMap := by
    funext x
    simp only [writtenInExtChartAt, Function.comp_apply, basis_extChartAt_apply,
      basis_extChartAt_symm_apply, mapReal_basisHomeomorph e f, Homeomorph.apply_symm_apply]
  rw [hm.mfderiv, heq]
  simp only [modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ,
    ContinuousLinearMap.fderiv]
  rfl

theorem basisCoordinateMap_rightTranslate (g : NilpotentLieBCHGroup L s hnil) (x : ι → ℝ) :
    basisCoordinateMap e f φ.toLinearMap (rightTranslate e g x) =
      rightTranslate f (mapReal (hM := hM) φ g) (basisCoordinateMap e f φ.toLinearMap x) := by
  change basisCoordinateMap e f φ.toLinearMap
    (basisHomeomorph e ((basisHomeomorph e).symm x * g)) = _
  rw [← mapReal_basisHomeomorph e f φ, map_mul, mapReal_basisHomeomorph_symm e f φ]
  rfl

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

variable (e : Basis ι ℝ L) (f : Basis κ ℝ M)
  (φ : NilpotentLieBCHGroup L s hnil →* NilpotentLieBCHGroup M s hM)

noncomputable def homCoordinates (v : ι → ℝ) : κ → ℝ :=
  basisHomeomorph f (φ ((basisHomeomorph e).symm v))

theorem homCoordinates_apply (g : NilpotentLieBCHGroup L s hnil) :
    homCoordinates e f φ (basisHomeomorph e g) = basisHomeomorph f (φ g) := by
  simp only [homCoordinates, Homeomorph.symm_apply_apply]

theorem homCoordinates_rightTranslate (g : NilpotentLieBCHGroup L s hnil) (v : ι → ℝ) :
    homCoordinates e f φ (rightTranslate e g v) =
      rightTranslate f (φ g) (homCoordinates e f φ v) := by
  simp only [homCoordinates, rightTranslate, Homeomorph.symm_apply_apply, map_mul]

theorem homCoordinates_continuous (hφ : Continuous φ) : Continuous (homCoordinates e f φ) :=
  (basisHomeomorph f).continuous.comp (hφ.comp (basisHomeomorph e).symm.continuous)

@[simp] theorem homCoordinates_zero : homCoordinates e f φ 0 = 0 := by
  have he : (basisHomeomorph (hnil := hnil) e).symm 0 = 1 := by
    apply ext
    exact map_zero e.equivFun.symm
  simp only [homCoordinates, he, map_one]
  exact map_zero f.equivFun

theorem basisHomeomorph_pow (g : NilpotentLieBCHGroup L s hnil) (n : ℕ) :
    basisHomeomorph e (g ^ n) = n • basisHomeomorph e g := by
  change e.equivFun (g ^ n).coord = n • e.equivFun g.coord
  rw [coord_pow, map_nsmul]

theorem basisHomeomorph_zpow (g : NilpotentLieBCHGroup L s hnil) (n : ℤ) :
    basisHomeomorph e (g ^ n) = n • basisHomeomorph e g := by
  change e.equivFun (g ^ n).coord = n • e.equivFun g.coord
  rw [coord_zpow, map_zsmul]

theorem homCoordinates_nsmul (n : ℕ) (v : ι → ℝ) :
    homCoordinates e f φ (n • v) = n • homCoordinates e f φ v := by
  have he : (basisHomeomorph (hnil := hnil) e).symm (n • v) =
      ((basisHomeomorph e).symm v) ^ n := by
    apply (basisHomeomorph e).injective
    simp only [Homeomorph.apply_symm_apply, basisHomeomorph_pow]
  simp only [homCoordinates, he, map_pow, basisHomeomorph_pow]

theorem homCoordinates_zsmul (n : ℤ) (v : ι → ℝ) :
    homCoordinates e f φ (n • v) = n • homCoordinates e f φ v := by
  have he : (basisHomeomorph (hnil := hnil) e).symm (n • v) =
      ((basisHomeomorph e).symm v) ^ n := by
    apply (basisHomeomorph e).injective
    simp only [Homeomorph.apply_symm_apply, basisHomeomorph_zpow]
  simp only [homCoordinates, he, map_zpow, basisHomeomorph_zpow]

theorem homCoordinates_natCast_smul (n : ℕ) (v : ι → ℝ) :
    homCoordinates e f φ ((n : ℝ) • v) = (n : ℝ) • homCoordinates e f φ v := by
  simpa only [Nat.cast_smul_eq_nsmul] using homCoordinates_nsmul e f φ n v

theorem homCoordinates_intCast_smul (n : ℤ) (v : ι → ℝ) :
    homCoordinates e f φ ((n : ℝ) • v) = (n : ℝ) • homCoordinates e f φ v := by
  simpa only [Int.cast_smul_eq_zsmul] using homCoordinates_zsmul e f φ n v

theorem homCoordinates_ratCast_smul (q : ℚ) (v : ι → ℝ) :
    homCoordinates e f φ ((q : ℝ) • v) = (q : ℝ) • homCoordinates e f φ v := by
  have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hq : (q.den : ℝ) * (q : ℝ) = (q.num : ℝ) := by
    rw [Rat.cast_def]
    field_simp
  apply smul_right_injective (κ → ℝ) hd
  dsimp only
  rw [← homCoordinates_natCast_smul, smul_smul, hq, homCoordinates_intCast_smul,
    smul_smul, hq]

theorem homCoordinates_smul (hφ : Continuous φ) (t : ℝ) (v : ι → ℝ) :
    homCoordinates e f φ (t • v) = t • homCoordinates e f φ v := by
  have heq : (fun t : ℝ => homCoordinates e f φ (t • v)) =
      fun t : ℝ => t • homCoordinates e f φ v :=
    (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).equalizer
      ((homCoordinates_continuous e f φ hφ).comp (continuous_id.smul continuous_const))
      (continuous_id.smul continuous_const)
      (funext fun q => homCoordinates_ratCast_smul e f φ q v)
  exact congrFun heq t

theorem homCoordinates_eq_fderiv (hφ : Continuous φ)
    (hd : DifferentiableAt ℝ (homCoordinates e f φ) 0) (v : ι → ℝ) :
    homCoordinates e f φ v = fderiv ℝ (homCoordinates e f φ) 0 v := by
  have hline : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hD : HasFDerivAt (homCoordinates e f φ) (fderiv ℝ (homCoordinates e f φ) 0)
      ((0 : ℝ) • v) := by simpa using hd.hasFDerivAt
  have hcomp := hD.comp_hasDerivAt (0 : ℝ) hline
  have heq : homCoordinates e f φ ∘ (fun t : ℝ => t • v) =
      fun t : ℝ => t • homCoordinates e f φ v :=
    funext fun t => homCoordinates_smul e f φ hφ t v
  rw [heq] at hcomp
  have hlin : HasDerivAt (fun t : ℝ => t • homCoordinates e f φ v)
      (homCoordinates e f φ v) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (homCoordinates e f φ v)
  exact hlin.unique hcomp

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (a : NilpotentLieBCHGroup L s hnil)

include e in
theorem continuous_conjugation : Continuous ((MulAut.conj a).toMonoidHom) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  exact (continuous_const.mul continuous_id).mul continuous_const

theorem contDiff_conjugationCoordinates (n : ℕ∞ω) :
    ContDiff ℝ n (homCoordinates e e (MulAut.conj a).toMonoidHom) := by
  let := basisChartedSpace (hnil := hnil) e
  let := lieGroup_basis (hnil := hnil) e n
  exact ((contMDiff_basisHomeomorph e n).comp
    ((contMDiff_const.mul (contMDiff_basisHomeomorph_symm e n)).mul contMDiff_const)).contDiff

noncomputable def conjugationLinearMap : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  fderiv ℝ (homCoordinates e e (MulAut.conj a).toMonoidHom) 0

theorem homCoordinates_conjugation_eq :
    homCoordinates e e (MulAut.conj a).toMonoidHom = conjugationLinearMap e a := by
  funext v
  exact homCoordinates_eq_fderiv e e (MulAut.conj a).toMonoidHom (continuous_conjugation e a)
    ((contDiff_conjugationCoordinates e a 1).differentiable one_ne_zero).differentiableAt v

theorem conjugationLinearMap_coordinates (x : NilpotentLieBCHGroup L s hnil) :
    conjugationLinearMap e a (basisHomeomorph e x) = basisHomeomorph e (a * x * a⁻¹) := by
  rw [← homCoordinates_conjugation_eq, homCoordinates_apply]
  rfl

theorem conjugationLinearMap_basis [DecidableEq ι] (i k : ι) :
    conjugationLinearMap e a (Pi.single i 1) k =
      e.repr (a * (⟨e i⟩ : NilpotentLieBCHGroup L s hnil) * a⁻¹).coord k := by
  have he : basisHomeomorph (hnil := hnil) e ⟨e i⟩ = Pi.single i 1 := by
    funext j
    simpa only [basisHomeomorph_apply, Pi.single_apply, eq_comm] using e.equivFun_self i j
  rw [← he, conjugationLinearMap_coordinates]
  rfl

end Erdos3.NilpotentLieBCHGroup

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisCoordinateBounds
namespace OAI

section

namespace Erdos3

open Module

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [AddCommGroup L] [Module ℝ L] [AddCommGroup M] [Module ℝ M]

theorem basisCoordinateMap_apply_eq_sum (e : Basis ι ℝ L) (f : Basis κ ℝ M)
    (φ : L →ₗ[ℝ] M) (v : ι → ℝ) (k : κ) :
    basisCoordinateMap e f φ v k = ∑ i, f.repr (φ (e i)) k * v i := by
  rw [basisCoordinateMap_apply, Basis.equivFun_symm_apply]
  change f.repr (φ (∑ i, v i • e i)) k = _
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, mul_comm]

theorem basisCoordinateMap_L2_bound (e : Basis ι ℝ L) (f : Basis κ ℝ M)
    (φ : L →ₗ[ℝ] M) (B : ℝ) (hB : 0 ≤ B)
    (hφ : ∀ k i, |f.repr (φ (e i)) k| ≤ B) (v : ι → ℝ) :
    coordinateL2Norm (basisCoordinateMap e f φ v) ≤
      ((Fintype.card κ : ℝ) + Fintype.card ι + 1) * (B + 1) * coordinateL2Norm v := by
  have heq : basisCoordinateMap e f φ v = fun k => ∑ i, f.repr (φ (e i)) k * v i :=
    funext (basisCoordinateMap_apply_eq_sum e f φ v)
  rw [heq]
  exact coordinateL2Norm_matrix_entry_bound (fun k i => f.repr (φ (e i)) k) B hB hφ v

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHQuotientChart
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem eq_one_of_subgroup_grid_of_small_coordinates (e : Basis ι ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g ∈ Γ)
    (hsmall : ∀ i, |e.repr g.coord i| < 1 / (l : ℝ)) : g = 1 := by
  apply ext
  apply e.equivFun.injective
  simpa only [coord_one, map_zero] using
    eq_zero_of_mem_realDenominatorGrid_of_abs_lt hl (hgrid g hg) hsmall

variable [IsScalarTower ℚ ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

theorem quotient_coordinate_injOn_of_radius
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hsep : bchBoxCoordinateBound s (Fintype.card ι) H 1 * (2 * r) < 1 / (l : ℝ))
    (z : NilpotentLieBCHGroup L s hnil) :
    Set.InjOn (fun v : ι → ℝ => (QuotientGroup.mk (z * (basisHomeomorph e).symm v) : _ ⧸ Γ))
      {v | ∀ i, |v i| ≤ r} := by
  intro x hx y hy hxy
  let u := (basisHomeomorph (hnil := hnil) e).symm x
  let v := (basisHomeomorph (hnil := hnil) e).symm y
  have hu : e.equivFun u.coord = x := (basisHomeomorph (hnil := hnil) e).apply_symm_apply x
  have hv : e.equivFun v.coord = y := (basisHomeomorph (hnil := hnil) e).apply_symm_apply y
  have hur (i) : |e.repr u.coord i| ≤ r := by simpa only [← hu, Basis.equivFun_apply] using hx i
  have hvr (i) : |e.repr v.coord i| ≤ r := by simpa only [← hv, Basis.equivFun_apply] using hy i
  have hmem : u⁻¹ * v ∈ Γ := by
    have h := QuotientGroup.eq.mp hxy
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using h
  have hone : u⁻¹ * v = 1 := by
    apply eq_one_of_subgroup_grid_of_small_coordinates e Γ l hl hgrid _ hmem
    intro k
    have hbound := lieBCH_sub_coordinates_bound e c hstructure hc hnil (-u.coord) (-v.coord)
      (B := 1) (δ := 2 * r) le_rfl (by positivity)
      (fun i => by simpa only [map_neg, Finsupp.neg_apply, abs_neg] using (hur i).trans hr1)
      (fun i => by simpa only [map_neg, Finsupp.neg_apply, abs_neg] using (hvr i).trans hr1)
      (fun i => by
        simp only [map_neg, Finsupp.neg_apply, neg_sub_neg]
        exact (abs_sub _ _).trans (by linarith [hur i, hvr i])) k
    simpa only [coord_mul, coord_inv, neg_neg] using hbound.trans_lt hsep
  have huv : u = v := inv_mul_eq_one.mp hone
  exact hu.symm.trans ((congrArg (fun g => e.equivFun g.coord) huv).trans hv)

end Erdos3.NilpotentLieBCHGroup

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHLatticeImageGap
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped ContDiff

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

theorem rightVelocity_mapReal (e : Basis ι ℝ L) (f : Basis κ ℝ M) (φ : L →ₗ⁅ℝ⁆ M)
    (g : NilpotentLieBCHGroup L s hnil) :
    (rightVelocity f (mapReal (hM := hM) φ g)).comp (basisCoordinateMap e f φ.toLinearMap) =
      (basisCoordinateMap e f φ.toLinearMap).comp (rightVelocity e g) := by
  let A := basisCoordinateMap e f φ.toLinearMap
  have hc : rightTranslate f (mapReal (hM := hM) φ g⁻¹) ∘ A = A ∘ rightTranslate e g⁻¹ := by
    funext x
    exact (basisCoordinateMap_rightTranslate e f φ g⁻¹ x).symm
  have hi := (contDiff_rightTranslate e g⁻¹ 1).differentiable (by decide)
  have ho := (contDiff_rightTranslate f (mapReal (hM := hM) φ g⁻¹) 1).differentiable (by decide)
  have hd := congrArg (fun F : (ι → ℝ) → (κ → ℝ) => fderiv ℝ F (basisHomeomorph e g)) hc
  rw [fderiv_comp _ ho.differentiableAt A.differentiableAt,
    fderiv_comp _ A.differentiableAt hi.differentiableAt,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv] at hd
  dsimp only [A] at hd
  rw [← mapReal_basisHomeomorph e f φ, map_inv] at hd
  exact hd

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Manifold
open scoped Manifold ContDiff Bundle NNReal ENNReal

section Norm

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem norm_tangent_eq_coordinateL2Norm (e : Basis ι ℝ L) (g : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hnil) e
    ∀ v : TangentSpace 𝓘(ℝ, ι → ℝ) g, ‖v‖ = coordinateL2Norm (rightVelocity e g v) := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  intro v
  rw [norm_eq_sqrt_real_inner]
  change Real.sqrt (rightInnerForm e g v v) = _
  simpa only [coordinateL2Norm, pow_two] using
    congrArg Real.sqrt (rightInnerForm_apply e g v v)

end Norm

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

variable (e : Basis ι ℝ L) (f : Basis κ ℝ M) (φ : L →ₗ⁅ℝ⁆ M)

theorem norm_mfderiv_mapReal_le {C : ℝ}
    (hA : ∀ w, coordinateL2Norm (basisCoordinateMap e f φ.toLinearMap w) ≤ C * coordinateL2Norm w)
    (g : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := basisChartedSpace (hnil := hM) f
    letI := rightRiemannianBundle (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hM) f
    ∀ v : TangentSpace 𝓘(ℝ, ι → ℝ) g,
      ‖mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) (mapReal (hM := hM) φ) g v‖ ≤ C * ‖v‖ := by
  let := basisChartedSpace (hnil := hnil) e
  let := basisChartedSpace (hnil := hM) f
  let := rightRiemannianBundle (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hM) f
  intro v
  have hv := mfderiv_mapReal_coordinates (hM := hM) e f φ g v
  have hc := congrArg (fun T : (ι → ℝ) →L[ℝ] (κ → ℝ) => T v)
    (rightVelocity_mapReal (hM := hM) e f φ g)
  have hvel := (congrArg (fun w : κ → ℝ => rightVelocity f (mapReal (hM := hM) φ g) w) hv).trans hc
  calc
    ‖mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) (mapReal (hM := hM) φ) g v‖ =
        coordinateL2Norm (rightVelocity f (mapReal (hM := hM) φ g)
          (mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) (mapReal (hM := hM) φ) g v)) :=
      norm_tangent_eq_coordinateL2Norm f _ _
    _ = coordinateL2Norm (basisCoordinateMap e f φ.toLinearMap (rightVelocity e g v)) :=
      congrArg coordinateL2Norm hvel
    _ ≤ C * coordinateL2Norm (rightVelocity e g v) := hA _
    _ = C * ‖v‖ := congrArg (C * ·) (norm_tangent_eq_coordinateL2Norm e g v).symm

theorem lipschitz_mapReal_of_coordinate_bound {C : ℝ≥0} (hC : 0 < C)
    (hA : ∀ w, coordinateL2Norm (basisCoordinateMap e f φ.toLinearMap w) ≤ C * coordinateL2Norm w) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := rightMetricSpace (hnil := hM) f
    LipschitzWith C (mapReal (hnil := hnil) (hM := hM) φ) := by
  let := basisChartedSpace (hnil := hnil) e
  let := basisChartedSpace (hnil := hM) f
  let := rightRiemannianBundle (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hM) f
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace (hnil := hM) f
  apply riemannianEDist_le_mul_of_mfderiv_bound hC (contMDiff_mapReal e f φ 1)
  intro g v
  have h := ENNReal.ofReal_le_ofReal (norm_mfderiv_mapReal_le (hM := hM) e f φ hA g v)
  simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg C), ofReal_norm,
    ENNReal.ofReal_coe_nnreal] using h

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s t : ℕ} (e : Basis ι ℝ L)
  (hs : LieModule.lowerCentralSeries ℚ L L s = ⊥)
  (ht : LieModule.lowerCentralSeries ℚ L L t = ⊥)

theorem lipschitz_changeStep :
    letI := rightMetricSpace (hnil := hs) e
    letI := rightMetricSpace (hnil := ht) e
    LipschitzWith 1 (changeStep hs ht) := by
  apply lipschitz_mapReal_of_coordinate_bound (hnil := hs) (hM := ht)
    e e (LieHom.id : L →ₗ⁅ℝ⁆ L) (by norm_num : (0 : ℝ≥0) < 1)
  intro w
  change coordinateL2Norm (e.equivFun (e.equivFun.symm w)) ≤ 1 * coordinateL2Norm w
  rw [LinearEquiv.apply_symm_apply, one_mul]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Manifold
open scoped Manifold ContDiff Bundle NNReal ENNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem rightTranslate_fderiv_zero_rightVelocity (e : Basis ι ℝ L)
    (g : NilpotentLieBCHGroup L s hnil) :
    (fderiv ℝ (rightTranslate e g) 0).comp (rightVelocity e g) =
      ContinuousLinearMap.id ℝ (ι → ℝ) := by
  have h := rightTranslate_fderiv_leftInverse e g⁻¹ (basisHomeomorph e g)
  rw [rightTranslate_coordinates, mul_inv_cancel] at h
  simpa only [inv_inv, rightTranslate_coordinates, mul_inv_cancel, basisHomeomorph_apply,
    coord_one, map_zero, rightVelocity] using h

theorem coordinate_norm_le_rightVelocity (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (g : NilpotentLieBCHGroup L s hnil) (B : ℝ) (hB : 1 ≤ B)
    (hg : ∀ i, |e.repr g.coord i| ≤ B) (v : ι → ℝ) :
    ‖v‖ ≤ bchBoxCoordinateBound s (Fintype.card ι) H B * coordinateL2Norm (rightVelocity e g v) := by
  have h := congrArg (fun A : (ι → ℝ) →L[ℝ] (ι → ℝ) => A v)
    (rightTranslate_fderiv_zero_rightVelocity e g)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
  calc
    ‖v‖ = ‖fderiv ℝ (rightTranslate e g) 0 (rightVelocity e g v)‖ := congrArg norm h.symm
    _ ≤ ‖fderiv ℝ (rightTranslate e g) 0‖ * ‖rightVelocity e g v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ bchBoxCoordinateBound s (Fintype.card ι) H B * coordinateL2Norm (rightVelocity e g v) :=
      mul_le_mul (norm_fderiv_rightTranslate_zero_le e c hstructure hc g B hB hg)
        (norm_le_coordinateL2Norm _) (norm_nonneg _) (bchBoxCoordinateBound_nonneg _ _ _ (by linarith))

omit [IsScalarTower ℚ ℝ L] in
theorem mfderiv_basisHomeomorph_coordinates (e : Basis ι ℝ L)
    (g : NilpotentLieBCHGroup L s hnil) (v : ι → ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (basisHomeomorph e) g v = v := by
  let := basisChartedSpace (hnil := hnil) e
  have hm := (contMDiff_basisHomeomorph (hnil := hnil) e 1).mdifferentiableAt (x := g) one_ne_zero
  have heq : writtenInExtChartAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) g (basisHomeomorph e) = id := by
    funext x
    simp only [writtenInExtChartAt, Function.comp_apply, basis_extChartAt_symm_apply,
      extChartAt_model_space_eq_id, Homeomorph.apply_symm_apply, id_eq]
    rfl
  rw [hm.mfderiv, heq]
  simp only [modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ, fderiv_id]
  rfl

theorem norm_mfderiv_basisHomeomorph_le (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (g : NilpotentLieBCHGroup L s hnil) (B : ℝ) (hB : 1 ≤ B)
    (hg : ∀ i, |e.repr g.coord i| ≤ B) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hnil) e
    ∀ v : TangentSpace 𝓘(ℝ, ι → ℝ) g,
      ‖tangentModelVector (mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (basisHomeomorph e) g v)‖ ≤
        bchBoxCoordinateBound s (Fintype.card ι) H B * ‖v‖ := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  intro v
  have hcoords : tangentModelVector
      (mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (basisHomeomorph e) g v) = tangentModelVector v :=
    mfderiv_basisHomeomorph_coordinates e g v
  apply (congrArg norm hcoords).le.trans
  exact (coordinate_norm_le_rightVelocity e c hstructure hc g B hB hg v).trans_eq
    (congrArg (bchBoxCoordinateBound s (Fintype.card ι) H B * ·)
      (norm_tangent_eq_coordinateL2Norm e g v).symm)

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Manifold
open scoped Manifold ContDiff Bundle

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def coordinateLine (e : Basis ι ℝ L) (v : ι → ℝ) (t : ℝ) :
    NilpotentLieBCHGroup L s hnil := (basisHomeomorph e).symm (t • v)

variable (e : Basis ι ℝ L) (v : ι → ℝ)

@[simp] theorem coordinateLine_zero : coordinateLine (hnil := hnil) e v 0 = 1 := by
  apply ext
  change e.equivFun.symm ((0 : ℝ) • v) = 0
  simp only [zero_smul, map_zero]

@[simp] theorem coordinateLine_one :
    coordinateLine (hnil := hnil) e v 1 = (basisHomeomorph e).symm v := by
  simp only [coordinateLine, one_smul]

theorem contMDiff_coordinateLine (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, ι → ℝ) n (coordinateLine (hnil := hnil) e v) := by
  let := basisChartedSpace (hnil := hnil) e
  exact (contMDiff_basisHomeomorph_symm e n).comp (contMDiff_id.smul contMDiff_const)

theorem rightTranslate_coordinateLine_inv (t u : ℝ) :
    rightTranslate e (coordinateLine (hnil := hnil) e v t)⁻¹ (u • v) = (u - t) • v := by
  change e.equivFun (lieBCH s (e.equivFun.symm (u • v)) (-e.equivFun.symm (t • v))) = _
  rw [map_smul, map_smul, lieBCH_eq_add_of_lie_eq_zero hnil (by simp [smul_lie, lie_smul])]
  simp only [map_add, map_neg, map_smul, LinearEquiv.apply_symm_apply, sub_eq_add_neg, add_smul, neg_smul]

variable [IsScalarTower ℚ ℝ L]

theorem rightVelocity_coordinateLine (t : ℝ) :
    rightVelocity e (coordinateLine (hnil := hnil) e v t) v = v := by
  have hl : HasDerivAt (fun u : ℝ => u • v) v t := by
    simpa using (hasDerivAt_id t).smul_const v
  have hr := ((contDiff_rightTranslate e (coordinateLine (hnil := hnil) e v t)⁻¹ 1).differentiable
    one_ne_zero).differentiableAt (x := t • v) |>.hasFDerivAt
  have hcomp := hr.comp_hasDerivAt t hl
  have heq : rightTranslate e (coordinateLine (hnil := hnil) e v t)⁻¹ ∘ (fun u : ℝ => u • v) =
      fun u : ℝ => (u - t) • v := funext (rightTranslate_coordinateLine_inv e v t)
  rw [heq] at hcomp
  have hd : HasDerivAt (fun u : ℝ => (u - t) • v) v t := by
    simpa using ((hasDerivAt_id t).sub_const t).smul_const v
  simpa only [rightVelocity, coordinateLine, Homeomorph.apply_symm_apply] using hcomp.unique hd

omit [IsScalarTower ℚ ℝ L] in
theorem mfderiv_coordinateLine (t : ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    mfderiv 𝓘(ℝ) 𝓘(ℝ, ι → ℝ) (coordinateLine (hnil := hnil) e v) t 1 = v := by
  let := basisChartedSpace (hnil := hnil) e
  have hm := (contMDiff_coordinateLine (hnil := hnil) e v 1).mdifferentiableAt (x := t) one_ne_zero
  have heq : writtenInExtChartAt 𝓘(ℝ) 𝓘(ℝ, ι → ℝ) t (coordinateLine (hnil := hnil) e v) =
      fun u : ℝ => u • v := by
    funext u
    simp [writtenInExtChartAt, coordinateLine]
    rfl
  rw [hm.mfderiv, heq]
  simp only [modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ]
  change deriv (fun u : ℝ => u • v) t = v
  exact (show HasDerivAt (fun u : ℝ => u • v) v t by
    simpa using (hasDerivAt_id t).smul_const v).deriv

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Manifold
open scoped Manifold ContDiff Bundle NNReal ENNReal

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

variable (e : Basis ι ℝ L) (f : Basis κ ℝ M)
  (φ : NilpotentLieBCHGroup L s hnil →* NilpotentLieBCHGroup M s hM)
  (A : (ι → ℝ) →L[ℝ] (κ → ℝ)) (hA : homCoordinates e f φ = A)

include hA

theorem linear_hom_basisHomeomorph (g : NilpotentLieBCHGroup L s hnil) :
    basisHomeomorph f (φ g) = A (basisHomeomorph e g) := by
  rw [← homCoordinates_apply e f φ, hA]

theorem contMDiff_linear_hom (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := basisChartedSpace (hnil := hM) f
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) n φ := by
  let := basisChartedSpace (hnil := hnil) e
  let := basisChartedSpace (hnil := hM) f
  apply ContMDiff.of_comp_isOpenEmbedding (basisHomeomorph f).isOpenEmbedding
  have hc := A.contDiff.contMDiff.comp (contMDiff_basisHomeomorph (hnil := hnil) e n)
  have he : (basisHomeomorph f) ∘ φ = A ∘ basisHomeomorph e :=
    funext (linear_hom_basisHomeomorph e f φ A hA)
  rw [he]
  exact hc

theorem mfderiv_linear_hom_coordinates (g : NilpotentLieBCHGroup L s hnil) (v : ι → ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := basisChartedSpace (hnil := hM) f
    mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) φ g v = A v := by
  let := basisChartedSpace (hnil := hnil) e
  let := basisChartedSpace (hnil := hM) f
  have hm := (contMDiff_linear_hom e f φ A hA 1).mdifferentiableAt (x := g) one_ne_zero
  have heq : writtenInExtChartAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) g φ = A := by
    funext x
    simpa only [writtenInExtChartAt, Function.comp_apply, basis_extChartAt_apply,
      basis_extChartAt_symm_apply, homCoordinates] using congrFun hA x
  rw [hm.mfderiv, heq]
  simp only [modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ, ContinuousLinearMap.fderiv]
  rfl

variable [IsScalarTower ℚ ℝ L] [IsScalarTower ℚ ℝ M]

theorem rightVelocity_linear_hom (g : NilpotentLieBCHGroup L s hnil) :
    (rightVelocity f (φ g)).comp A = A.comp (rightVelocity e g) := by
  have hc : rightTranslate f (φ g⁻¹) ∘ A = A ∘ rightTranslate e g⁻¹ := by
    funext v
    have h := homCoordinates_rightTranslate e f φ g⁻¹ v
    rw [hA] at h
    exact h.symm
  have hi := (contDiff_rightTranslate e g⁻¹ 1).differentiable (by decide)
  have ho := (contDiff_rightTranslate f (φ g⁻¹) 1).differentiable (by decide)
  have hd := congrArg (fun F : (ι → ℝ) → (κ → ℝ) => fderiv ℝ F (basisHomeomorph e g)) hc
  rw [fderiv_comp _ ho.differentiableAt A.differentiableAt,
    fderiv_comp _ A.differentiableAt hi.differentiableAt,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv] at hd
  rw [← linear_hom_basisHomeomorph e f φ A hA, map_inv] at hd
  exact hd

theorem norm_mfderiv_linear_hom_le {C : ℝ}
    (hbound : ∀ w, coordinateL2Norm (A w) ≤ C * coordinateL2Norm w)
    (g : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := basisChartedSpace (hnil := hM) f
    letI := rightRiemannianBundle (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hM) f
    ∀ v : TangentSpace 𝓘(ℝ, ι → ℝ) g,
      ‖mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) φ g v‖ ≤ C * ‖v‖ := by
  let := basisChartedSpace (hnil := hnil) e
  let := basisChartedSpace (hnil := hM) f
  let := rightRiemannianBundle (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hM) f
  intro v
  have hv := mfderiv_linear_hom_coordinates e f φ A hA g v
  have hc := congrArg (fun T : (ι → ℝ) →L[ℝ] (κ → ℝ) => T v)
    (rightVelocity_linear_hom e f φ A hA g)
  have hvel := (congrArg (fun w : κ → ℝ => rightVelocity f (φ g) w) hv).trans hc
  calc
    _ = coordinateL2Norm (rightVelocity f (φ g)
        (mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, κ → ℝ) φ g v)) := norm_tangent_eq_coordinateL2Norm f _ _
    _ = coordinateL2Norm (A (rightVelocity e g v)) := congrArg coordinateL2Norm hvel
    _ ≤ C * coordinateL2Norm (rightVelocity e g v) := hbound _
    _ = C * ‖v‖ := congrArg (C * ·) (norm_tangent_eq_coordinateL2Norm e g v).symm

theorem lipschitz_linear_hom {C : ℝ≥0} (hC : 0 < C)
    (hbound : ∀ w, coordinateL2Norm (A w) ≤ C * coordinateL2Norm w) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := rightMetricSpace (hnil := hM) f
    LipschitzWith C φ := by
  let := basisChartedSpace (hnil := hnil) e
  let := basisChartedSpace (hnil := hM) f
  let := rightRiemannianBundle (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hM) f
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace (hnil := hM) f
  apply riemannianEDist_le_mul_of_mfderiv_bound hC (contMDiff_linear_hom e f φ A hA 1)
  intro g v
  have h := ENNReal.ofReal_le_ofReal (norm_mfderiv_linear_hom_le e f φ A hA hbound g v)
  simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg C), ofReal_norm,
    ENNReal.ofReal_coe_nnreal] using h

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open scoped NNReal

noncomputable def bchLogMetricConstant (s d H : ℕ) (B : ℝ≥0) : ℝ≥0 :=
  ⟨bchBoxCoordinateBound s d H B + 1,
    add_nonneg (bchBoxCoordinateBound_nonneg _ _ _ B.coe_nonneg) zero_le_one⟩

theorem bchLogMetricConstant_pos (s d H : ℕ) (B : ℝ≥0) : 0 < bchLogMetricConstant s d H B := by
  change 0 < bchBoxCoordinateBound s d H B + 1
  have := bchBoxCoordinateBound_nonneg s d H B.coe_nonneg
  linarith

namespace NilpotentLieBCHGroup

open Module Manifold
open scoped Manifold ContDiff Bundle ENNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem edist_coordinates_le_of_near_one (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (B : ℝ≥0) (hB : 1 ≤ B) (g : NilpotentLieBCHGroup L s hnil) :
    letI := rightMetricSpace (hnil := hnil) e
    let C := bchLogMetricConstant s (Fintype.card ι) H B
    (C : ℝ≥0∞) * edist 1 g < B →
      edist (basisHomeomorph (hnil := hnil) e 1) (basisHomeomorph e g) ≤ C * edist 1 g := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  let := rightMetricSpace (hnil := hnil) e
  let C := bchLogMetricConstant s (Fintype.card ι) H B
  dsimp only
  intro hnear
  apply coordinate_edist_le_of_riemannianEDist_lt (bchLogMetricConstant_pos s (Fintype.card ι) H B)
    (contMDiff_basisHomeomorph e 1) 1 g ?_ hnear
  intro z hz v
  have hznorm : ‖basisHomeomorph e z‖ ≤ B := by
    simpa only [Metric.mem_closedBall, basisHomeomorph_apply, coord_one, map_zero,
      dist_zero_right] using hz
  have hzbox (i) : |e.repr z.coord i| ≤ B := by
    have hi := (norm_le_pi_norm (basisHomeomorph e z) i).trans hznorm
    simpa only [basisHomeomorph_apply, Basis.equivFun_apply, Real.norm_eq_abs] using hi
  have hv := norm_mfderiv_basisHomeomorph_le e c hstructure hc z B hB hzbox v
  have hAC : bchBoxCoordinateBound s (Fintype.card ι) H B ≤ (C : ℝ) := by
    change bchBoxCoordinateBound s (Fintype.card ι) H B ≤ bchBoxCoordinateBound s (Fintype.card ι) H B + 1
    linarith
  have hv' := hv.trans (mul_le_mul_of_nonneg_right hAC (norm_nonneg v))
  simpa only [ENNReal.ofReal_mul C.coe_nonneg, ofReal_norm, ENNReal.ofReal_coe_nnreal] using
    ENNReal.ofReal_le_ofReal hv'

theorem norm_coordinates_le_of_near_one (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (B : ℝ≥0) (hB : 1 ≤ B) (g : NilpotentLieBCHGroup L s hnil) :
    letI := rightMetricSpace (hnil := hnil) e
    let C := bchLogMetricConstant s (Fintype.card ι) H B
    (C : ℝ) * dist 1 g < B → ‖basisHomeomorph e g‖ ≤ C * dist 1 g := by
  let := rightMetricSpace (hnil := hnil) e
  let C := bchLogMetricConstant s (Fintype.card ι) H B
  dsimp only
  intro hnear
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB
  have hnearE : (C : ℝ≥0∞) * edist 1 g < B := by
    have h : ENNReal.ofReal ((C : ℝ) * dist 1 g) < ENNReal.ofReal (B : ℝ) :=
      (ENNReal.ofReal_lt_ofReal_iff hBpos).mpr hnear
    rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal] at h
    simpa only [edist_dist] using h
  have h := edist_coordinates_le_of_near_one e c hstructure hc B hB g hnearE
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top 1 g)) h
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist, ENNReal.toReal_ofReal dist_nonneg,
    basisHomeomorph_apply, coord_one, map_zero, dist_zero_left,
    ENNReal.toReal_ofReal (norm_nonneg _)] using hr

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def bchInverseBoxConstant (s d H : ℕ) (B : ℝ≥0) : ℝ≥0 :=
  (⟨bchBoxCoordinateBound s d H B, bchBoxCoordinateBound_nonneg _ _ _ B.coe_nonneg⟩ + 2 * B) *
    bchLogMetricConstant s d H 1

namespace NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

noncomputable def bchLatticeSeparationRadius (s d H l : ℕ) : ℝ :=
  1 / ((l : ℝ) + 1) / (bchLogMetricConstant s d H 1 : ℝ)

namespace NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

open scoped NNReal

namespace NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dist_coordinates_le_of_near_box
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (B : ℝ≥0) (hB : 1 ≤ B) (g h : NilpotentLieBCHGroup L s hnil)
    (hg : ∀ i, |e.repr g.coord i| ≤ B) :
    letI := rightMetricSpace (hnil := hnil) e
    let C := bchLogMetricConstant s (Fintype.card ι) H 1
    (C : ℝ) * dist g h < 1 →
      dist (basisHomeomorph e g) (basisHomeomorph e h) ≤
        bchBoxCoordinateBound s (Fintype.card ι) H B * C * dist g h := by
  let := rightMetricSpace (hnil := hnil) e
  let C := bchLogMetricConstant s (Fintype.card ι) H 1
  dsimp only
  intro hnear
  let z := h * g⁻¹
  have hdist : dist 1 z = dist g h := by
    simpa only [mul_inv_cancel] using (rightMetricSpace_isometry_mul_right e g⁻¹).dist_eq g h
  have hz : ‖basisHomeomorph e z‖ ≤ (C : ℝ) * dist g h := by
    have hn : (C : ℝ) * dist 1 z < (1 : ℝ≥0) := by simpa only [hdist, NNReal.coe_one] using hnear
    simpa only [hdist] using norm_coordinates_le_of_near_one e c hstructure hc 1 le_rfl z hn
  have hzbox (i) : |basisHomeomorph e z i| ≤ B := by
    have hi : |basisHomeomorph e z i| ≤ ‖basisHomeomorph e z‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (basisHomeomorph e z) i
    exact ((hi.trans hz).trans hnear.le).trans hB
  have hzero : basisHomeomorph (hnil := hnil) e 1 = 0 := by
    simp only [basisHomeomorph_apply, coord_one, map_zero]
  have hRzero : rightTranslate e g 0 = basisHomeomorph e g := by
    rw [← hzero, rightTranslate_coordinates, one_mul]
  have hzg : z * g = h := by simp only [z, inv_mul_cancel_right]
  have hLip := (lipschitzOn_rightTranslate_box e c hstructure hc g B hB hg).dist_le_mul
    (basisHomeomorph e z) hzbox 0 (by
      intro i
      simpa only [Pi.zero_apply, abs_zero] using B.coe_nonneg)
  rw [rightTranslate_coordinates, hzg, hRzero, dist_zero_right] at hLip
  calc
    _ ≤ bchBoxCoordinateBound s (Fintype.card ι) H B * ‖basisHomeomorph e z‖ := by
      simpa only [dist_comm, NNReal.toReal] using hLip
    _ ≤ bchBoxCoordinateBound s (Fintype.card ι) H B * ((C : ℝ) * dist g h) :=
      mul_le_mul_of_nonneg_left hz (bchBoxCoordinateBound_nonneg s _ H B.coe_nonneg)
    _ = _ := by ring

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped Matrix NNReal

variable {ι κ L : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem rational_kernel_of_near_bounded_point
    (e : Basis κ ℝ L) (c : κ → κ → κ → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Q : Matrix ι κ ℚ) (HQ B : ℝ≥0) (hB : 1 ≤ B)
    (hQ : ∀ i j, |(Q i j : ℝ)| ≤ HQ) (l : ℕ) (hl : 0 < l)
    (g γ : NilpotentLieBCHGroup L s hnil)
    (hg : ∀ i, |e.repr g.coord i| ≤ B)
    (hγ : basisHomeomorph e γ ∈ realDenominatorGrid l)
    (hkernel : (fun i j => (Q i j : ℝ)) *ᵥ basisHomeomorph e g = 0) :
    letI := rightMetricSpace (hnil := hnil) e
    let C := bchLogMetricConstant s (Fintype.card κ) H 1
    let A := bchBoxCoordinateBound s (Fintype.card κ) H B
    (C : ℝ) * dist g γ < 1 →
    ((matrixDenominator Q * l : ℕ) : ℝ) * (((Fintype.card κ : ℝ) + 1) * (HQ + 1)) *
      (A * C) * dist g γ < 1 →
    (fun i j => (Q i j : ℝ)) *ᵥ basisHomeomorph e γ = 0 := by
  let := rightMetricSpace (hnil := hnil) e
  dsimp only
  intro hnear hsmall
  apply rational_matrix_kernel_separation Q HQ hQ l hl (basisHomeomorph e γ) (basisHomeomorph e g)
    hγ hkernel
  have hcoord := dist_coordinates_le_of_near_box e c hstructure hc B hB g γ hg hnear
  rw [dist_comm] at hcoord
  calc
    _ ≤ ((matrixDenominator Q * l : ℕ) : ℝ) * (((Fintype.card κ : ℝ) + 1) * (HQ + 1)) *
        (bchBoxCoordinateBound s (Fintype.card κ) H B *
          (bchLogMetricConstant s (Fintype.card κ) H 1 : ℝ) * dist g γ) := by
      exact mul_le_mul_of_nonneg_left hcoord (by positivity)
    _ < 1 := by nlinarith [hsmall]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped Matrix NNReal

variable {ι κ L : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem lattice_translate_mem_of_small_dist
    (e : Basis κ ℝ L) (c : κ → κ → κ → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Q : Matrix ι κ ℚ) (HQ B K : ℝ≥0) (hB : 1 ≤ B)
    (hQ : ∀ i j, |(Q i j : ℝ)| ≤ HQ) (l : ℕ) (hl : 0 < l)
    (J : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hJ : ∀ g, g ∈ J ↔ (fun i j => (Q i j : ℝ)) *ᵥ basisHomeomorph e g = 0)
    (x y γ : NilpotentLieBCHGroup L s hnil) (hx : x ∈ J) (hy : y ∈ J)
    (hγ : basisHomeomorph e γ ∈ realDenominatorGrid l)
    (hxy : ∀ i, |e.repr (y⁻¹ * x).coord i| ≤ B)
    (hleft : letI := rightMetricSpace (hnil := hnil) e; LipschitzWith K (fun z => y⁻¹ * z)) :
    letI := rightMetricSpace (hnil := hnil) e
    let C := bchLogMetricConstant s (Fintype.card κ) H 1
    let A := bchBoxCoordinateBound s (Fintype.card κ) H B
    (C : ℝ) * K * dist x (y * γ) < 1 →
    ((matrixDenominator Q * l : ℕ) : ℝ) * (((Fintype.card κ : ℝ) + 1) * (HQ + 1)) *
      (A * C) * K * dist x (y * γ) < 1 → γ ∈ J := by
  let := rightMetricSpace (hnil := hnil) e
  dsimp only
  intro hnear hsmall
  have hdist : dist (y⁻¹ * x) γ ≤ (K : ℝ) * dist x (y * γ) := by
    simpa only [inv_mul_cancel_left] using hleft.dist_le_mul x (y * γ)
  apply (hJ γ).mpr
  apply rational_kernel_of_near_bounded_point e c hstructure hc Q HQ B hB hQ l hl (y⁻¹ * x) γ
    hxy hγ ((hJ _).mp (J.mul_mem (J.inv_mem hy) hx))
  · calc
      _ ≤ (bchLogMetricConstant s (Fintype.card κ) H 1 : ℝ) * (K * dist x (y * γ)) :=
        mul_le_mul_of_nonneg_left hdist (NNReal.coe_nonneg _)
      _ < 1 := by nlinarith [hnear]
  · have hA := bchBoxCoordinateBound_nonneg s (Fintype.card κ) H B.coe_nonneg
    calc
      _ ≤ ((matrixDenominator Q * l : ℕ) : ℝ) * (((Fintype.card κ : ℝ) + 1) * (HQ + 1)) *
          (bchBoxCoordinateBound s (Fintype.card κ) H B *
            (bchLogMetricConstant s (Fintype.card κ) H 1 : ℝ)) * (K * dist x (y * γ)) :=
        mul_le_mul_of_nonneg_left hdist (by positivity)
      _ < 1 := by nlinarith [hsmall]

theorem exists_uniform_lattice_image_gap
    (e : Basis κ ℝ L) (c : κ → κ → κ → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Q : Matrix ι κ ℚ) (HQ B K : ℝ≥0) (hB : 1 ≤ B)
    (hQ : ∀ i j, |(Q i j : ℝ)| ≤ HQ) (l : ℕ) (hl : 0 < l)
    (J Λ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hJ : ∀ g, g ∈ J ↔ (fun i j => (Q i j : ℝ)) *ᵥ basisHomeomorph e g = 0)
    (hΛ : ∀ γ ∈ Λ, basisHomeomorph e γ ∈ realDenominatorGrid l)
    (S : Set (NilpotentLieBCHGroup L s hnil)) (hS : S ⊆ J)
    (hprod : ∀ x ∈ S, ∀ y ∈ S, ∀ i, |e.repr (y⁻¹ * x).coord i| ≤ B)
    (hleft : letI := rightMetricSpace (hnil := hnil) e;
      ∀ y ∈ S, LipschitzWith K (fun z => y⁻¹ * z)) :
    letI := rightMetricSpace (hnil := hnil) e
    let C := bchLogMetricConstant s (Fintype.card κ) H 1
    let A := bchBoxCoordinateBound s (Fintype.card κ) H B
    ∃ ε : ℝ≥0, 0 < ε ∧
      (ε : ℝ)⁻¹ = (C : ℝ) * K +
        ((matrixDenominator Q * l : ℕ) : ℝ) * (((Fintype.card κ : ℝ) + 1) * (HQ + 1)) *
          (A * C) * K + 1 ∧
      ∀ x ∈ S, ∀ y ∈ S, ∀ γ ∈ Λ, dist x (y * γ) < ε → γ ∈ J := by
  let := rightMetricSpace (hnil := hnil) e
  let a : ℝ := (bchLogMetricConstant s (Fintype.card κ) H 1 : ℝ) * K
  let b : ℝ := ((matrixDenominator Q * l : ℕ) : ℝ) *
    (((Fintype.card κ : ℝ) + 1) * (HQ + 1)) *
    (bchBoxCoordinateBound s (Fintype.card κ) H B *
      (bchLogMetricConstant s (Fintype.card κ) H 1 : ℝ)) * K
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by
    have := bchBoxCoordinateBound_nonneg s (Fintype.card κ) H B.coe_nonneg
    dsimp [b]
    positivity
  have hr : 0 < a + b + 1 := by linarith
  let ε : ℝ≥0 := ⟨(a + b + 1)⁻¹, (inv_pos.mpr hr).le⟩
  refine ⟨ε, show (0 : ℝ) < (a + b + 1)⁻¹ from inv_pos.mpr hr, ?_, ?_⟩
  · exact inv_inv (a + b + 1)
  · intro x hx y hy γ hγ hnear
    have hscaled : (a + b + 1) * dist x (y * γ) < 1 := by
      have h := mul_lt_mul_of_pos_left hnear hr
      change (a + b + 1) * dist x (y * γ) < (a + b + 1) * (a + b + 1)⁻¹ at h
      simpa only [mul_inv_cancel₀ hr.ne'] using h
    apply lattice_translate_mem_of_small_dist e c hstructure hc Q HQ B K hB hQ l hl
      J hJ x y γ (hS hx) (hS hy) (hΛ γ hγ) (hprod x hx y hy) (hleft y hy)
    · change a * dist x (y * γ) < 1
      nlinarith [dist_nonneg (x := x) (y := y * γ)]
    · change b * dist x (y * γ) < 1
      nlinarith [dist_nonneg (x := x) (y := y * γ)]

end Erdos3.NilpotentLieBCHGroup

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHQuotientLocalIsometry
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

local notation "E" => ℝ ⊗[ℚ] L
local notation "G" => NilpotentLieBCHGroup E s (realification_lowerCentralSeries_eq_bot hnil)

section Topology

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

end Topology

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

local notation "E" => ℝ ⊗[ℚ] L
local notation "G" => NilpotentLieBCHGroup E s (realification_lowerCentralSeries_eq_bot hnil)

section Topology

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

end Topology

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module _root_.Set

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

@[instance_reducible]
noncomputable def quotientMetricSpace (e : Basis ι ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) :
    MetricSpace (NilpotentLieBCHGroup L s hnil ⧸ Γ) := by
  letI : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  letI := rightMetricSpace (hnil := hnil) e
  letI := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  exact rightCosetMetricSpace Γ hΓ

theorem quotientMetricSpace_edist_mk (e : Basis ι ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
    (x y : NilpotentLieBCHGroup L s hnil) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := quotientMetricSpace e Γ hΓ
    edist (QuotientGroup.mk x : _ ⧸ Γ) (QuotientGroup.mk y) = ⨅ γ : Γ, edist x (y * γ) := rfl

theorem quotientMetricSpace_lipschitz_mk (e : Basis ι ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := quotientMetricSpace e Γ hΓ
    LipschitzWith 1 (QuotientGroup.mk : NilpotentLieBCHGroup L s hnil → _ ⧸ Γ) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  exact rightCosetMetricSpace_lipschitz_mk Γ hΓ

end Erdos3.NilpotentLieBCHGroup

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

local notation "G" => NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)

@[instance_reducible]
noncomputable def realificationQuotientMetricSpace (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    MetricSpace (G ⧸ Γ.map NilpotentLieBCHGroup.realificationHom) :=
  NilpotentLieBCHGroup.quotientMetricSpace (e.baseChange ℝ)
    (Γ.map NilpotentLieBCHGroup.realificationHom)
    (NilpotentLieBCHGroup.realification_subgroup_closed_discrete e Γ l hl houter).1

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

noncomputable def realificationLieHom (φ : L →ₗ⁅ℚ⁆ M) :
    (ℝ ⊗[ℚ] L) →ₗ⁅ℝ⁆ (ℝ ⊗[ℚ] M) where
  toLinearMap := φ.toLinearMap.baseChange ℝ
  map_lie' {x y} := (LieAlgebra.ExtendScalars.map (AlgHom.id ℚ ℝ) φ).map_lie x y

@[simp] theorem realificationLieHom_tmul (φ : L →ₗ⁅ℚ⁆ M) (a : ℝ) (x : L) :
    realificationLieHom φ (a ⊗ₜ[ℚ] x) = a ⊗ₜ[ℚ] φ x := rfl

theorem realificationLieHom_basis (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (k : κ) (i : ι) :
    (f.baseChange ℝ).repr (realificationLieHom φ ((e.baseChange ℝ) i)) k =
      (f.repr (φ (e i)) k : ℝ) := by
  simp only [Basis.baseChange_apply, realificationLieHom_tmul, Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def]

namespace NilpotentLieBCHGroup

variable {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

noncomputable def realificationMap (φ : L →ₗ⁅ℚ⁆ M) :
    NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil) →*
      NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) t (realification_lowerCentralSeries_eq_bot hM) :=
  mapReal (realificationLieHom φ)

@[simp] theorem realificationMap_coord (φ : L →ₗ⁅ℚ⁆ M)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)) :
    (realificationMap (hnil := hnil) (hM := hM) φ g).coord = realificationLieHom φ g.coord := rfl

theorem realificationMap_realificationHom_ofSteps (φ : L →ₗ⁅ℚ⁆ M)
    (g : NilpotentLieBCHGroup L s hnil) :
    realificationMap (hnil := hnil) (hM := hM) φ (realificationHom g) =
      realificationHom (mapOfSteps (hM := hM) φ g) := by
  apply ext
  rfl

theorem realificationMap_realificationHom
    {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}
    (φ : L →ₗ⁅ℚ⁆ M) (g : NilpotentLieBCHGroup L s hnil) :
    realificationMap (hnil := hnil) (hM := hM) φ (realificationHom g) =
      realificationHom (map (hM := hM) φ g) := by
  apply ext
  rfl

theorem realificationMap_subgroup (φ : L →ₗ⁅ℚ⁆ M)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (Λ : Subgroup (NilpotentLieBCHGroup M t hM)) (hφ : Γ ≤ Λ.comap (mapOfSteps φ)) :
    Γ.map realificationHom ≤ (Λ.map realificationHom).comap
      (realificationMap (hnil := hnil) (hM := hM) φ) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  change realificationMap (hnil := hnil) (hM := hM) φ (realificationHom y) ∈ Λ.map realificationHom
  rw [realificationMap_realificationHom_ofSteps (hM := hM)]
  exact Subgroup.mem_map.mpr ⟨mapOfSteps φ y, hφ hy, rfl⟩

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

open scoped NNReal

def coordinateLipschitzBound (m n : ℕ) (B : ℝ≥0) : ℝ≥0 :=
  ((m : ℝ≥0) + n + 1) * (B + 1)

theorem coordinateLipschitzBound_pos (m n : ℕ) (B : ℝ≥0) :
    0 < coordinateLipschitzBound m n B := by
  unfold coordinateLipschitzBound
  positivity

theorem coordinateLipschitzBound_le_exp (m n : ℕ) (B : ℝ≥0) {p : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hn : (n : ℝ) ≤ p)
    (hB : (B : ℝ) ≤ Real.exp p) :
    (coordinateLipschitzBound m n B : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
  have hdim : (m : ℝ) + n + 1 ≤ Real.exp (2 * p) := by
    linarith [Real.add_one_le_exp (2 * p)]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hheight : (B : ℝ) + 1 ≤ Real.exp (p + 1) := by
    calc
      _ ≤ Real.exp p * 2 := by linarith [Real.one_le_exp_iff.mpr hp]
      _ ≤ Real.exp p * Real.exp 1 := mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg _)
      _ = Real.exp (p + 1) := (Real.exp_add _ _).symm
  change ((m : ℝ) + n + 1) * ((B : ℝ) + 1) ≤ _
  calc
    _ ≤ Real.exp (2 * p) * Real.exp (p + 1) :=
      mul_le_mul hdim hheight (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (3 * p + 1) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp ((p + 2) ^ 2) := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])

namespace NilpotentLieBCHGroup

open Module

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

variable (e : Basis ι ℝ L) (f : Basis κ ℝ M) (φ : L →ₗ⁅ℝ⁆ M)

theorem lipschitz_mapReal_of_entry_bound (B : ℝ≥0)
    (hφ : ∀ k i, |f.repr (φ (e i)) k| ≤ B) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := rightMetricSpace (hnil := hM) f
    LipschitzWith (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) B)
      (mapReal (hnil := hnil) (hM := hM) φ) := by
  apply lipschitz_mapReal_of_coordinate_bound e f φ (coordinateLipschitzBound_pos _ _ _)
  intro w
  exact basisCoordinateMap_L2_bound e f φ.toLinearMap B B.coe_nonneg hφ w

theorem lipschitz_mapReal_of_rational_height (A : κ → ι → ℚ) (H : ℕ)
    (hA : ∀ k i, f.repr (φ (e i)) k = (A k i : ℝ))
    (hH : ∀ k i, RationalHeightLE (A k i) H) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := rightMetricSpace (hnil := hM) f
    LipschitzWith (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) H)
      (mapReal (hnil := hnil) (hM := hM) φ) := by
  apply lipschitz_mapReal_of_entry_bound e f φ H
  intro k i
  rw [hA]
  exact (hH k i).abs_real_le

variable (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (Λ : Subgroup (NilpotentLieBCHGroup M t hM))
  (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
  (hΛ : IsClosed (Λ : Set (NilpotentLieBCHGroup M t hM)))
  (hmap : Γ ≤ Λ.comap (mapReal φ))

theorem lipschitz_quotient_mapReal_of_entry_bound (B : ℝ≥0)
    (hφ : ∀ k i, |f.repr (φ (e i)) k| ≤ B) :
    letI := quotientMetricSpace e Γ hΓ
    letI := quotientMetricSpace f Λ hΛ
    LipschitzWith (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) B)
      (cosetMap Γ Λ (mapReal φ) hmap) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let : FiniteDimensional ℝ M := f.finiteDimensional_of_finite
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace (hnil := hM) f
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hM) f
  exact lipschitz_cosetMap Γ Λ hΓ hΛ (mapReal φ) hmap
    (lipschitz_mapReal_of_entry_bound e f φ B hφ)

end NilpotentLieBCHGroup

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

section Distance

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def basisQuotientDist (e : Basis ι ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) (x y : _ ⧸ Γ) : ℝ :=
  letI := quotientMetricSpace e Γ hΓ
  dist x y

end Distance

section Map

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

theorem basisQuotientDist_mapReal_le (e : Basis ι ℝ L) (f : Basis κ ℝ M)
    (φ : L →ₗ⁅ℝ⁆ M) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (Λ : Subgroup (NilpotentLieBCHGroup M s hM))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
    (hΛ : IsClosed (Λ : Set (NilpotentLieBCHGroup M s hM)))
    (hmap : Γ ≤ Λ.comap (mapReal φ)) (B : ℝ≥0) (hφ : ∀ k i, |f.repr (φ (e i)) k| ≤ B)
    (x y : _ ⧸ Γ) :
    basisQuotientDist f Λ hΛ (cosetMap Γ Λ (mapReal φ) hmap x) (cosetMap Γ Λ (mapReal φ) hmap y) ≤
      coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) B * basisQuotientDist e Γ hΓ x y := by
  let := quotientMetricSpace e Γ hΓ
  let := quotientMetricSpace f Λ hΛ
  exact (lipschitz_quotient_mapReal_of_entry_bound e f φ Γ Λ hΓ hΛ hmap B hφ).dist_le_mul x y

end Map

section BasisChange

variable {ι κ L : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

omit [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L] in
@[simp] theorem mapReal_id (x : NilpotentLieBCHGroup L s hnil) :
    mapReal (hM := hnil) (LieHom.id : L →ₗ⁅ℝ⁆ L) x = x := rfl

theorem basisQuotientDist_change_le (e : Basis ι ℝ L) (f : Basis κ ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
    (B : ℝ≥0) (hB : ∀ k i, |f.repr (e i) k| ≤ B) (x y : _ ⧸ Γ) :
    basisQuotientDist f Γ hΓ x y ≤
      coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) B * basisQuotientDist e Γ hΓ x y := by
  have hmap : Γ ≤ Γ.comap (mapReal (LieHom.id : L →ₗ⁅ℝ⁆ L)) := by
    intro g hg
    simpa only [Subgroup.mem_comap, mapReal_id] using hg
  have heq : cosetMap Γ Γ (mapReal (LieHom.id : L →ₗ⁅ℝ⁆ L)) hmap = id := by
    funext z
    induction z using Quotient.inductionOn with
    | h z => rfl
  simpa only [heq, id_eq] using
    basisQuotientDist_mapReal_le e f LieHom.id Γ Γ hΓ hΓ hmap B hB x y

end BasisChange

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (a : NilpotentLieBCHGroup L s hnil)

theorem lipschitz_conjugation_of_basis_bound (B : ℝ≥0)
    (hB : ∀ i k, |e.repr (a * (⟨e i⟩ : NilpotentLieBCHGroup L s hnil) * a⁻¹).coord k| ≤ B) :
    letI := rightMetricSpace (hnil := hnil) e
    LipschitzWith (coordinateLipschitzBound (Fintype.card ι) (Fintype.card ι) B)
      (MulAut.conj a) := by
  classical
  apply lipschitz_linear_hom e e (MulAut.conj a).toMonoidHom (conjugationLinearMap e a)
    (homCoordinates_conjugation_eq e a) (coordinateLipschitzBound_pos _ _ _)
  intro v
  apply coordinateLinearMap_L2_bound _ B B.coe_nonneg
  intro k i
  rw [conjugationLinearMap_basis]
  exact hB i k

theorem lipschitz_mul_left_of_basis_bound (B : ℝ≥0)
    (hB : ∀ i k, |e.repr (a * (⟨e i⟩ : NilpotentLieBCHGroup L s hnil) * a⁻¹).coord k| ≤ B) :
    letI := rightMetricSpace (hnil := hnil) e
    LipschitzWith (coordinateLipschitzBound (Fintype.card ι) (Fintype.card ι) B)
      (fun x => a * x) := by
  let := rightMetricSpace (hnil := hnil) e
  have h := (rightMetricSpace_isometry_mul_right e a).lipschitz.comp
    (lipschitz_conjugation_of_basis_bound e a B hB)
  simpa only [one_mul, Function.comp_def, MulAut.conj_apply, mul_assoc, inv_mul_cancel, mul_one] using h

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct NNReal

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

variable (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)

theorem lipschitz_realificationMap (H : ℕ)
    (hH : ∀ k i, RationalHeightLE (f.repr (φ (e i)) k) H) :
    letI := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hnil) (e.baseChange ℝ)
    letI := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hM) (f.baseChange ℝ)
    LipschitzWith (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) H)
      (realificationMap (hnil := hnil) (hM := hM) φ) :=
  lipschitz_mapReal_of_rational_height (e.baseChange ℝ) (f.baseChange ℝ) (realificationLieHom φ)
    (fun k i => f.repr (φ (e i)) k) H (realificationLieHom_basis e f φ) hH

theorem exists_realificationMap_lipschitz_exp_bound (H : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hH : ∀ k i, RationalHeightLE (f.repr (φ (e i)) k) H) :
    letI := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hnil) (e.baseChange ℝ)
    letI := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hM) (f.baseChange ℝ)
    ∃ C : ℝ≥0, 0 < C ∧ (C : ℝ) ≤ Real.exp ((p + 2) ^ 2) ∧
      LipschitzWith C (realificationMap (hnil := hnil) (hM := hM) φ) :=
  ⟨coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) H,
    coordinateLipschitzBound_pos _ _ _, coordinateLipschitzBound_le_exp _ _ H hp hκ hι hHp,
    lipschitz_realificationMap e f φ H hH⟩

variable (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (Λ : Subgroup (NilpotentLieBCHGroup M t hM)) (hφ : Γ ≤ Λ.comap (mapOfSteps φ))

theorem lipschitz_realificationMap_quotient (l m : ℕ) (hl : 0 < l) (hm : 0 < m)
    (hΓ : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (hΛ : bchSubgroupCoordinates f Λ ⊆ denominatorGrid m)
    (H : ℕ) (hH : ∀ k i, RationalHeightLE (f.repr (φ (e i)) k) H) :
    letI := realificationQuotientMetricSpace e Γ l hl hΓ
    letI := realificationQuotientMetricSpace f Λ m hm hΛ
    LipschitzWith (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) H)
      (cosetMap (Γ.map realificationHom) (Λ.map realificationHom)
        (realificationMap (hnil := hnil) (hM := hM) φ)
        (realificationMap_subgroup φ Γ Λ hφ)) := by
  apply lipschitz_quotient_mapReal_of_entry_bound (e.baseChange ℝ) (f.baseChange ℝ)
    (realificationLieHom φ) (Γ.map realificationHom) (Λ.map realificationHom)
    (realification_subgroup_closed_discrete e Γ l hl hΓ).1
    (realification_subgroup_closed_discrete f Λ m hm hΛ).1
    (realificationMap_subgroup φ Γ Λ hφ) H
  intro k i
  rw [realificationLieHom_basis]
  exact (hH k i).abs_real_le

theorem exists_realificationMap_quotient_lipschitz_exp_bound
    (l m : ℕ) (hl : 0 < l) (hm : 0 < m)
    (hΓ : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (hΛ : bchSubgroupCoordinates f Λ ⊆ denominatorGrid m)
    (H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hH : ∀ k i, RationalHeightLE (f.repr (φ (e i)) k) H) :
    letI := realificationQuotientMetricSpace e Γ l hl hΓ
    letI := realificationQuotientMetricSpace f Λ m hm hΛ
    ∃ C : ℝ≥0, 0 < C ∧ (C : ℝ) ≤ Real.exp ((p + 2) ^ 2) ∧
      LipschitzWith C (cosetMap (Γ.map realificationHom) (Λ.map realificationHom)
        (realificationMap (hnil := hnil) (hM := hM) φ) (realificationMap_subgroup φ Γ Λ hφ)) :=
  ⟨coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) H,
    coordinateLipschitzBound_pos _ _ _, coordinateLipschitzBound_le_exp _ _ H hp hκ hι hHp,
    lipschitz_realificationMap_quotient e f φ Γ Λ hφ l m hl hm hΓ hΛ H hH⟩

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3.NilpotentLieBCHGroup

end

end OAI

end


