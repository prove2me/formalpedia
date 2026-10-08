-- Prove2me | Definitions.Def_OAIErdos3B089
-- name    : OAIErdos3B089
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T13:00:53.972153+00:00
-- url     : https://prove2.me/theorems/e31929f9-9d2f-46ec-a962-f7a271bcecf4
-- title:
--   OpenAI Erdős-3 split, definitions bundle 90 of 91
-- statement:
--   Definitions bundle 90 of 91 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B088`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 90 available.
--
--   Modules: `OAI.Erdos3.DualFirstOrderCongruent`, `OAI.Erdos3.IsCentralLieBasis`, `OAI.Erdos3.IsCentralLieBasis.bch_low_coordinate`, `OAI.Erdos3.IsCentralLieBasis.bch_remainder_mem_tail`, `OAI.Erdos3.IsCentralLieBasis.exists_ordered_lattice_generators`, `OAI.Erdos3.IsCentralLieBasis.exists_surjective_orderedZpowProduct`, `OAI.Erdos3.IsCentralLieBasis.exists_tail_generator`, `OAI.Erdos3.IsCentralLieBasis.leadingCoordinateSubgroup`, `OAI.Erdos3.IsCentralLieBasis.leadingCoordinateSubgroup_isAddCyclic`, `OAI.Erdos3.IsCentralLieBasis.leadingCoordinateSubgroup_le_zmultiples`, `OAI.Erdos3.IsCentralLieBasis.lie_mem_tail_succ`, `OAI.Erdos3.IsCentralLieBasis.subgroupPowerCover_index_le`, `OAI.Erdos3.IsCentralLieBasis.tailIdeal`, `OAI.Erdos3.IsRealCentralLieBasis`, `OAI.Erdos3.IsRealCentralLieBasis.lie_mem_tail_succ`, `OAI.Erdos3.IsRealCentralLieBasis.tailIdeal`, `OAI.Erdos3.NilpotentAlgebraFiltration.exp_eq_quadratic`, `OAI.Erdos3.NilpotentAlgebraFiltration.mul_eq_zero_of_degrees`, `OAI.Erdos3.NilpotentAlgebraFiltration.nilpotentBCH_eq_quadratic`, `OAI.Erdos3.NilpotentLieBCHGroup.conjugationCoord_eq_add_lie`, `OAI.Erdos3.NilpotentLieBCHGroup.conjugation_polynomial`, `OAI.Erdos3.NilpotentLieBCHGroup.dist_le_bchBoxMetricConstant`, `OAI.Erdos3.NilpotentLieBCHGroup.dist_le_coordinateL2Norm_mul_inv`, `OAI.Erdos3.NilpotentLieBCHGroup.dist_linear_lift_le`, `OAI.Erdos3.NilpotentLieBCHGroup.dist_one_le_coordinateL2Norm`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjoint_conjugation_mod`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjoint_current_bracket_relation`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjoint_eq_add_lie`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjoint_eq_conjugationCoord`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjoint_eq_conjugation_of_abelian_ideal`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjoint_eq_self_of_lie_eq_zero`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjoint_mem_of_invariant`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjoint_sub_first_bracket_mem`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjoint_sub_mem`, `OAI.Erdos3.NilpotentLieBCHGroup.dualAdjoint_sub_mem_ideal`, `OAI.Erdos3.NilpotentLieBCHGroup.dualLinearLift_adjoint`, `OAI.Erdos3.NilpotentLieBCHGroup.dualLinearLift_adjoint_eq`, `OAI.Erdos3.NilpotentLieBCHGroup.dualLinearLift_adjoint_of_steps`, `OAI.Erdos3.NilpotentLieBCHGroup.dualLinearLift_logDerivative`, `OAI.Erdos3.NilpotentLieBCHGroup.dualLinearLift_logDerivative_eq`, `OAI.Erdos3.NilpotentLieBCHGroup.dualLogDerivative_inv`, `OAI.Erdos3.NilpotentLieBCHGroup.dualLogDerivative_mem_of_invariant`, `OAI.Erdos3.NilpotentLieBCHGroup.dualLogDerivative_one`, `OAI.Erdos3.NilpotentLieBCHGroup.dualLogDerivative_remove`, `OAI.Erdos3.NilpotentLieBCHGroup.dualLogDerivative_sub_mem`, `OAI.Erdos3.NilpotentLieBCHGroup.dualLogDerivative_sub_tangent_mem`, `OAI.Erdos3.NilpotentLieBCHGroup.enorm_mfderiv_coordinateLine`, `OAI.Erdos3.NilpotentLieBCHGroup.exists_coordinateBox_metric_cover`, `OAI.Erdos3.NilpotentLieBCHGroup.exists_local_metric_lifts_of_section`, `OAI.Erdos3.NilpotentLieBCHGroup.exists_local_metric_lifts_on_image`, `OAI.Erdos3.NilpotentLieBCHGroup.lipschitzOn_basisHomeomorph_symm_box`, `OAI.Erdos3.NilpotentLieBCHGroup.map_dualAdjoint`, `OAI.Erdos3.NilpotentLieBCHGroup.norm_mfderiv_coordinateLine`, `OAI.Erdos3.NilpotentLieBCHGroup.pathELength_coordinateLine`, `OAI.Erdos3.NilpotentLieBCHGroup.quotient_coordinate_injOn`, `OAI.Erdos3.NilpotentLieBCHGroup.realBCHLine`, `OAI.Erdos3.NilpotentLieBCHGroup.realBCHLine_add`, `OAI.Erdos3.NilpotentLieBCHGroup.realBCHLine_commute`, `OAI.Erdos3.NilpotentLieBCHGroup.realBCHLine_dist_one_le`, `OAI.Erdos3.NilpotentLieBCHGroup.realBCHLine_one`, `OAI.Erdos3.NilpotentLieBCHGroup.realBCHLine_zero`, `OAI.Erdos3.NilpotentLieFiltration.adjoint_current_layer_relation`, `OAI.Erdos3.NilpotentLieFiltration.dualAdjoint_sub_first_bracket_mem_layer`, `OAI.Erdos3.NilpotentLieFiltration.dualAdjoint_sub_mem_layer`, `OAI.Erdos3.NilpotentLieFiltration.dualAdjoint_sub_mem_next_layer`, `OAI.Erdos3.NilpotentLieFiltration.dualLogDerivative_sub_tangent_mem_layer`, `OAI.Erdos3.NilpotentLieFiltration.exists_bounded_sorted_adapted_basis`, `OAI.Erdos3.NilpotentLieFiltration.exists_central_basis`, `OAI.Erdos3.NilpotentLieFiltration.exists_normal_cover_exp_quadratic`, `OAI.Erdos3.NilpotentLieFiltration.exists_sharp_normal_cover`, `OAI.Erdos3.NilpotentLieFiltration.exists_sorted_adapted_basis`, `OAI.Erdos3.NilpotentLieFiltration.invariant_sup_layer`, `OAI.Erdos3.NilpotentLieFiltration.layer_eq_span_of_weighted_flag`, `OAI.Erdos3.NilpotentLieFiltration.lie_mem_invariant_sup_next_layer`, `OAI.Erdos3.NilpotentLieFiltration.logDerivative_current_layer_relation`, `OAI.Erdos3.NilpotentLieFiltration.subgroupPowerCover_index_le`, `OAI.Erdos3.basisTail`, `OAI.Erdos3.basisTail_antitone`, `OAI.Erdos3.basisTail_eq_span`, `OAI.Erdos3.basisTail_terminal`, `OAI.Erdos3.basisTail_zero`, `OAI.Erdos3.basis_mem_tail`, `OAI.Erdos3.bchBoxCoordinateBound_le_bchBoxMetricConstant`, `OAI.Erdos3.bchBoxMetricConstant`, `OAI.Erdos3.bchInjectivityRadius`, `OAI.Erdos3.bchInjectivityRadius_le_one`, `OAI.Erdos3.bchInjectivityRadius_pos`, `OAI.Erdos3.bchInjectivityRadius_separation`, `OAI.Erdos3.bchProductDenominator`, `OAI.Erdos3.bchProductDenominator_pos`, `OAI.Erdos3.bchProductNumeratorBound`, `OAI.Erdos3.bchProductPolynomial_coefficient_bound`, `OAI.Erdos3.centralLieBasis_of_finite_flag`, `OAI.Erdos3.centralLieBasis_of_sorted_filtration`, `OAI.Erdos3.centralPairSpan`, `OAI.Erdos3.centralPairSpan_lie_eq_zero`, `OAI.Erdos3.centralPairSpan_lie_mem`, `OAI.Erdos3.centralPairSubalgebra`, `OAI.Erdos3.centralPairSubalgebra_step_two`, `OAI.Erdos3.coordinateL2Norm_smul`, `OAI.Erdos3.dualBaseLinear_smul_real`, `OAI.Erdos3.dualBaseSubalgebra`, `OAI.Erdos3.dualConstant_infinitesimal_lie`, `OAI.Erdos3.dualCoordinates`, `OAI.Erdos3.dualCoordinates_apply`, `OAI.Erdos3.dualCoordinates_symm_apply`, `OAI.Erdos3.dualFirstOrderCongruent_constant`, `OAI.Erdos3.dualFirstOrderCongruent_infinitesimal`, `OAI.Erdos3.dualFirstOrderCongruent_lieBCH`, `OAI.Erdos3.dualFirstOrderIdeal`, `OAI.Erdos3.dualIdealMorphism`, `OAI.Erdos3.dualIdealMorphism_left`, `OAI.Erdos3.dualIdealRealization`, `OAI.Erdos3.dualIdealRealization_apply`, `OAI.Erdos3.dualIdealSubalgebra`, `OAI.Erdos3.dualInfinitesimal_constant_lie`, `OAI.Erdos3.dualInvariantSubalgebra`, `OAI.Erdos3.dualInvariantTangentIdeal`, `OAI.Erdos3.dualLinearLift`, `OAI.Erdos3.dualLinearLift_apply`, `OAI.Erdos3.dualLinearLift_base`, `OAI.Erdos3.dualLinearLift_constant`, `OAI.Erdos3.dualLinearLift_infinitesimal`, `OAI.Erdos3.dualLinearLift_lieBCH`, `OAI.Erdos3.dualLinearLift_lieBCH_of_steps`, `OAI.Erdos3.dualLinearLift_tangent`, `OAI.Erdos3.dualQuotientEvaluate`, `OAI.Erdos3.dualQuotientEvaluate_apply`, `OAI.Erdos3.dualQuotientEvaluate_constant`, `OAI.Erdos3.dualQuotientEvaluate_infinitesimal`, `OAI.Erdos3.dualQuotientEvaluate_lieBCH`, `OAI.Erdos3.dualRealCoordinates`, `OAI.Erdos3.dualRealCoordinates_apply`, `OAI.Erdos3.dualRealCoordinates_symm_apply`, `OAI.Erdos3.dualRealLieAlgebra`, `OAI.Erdos3.dualRealModule`, `OAI.Erdos3.dualRealScalarTower`, `OAI.Erdos3.dualTangentLinear_lie`, `OAI.Erdos3.dualTangentLinear_smul_real`, `OAI.Erdos3.dual_ext`, `OAI.Erdos3.enlarged_power_dominates_twice_add_sixteen`, `OAI.Erdos3.exists_basis_with_nested_supports`, `OAI.Erdos3.exists_bchBoxMetricConstant_exp_bound`, `OAI.Erdos3.exists_bchInverseBoxConstant_exp_bound`, `OAI.Erdos3.exists_boundedList_option_padding`, `OAI.Erdos3.exists_externalNet_large_masked_complex_score`, `OAI.Erdos3.exists_finite_bounded_list_enumeration`, `OAI.Erdos3.exists_simultaneous_external_pivot_masks`, `OAI.Erdos3.exists_sorted_flag_basis_from_spanning_set`, `OAI.Erdos3.exists_sorted_weighted_flag_basis`, `OAI.Erdos3.finiteCellMean`, `OAI.Erdos3.finiteCellMean_sum`, `OAI.Erdos3.finiteCellResidueMean`, `OAI.Erdos3.finiteCellWeights`, `OAI.Erdos3.finiteExp_freeCoefficientBound`, `OAI.Erdos3.finiteLog_freeCoefficientBound`, `OAI.Erdos3.finiteSeriesDenominator`, `OAI.Erdos3.finiteSeriesDenominator_pos`, `OAI.Erdos3.finiteSeriesNumerator`, `OAI.Erdos3.finiteSeriesNumeratorBound`, `OAI.Erdos3.finiteSeriesNumerator_cast`, `OAI.Erdos3.finiteSeriesNumerator_le`, `OAI.Erdos3.finiteSeriesWeight`, `OAI.Erdos3.finite_flag_weight_le`, `OAI.Erdos3.lieBCH_conjugation_of_central_commutator`, `OAI.Erdos3.lieBCH_conjugation_sub_mem`, `OAI.Erdos3.lieBCH_eq_quadratic_of_central_commutator`, `OAI.Erdos3.lieBCH_eq_quadratic_of_step_two`, `OAI.Erdos3.maskedIntegerImageDensity`, `OAI.Erdos3.mem_basisTail_succ_iff`, `OAI.Erdos3.mem_dualIdealSubalgebra`, `OAI.Erdos3.mem_dualInvariantSubalgebra`, `OAI.Erdos3.mem_dualInvariantTangentIdeal`, `OAI.Erdos3.mem_nestedSupport_iff`, `OAI.Erdos3.nestedSupportWeight`, `OAI.Erdos3.nestedSupportWeight_le`, `OAI.Erdos3.polynomialDualEval`, `OAI.Erdos3.polynomialDualEval_constant`, `OAI.Erdos3.polynomialDualEval_linear`, `OAI.Erdos3.realBasisTail`, `OAI.Erdos3.realBasisTail_antitone`, `OAI.Erdos3.span_image_inl_of_basis_extension`, `OAI.Erdos3.span_inter_eq_of_spanning_family`, `OAI.Erdos3.span_range_inl_complement_basis`, `OAI.Erdos3.span_weight_gt_eq_basisTail`, `OAI.Erdos3.sum_externalNet_masked_complex_scores`, `OAI.Erdos3.weightCut`, `OAI.Erdos3.weightCut_le`, `OAI.Erdos3.weight_gt_iff_cut_le`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B016
import Definitions.Def_OAIErdos3B018

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSmoothPartitionBudget
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Manifold MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (v : ι → ℝ)

theorem norm_mfderiv_coordinateLine (t : ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hnil) e
    ‖mfderiv 𝓘(ℝ) 𝓘(ℝ, ι → ℝ) (coordinateLine (hnil := hnil) e v) t 1‖ = coordinateL2Norm v := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  have hv := (congrArg (fun w : ι → ℝ => rightVelocity e (coordinateLine (hnil := hnil) e v t) w)
    (mfderiv_coordinateLine (hnil := hnil) e v t)).trans (rightVelocity_coordinateLine e v t)
  exact (norm_tangent_eq_coordinateL2Norm e (coordinateLine (hnil := hnil) e v t) _).trans
    (congrArg coordinateL2Norm hv)

theorem enorm_mfderiv_coordinateLine (t : ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hnil) e
    ‖mfderiv 𝓘(ℝ) 𝓘(ℝ, ι → ℝ) (coordinateLine (hnil := hnil) e v) t 1‖ₑ =
      ENNReal.ofReal (coordinateL2Norm v) := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  rw [← ofReal_norm]
  exact congrArg ENNReal.ofReal (norm_mfderiv_coordinateLine e v t)

theorem pathELength_coordinateLine :
    letI := basisChartedSpace (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hnil) e
    pathELength 𝓘(ℝ, ι → ℝ) (coordinateLine (hnil := hnil) e v) 0 1 =
      ENNReal.ofReal (coordinateL2Norm v) := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  rw [pathELength_eq_lintegral_mfderiv_Icc]
  have hf : (fun t : ℝ => ‖mfderiv 𝓘(ℝ) 𝓘(ℝ, ι → ℝ) (coordinateLine (hnil := hnil) e v) t 1‖ₑ) =
      fun _ => ENNReal.ofReal (coordinateL2Norm v) :=
    funext (enorm_mfderiv_coordinateLine e v)
  rw [hf]
  simp

theorem dist_one_le_coordinateL2Norm (g : NilpotentLieBCHGroup L s hnil) :
    letI := rightMetricSpace (hnil := hnil) e
    dist 1 g ≤ coordinateL2Norm (basisHomeomorph e g) := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  let := rightMetricSpace (hnil := hnil) e
  have hedist : edist 1 g ≤ ENNReal.ofReal (coordinateL2Norm (basisHomeomorph e g)) := by
    apply (riemannianEDist_le_pathELength
      (contMDiff_coordinateLine e (basisHomeomorph e g) 1).contMDiffOn
      (coordinateLine_zero e _) (by simp only [coordinateLine_one, Homeomorph.symm_apply_apply])
      zero_le_one).trans_eq
    exact pathELength_coordinateLine e _
  rw [dist_edist]
  exact (ENNReal.toReal_mono (by simp) hedist).trans_eq
    (ENNReal.toReal_ofReal (coordinateL2Norm_nonneg _))

theorem dist_le_coordinateL2Norm_mul_inv (x y : NilpotentLieBCHGroup L s hnil) :
    letI := rightMetricSpace (hnil := hnil) e
    dist x y ≤ coordinateL2Norm (basisHomeomorph e (x * y⁻¹)) := by
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  rw [← dist_mul_right x y y⁻¹, mul_inv_cancel, dist_comm]
  exact dist_one_le_coordinateL2Norm e (x * y⁻¹)

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open scoped NNReal

noncomputable def bchBoxMetricConstant (s d H : ℕ) (B : ℝ≥0) : ℝ≥0 :=
  ⟨(d + 1) * bchBoxCoordinateBound s d H B,
    mul_nonneg (by positivity) (bchBoxCoordinateBound_nonneg s d H B.coe_nonneg)⟩

namespace NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) {H : ℕ}
  (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
  (hc : ∀ i j k, RationalHeightLE (c i j k) H)

include hstructure hc

theorem dist_le_bchBoxMetricConstant (B : ℝ≥0) (hB : 1 ≤ B) {δ : ℝ} (hδ : 0 ≤ δ)
    (x y : NilpotentLieBCHGroup L s hnil)
    (hx : ∀ i, |e.repr x.coord i| ≤ B) (hy : ∀ i, |e.repr y.coord i| ≤ B)
    (hxy : ∀ i, |e.repr x.coord i - e.repr y.coord i| ≤ δ) :
    letI := rightMetricSpace (hnil := hnil) e
    dist x y ≤ bchBoxMetricConstant s (Fintype.card ι) H B * δ := by
  let := rightMetricSpace (hnil := hnil) e
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hcoord (i : ι) : |basisHomeomorph e (x * y⁻¹) i| ≤
      bchBoxCoordinateBound s (Fintype.card ι) H B * δ :=
    lieBCH_sub_coordinates_bound e c hstructure hc hnil x.coord y.coord hBr hδ hx hy hxy i
  calc
    _ ≤ coordinateL2Norm (basisHomeomorph e (x * y⁻¹)) := dist_le_coordinateL2Norm_mul_inv e x y
    _ ≤ (Fintype.card ι + 1) * (bchBoxCoordinateBound s (Fintype.card ι) H B * δ) :=
      coordinateL2Norm_le_card_bound _
        (mul_nonneg (bchBoxCoordinateBound_nonneg s _ H B.coe_nonneg) hδ) hcoord
    _ = _ := by change _ = ((Fintype.card ι + 1) * bchBoxCoordinateBound s (Fintype.card ι) H B) * δ; ring

theorem lipschitzOn_basisHomeomorph_symm_box (B : ℝ≥0) (hB : 1 ≤ B) :
    letI := rightMetricSpace (hnil := hnil) e
    LipschitzOnWith (bchBoxMetricConstant s (Fintype.card ι) H B)
      (basisHomeomorph (hnil := hnil) e).symm {v | ∀ i, |v i| ≤ B} := by
  let := rightMetricSpace (hnil := hnil) e
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv w hw
  apply dist_le_bchBoxMetricConstant e c hstructure hc B hB dist_nonneg
  · intro i
    change |basisHomeomorph (hnil := hnil) e ((basisHomeomorph (hnil := hnil) e).symm v) i| ≤ _
    simpa only [Homeomorph.apply_symm_apply] using hv i
  · intro i
    change |basisHomeomorph (hnil := hnil) e ((basisHomeomorph (hnil := hnil) e).symm w) i| ≤ _
    simpa only [Homeomorph.apply_symm_apply] using hw i
  · intro i
    change |basisHomeomorph (hnil := hnil) e ((basisHomeomorph (hnil := hnil) e).symm v) i -
      basisHomeomorph (hnil := hnil) e ((basisHomeomorph (hnil := hnil) e).symm w) i| ≤ _
    simpa only [Homeomorph.apply_symm_apply, Real.dist_eq] using dist_le_pi_dist v w i

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s t H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

theorem dist_linear_lift_le (e : Basis ι ℝ L) (f : Basis κ ℝ M) (σ : M →ₗ[ℝ] L)
    (B : ℝ≥0) (hσB : ∀ i j, |e.repr (σ (f j)) i| ≤ B)
    (c : κ → κ → κ → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = f.repr ⁅f i, f j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := rightMetricSpace (hnil := hM) f
    let C := bchLogMetricConstant t (Fintype.card κ) H 1
    let K := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ) B *
      ((Fintype.card κ : ℝ≥0) + 1) * C
    ∀ g : NilpotentLieBCHGroup M t hM, dist 1 g < (C⁻¹ : ℝ≥0) →
      dist 1 (⟨σ g.coord⟩ : NilpotentLieBCHGroup L s hnil) ≤ K * dist 1 g := by
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace (hnil := hM) f
  let C := bchLogMetricConstant t (Fintype.card κ) H 1
  let A := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ) B
  change ∀ g : NilpotentLieBCHGroup M t hM, dist 1 g < (C⁻¹ : ℝ≥0) →
    dist 1 (⟨σ g.coord⟩ : NilpotentLieBCHGroup L s hnil) ≤
      (A * ((Fintype.card κ : ℝ≥0) + 1) * C : ℝ≥0) * dist 1 g
  intro g hg
  have hC : (0 : ℝ) < C := bchLogMetricConstant_pos t (Fintype.card κ) H 1
  have hnear : (C : ℝ) * dist 1 g < (1 : ℝ≥0) := by
    rw [NNReal.coe_inv] at hg
    change (C : ℝ) * dist 1 g < 1
    have hh := mul_lt_mul_of_pos_left hg hC
    simpa only [mul_inv_cancel₀ hC.ne'] using hh
  have hnorm := norm_coordinates_le_of_near_one f c hstructure hc 1 le_rfl g hnear
  let h : NilpotentLieBCHGroup L s hnil := ⟨σ g.coord⟩
  have hcoord : basisHomeomorph e h = basisCoordinateMap f e σ (basisHomeomorph f g) := by
    change e.equivFun (σ g.coord) = e.equivFun (σ (f.equivFun.symm (f.equivFun g.coord)))
    rw [LinearEquiv.symm_apply_apply]
  calc
    dist 1 h ≤ coordinateL2Norm (basisHomeomorph e h) := dist_one_le_coordinateL2Norm e h
    _ ≤ (A : ℝ) * coordinateL2Norm (basisHomeomorph f g) := by
      rw [hcoord]
      exact basisCoordinateMap_L2_bound f e σ B B.coe_nonneg hσB _
    _ ≤ A * (((Fintype.card κ : ℝ) + 1) * ‖basisHomeomorph f g‖) := by
      apply mul_le_mul_of_nonneg_left _ A.coe_nonneg
      exact coordinateL2Norm_le_card_bound _ (norm_nonneg _) (fun j => by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (basisHomeomorph f g) j)
    _ ≤ A * (((Fintype.card κ : ℝ) + 1) * ((C : ℝ) * dist 1 g)) := by
      gcongr
    _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]; ring

theorem exists_local_metric_lifts_of_section (e : Basis ι ℝ L) (f : Basis κ ℝ M)
    (φ : L →ₗ⁅ℝ⁆ M) (σ : M →ₗ[ℝ] L) (hσ : Function.RightInverse σ φ)
    (B : ℝ≥0) (hσB : ∀ i j, |e.repr (σ (f j)) i| ≤ B)
    (c : κ → κ → κ → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = f.repr ⁅f i, f j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := rightMetricSpace (hnil := hM) f
    let C := bchLogMetricConstant t (Fintype.card κ) H 1
    let K := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ) B *
      ((Fintype.card κ : ℝ≥0) + 1) * C
    ∀ g : NilpotentLieBCHGroup M t hM, dist 1 g < (C⁻¹ : ℝ≥0) →
      ∃ h : NilpotentLieBCHGroup L s hnil,
        mapReal φ h = g ∧ dist 1 h ≤ K * dist 1 g := by
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace (hnil := hM) f
  dsimp only
  intro g hg
  exact ⟨⟨σ g.coord⟩, ext (hσ g.coord), dist_linear_lift_le e f σ B hσB c hstructure hc g hg⟩

theorem exists_local_metric_lifts_on_image (e : Basis ι ℝ L) (f : Basis κ ℝ M)
    (φ : L →ₗ⁅ℝ⁆ M) (σ : M →ₗ[ℝ] L)
    (hσ : (φ.toLinearMap.comp σ).comp φ.toLinearMap = φ.toLinearMap)
    (B : ℝ≥0) (hσB : ∀ i j, |e.repr (σ (f j)) i| ≤ B)
    (c : κ → κ → κ → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = f.repr ⁅f i, f j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := rightMetricSpace (hnil := hM) f
    let C := bchLogMetricConstant t (Fintype.card κ) H 1
    let K := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ) B *
      ((Fintype.card κ : ℝ≥0) + 1) * C
    ∀ g ∈ (mapReal (hnil := hnil) (hM := hM) φ).range, dist 1 g < (C⁻¹ : ℝ≥0) →
      ∃ h : NilpotentLieBCHGroup L s hnil,
        mapReal φ h = g ∧ dist 1 h ≤ K * dist 1 g := by
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace (hnil := hM) f
  dsimp only
  intro g hgrange hg
  obtain ⟨x, hx⟩ := hgrange
  have hcoord : φ x.coord = g.coord := congrArg NilpotentLieBCHGroup.coord hx
  have hs := DFunLike.congr_fun hσ x.coord
  change φ (σ (φ x.coord)) = φ x.coord at hs
  rw [hcoord] at hs
  exact ⟨⟨σ g.coord⟩, ext hs, dist_linear_lift_le e f σ B hσB c hstructure hc g hg⟩

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module

theorem coordinateL2Norm_smul {ι : Type*} [Fintype ι] (r : ℝ) (v : ι → ℝ) :
    coordinateL2Norm (r • v) = |r| * coordinateL2Norm v := by
  unfold coordinateL2Norm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

namespace NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

def realBCHLine (v : L) (r : ℝ) : NilpotentLieBCHGroup L s hnil := ⟨r • v⟩

theorem realBCHLine_zero (v : L) : realBCHLine (hnil := hnil) v 0 = 1 := by
  apply ext
  exact zero_smul ℝ v

theorem realBCHLine_one (v : L) : realBCHLine (hnil := hnil) v 1 = ⟨v⟩ := by
  apply ext
  exact one_smul ℝ v

theorem realBCHLine_add (v : L) (r t : ℝ) :
    realBCHLine (hnil := hnil) v (r + t) = realBCHLine v r * realBCHLine v t := by
  apply ext
  change (r + t) • v = lieBCH s (r • v) (t • v)
  rw [lieBCH_eq_add_of_lie_eq_zero hnil (by simp [smul_lie, lie_smul]), add_smul]

theorem realBCHLine_commute (v : L) (hv : ∀ w : L, ⁅v, w⁆ = 0)
    (r : ℝ) (g : NilpotentLieBCHGroup L s hnil) : Commute (realBCHLine v r) g := by
  apply commute_of_lie_eq_zero
  change ⁅r • v, g.coord⁆ = 0
  rw [smul_lie, hv, smul_zero]

variable [IsScalarTower ℚ ℝ L] {ι : Type*} [Fintype ι] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]

theorem realBCHLine_dist_one_le (e : Basis ι ℝ L) (v : L) (r : ℝ) :
    letI := rightMetricSpace (hnil := hnil) e
    dist (realBCHLine (hnil := hnil) v r) 1 ≤ |r| * coordinateL2Norm (e.equivFun v) := by
  let := rightMetricSpace (hnil := hnil) e
  rw [dist_comm]
  apply (dist_one_le_coordinateL2Norm e (realBCHLine v r)).trans_eq
  change coordinateL2Norm (e.equivFun (r • v)) = _
  rw [map_smul, coordinateL2Norm_smul]

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_bchBoxMetricConstant_exp_bound (s r : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ (d H : ℕ) (B : ℝ≥0) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (B : ℝ) ≤ Real.exp ((p + 2) ^ r) →
      (bchBoxMetricConstant s d H B : ℝ) ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C, hC, hheight⟩ := exists_bchCoordinateHeight_exp_budget s
  let D := C + 2 * s + r + 10
  refine ⟨D, by dsimp [D]; omega, ?_⟩
  intro d H B p hp hd hH hB
  let t : ℝ := p + D
  have hD3 : (3 : ℝ) ≤ D := by exact_mod_cast (show 3 ≤ D by dsimp [D]; omega)
  have ht : 3 ≤ t := by dsimp [t]; linarith
  have hp2 : p + 2 ≤ t := by dsimp [t]; linarith
  have hd1 : (d : ℝ) + 1 ≤ t := by dsimp [t]; linarith
  have hs1 : (s : ℝ) + 1 ≤ t := by
    have h : (s : ℝ) + 1 ≤ D := by exact_mod_cast (show s + 1 ≤ D by dsimp [D]; omega)
    dsimp [t]
    linarith
  have hbase : 2 * (d : ℝ) + 1 ≤ t ^ 2 := by nlinarith [sq_nonneg (t - 1)]
  have hpoly : ((d : ℝ) + 1) * (((s : ℝ) + 1) * (2 * d + 1) ^ s) * (2 * d) * s ≤
      t ^ (2 * s + 5) := by
    calc
      _ ≤ t * (t * (t ^ 2) ^ s) * t ^ 2 * t := by
        gcongr <;> linarith
      _ = _ := by rw [← pow_mul, pow_add]; ring
  have hpolyexp : ((d : ℝ) + 1) * (((s : ℝ) + 1) * (2 * d + 1) ^ s) * (2 * d) * s ≤
      Real.exp (t ^ (D - 1)) := by
    apply hpoly.trans
    apply (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ t)
      (by dsimp [D]; omega : 2 * s + 5 ≤ D - 1)).trans
    linarith [Real.add_one_le_exp (t ^ (D - 1))]
  have hcoef : (bchCoordinateHeight s d H : ℝ) ≤ Real.exp (t ^ (D - 1)) := by
    apply (hheight d H p hp hd hH).trans
    apply Real.exp_le_exp.mpr
    have hCD : (C : ℝ) ≤ D := by exact_mod_cast (show C ≤ D by dsimp [D]; omega)
    apply (pow_le_pow_left₀ (by positivity) (show p + C ≤ t by dsimp [t]; linarith) C).trans
    exact pow_le_pow_right₀ (by linarith) (by dsimp [D]; omega)
  have hlength : ((s * (2 * d + 1) : ℕ) : ℝ) ≤ t ^ 3 := by
    push_cast
    calc
      _ ≤ t * t ^ 2 := mul_le_mul (by linarith) hbase (by positivity) (by linarith)
      _ = _ := by ring
  have hinput : (B : ℝ) ^ (s * (2 * d + 1)) ≤ Real.exp (t ^ (D - 1)) := by
    calc
      _ ≤ (Real.exp ((p + 2) ^ r)) ^ (s * (2 * d + 1)) :=
        pow_le_pow_left₀ B.coe_nonneg hB _
      _ = Real.exp (((s * (2 * d + 1) : ℕ) : ℝ) * (p + 2) ^ r) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (t ^ 3 * t ^ r) := Real.exp_le_exp.mpr
        (mul_le_mul hlength (pow_le_pow_left₀ (by linarith) hp2 r) (by positivity) (by positivity))
      _ = Real.exp (t ^ (r + 3)) := by rw [← pow_add, Nat.add_comm 3 r]
      _ ≤ Real.exp (t ^ (D - 1)) := Real.exp_le_exp.mpr
        (pow_le_pow_right₀ (by linarith) (by dsimp [D]; omega))
  change ((d : ℝ) + 1) * bchBoxCoordinateBound s d H B ≤ _
  unfold bchBoxCoordinateBound
  push_cast
  calc
    _ = (((d : ℝ) + 1) * (((s : ℝ) + 1) * (2 * d + 1) ^ s) * (2 * d) * s) *
        bchCoordinateHeight s d H * (B : ℝ) ^ (s * (2 * d + 1)) := by ring
    _ ≤ Real.exp (t ^ (D - 1)) * Real.exp (t ^ (D - 1)) * Real.exp (t ^ (D - 1)) :=
      mul_le_mul (mul_le_mul hpolyexp hcoef (by positivity) (by positivity)) hinput
        (by positivity) (by positivity)
    _ = Real.exp (3 * t ^ (D - 1)) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (t ^ D) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ t * t ^ (D - 1) := mul_le_mul_of_nonneg_right ht (by positivity)
        _ = _ := by rw [← pow_succ', Nat.sub_add_cancel (by dsimp [D]; omega : 1 ≤ D)]
    _ = _ := rfl

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

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

theorem exists_coordinateBox_metric_cover {ι L : Type*} [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
    [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
    {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) (B : ℝ≥0) (hB : 1 ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    let K := bchBoxMetricConstant s (Fintype.card ι) H B
    let N := boxCoverMeshCount B K ε
    ∃ centers : (ι → Fin (N + 1)) → coordinateBox (hnil := hnil) e B,
      letI := rightMetricSpace (hnil := hnil) e
      ∀ x : coordinateBox (hnil := hnil) e B, ∃ j, dist x (centers j) ≤ ε := by
  let K := bchBoxMetricConstant s (Fintype.card ι) H B
  let N := boxCoverMeshCount B K ε
  have hN : 0 < N := boxCoverMeshCount_pos _ _ _
  let centers : (ι → Fin (N + 1)) → coordinateBox (hnil := hnil) e B := fun k =>
    ⟨(basisHomeomorph (hnil := hnil) e).symm (uniformBoxGrid B N k), by
      intro i
      change |basisHomeomorph (hnil := hnil) e
        ((basisHomeomorph (hnil := hnil) e).symm (uniformBoxGrid B N k)) i| ≤ B
      rw [Homeomorph.apply_symm_apply]
      exact uniformBoxGrid_mem B.coe_nonneg hN k i⟩
  refine ⟨centers, ?_⟩
  let := rightMetricSpace (hnil := hnil) e
  intro x
  obtain ⟨j, hj⟩ := exists_uniformBoxGrid_approx (lt_of_lt_of_le zero_lt_one hB) hN
    (basisHomeomorph (hnil := hnil) e x.val) x.property
  refine ⟨j, ?_⟩
  have h := (lipschitzOn_basisHomeomorph_symm_box (hnil := hnil) e c hstructure hc B hB).dist_le_mul
    (basisHomeomorph (hnil := hnil) e x.val) x.property
    (uniformBoxGrid B N j) (uniformBoxGrid_mem B.coe_nonneg hN j)
  have hdist := h.trans ((mul_le_mul_of_nonneg_left hj K.coe_nonneg).trans (boxCoverMeshCount_error K hε))
  simpa only [centers, Subtype.dist_eq, Homeomorph.symm_apply_apply] using hdist

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

noncomputable def bchInjectivityRadius (s d H l : ℕ) : ℝ :=
  1 / (4 * ((l : ℝ) + 1) * (bchBoxCoordinateBound s d H 1 + 1))

theorem bchInjectivityRadius_pos (s d H l : ℕ) : 0 < bchInjectivityRadius s d H l := by
  have := bchBoxCoordinateBound_nonneg s d H (B := 1) (by norm_num)
  unfold bchInjectivityRadius
  positivity

theorem bchInjectivityRadius_le_one (s d H l : ℕ) : bchInjectivityRadius s d H l ≤ 1 := by
  have hA := bchBoxCoordinateBound_nonneg s d H (B := 1) (by norm_num)
  unfold bchInjectivityRadius
  apply (div_le_one (by positivity)).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) l]

theorem bchInjectivityRadius_separation (s d H l : ℕ) (hl : 0 < l) :
    bchBoxCoordinateBound s d H 1 * (2 * bchInjectivityRadius s d H l) < 1 / (l : ℝ) := by
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hl1 : (0 : ℝ) < l + 1 := by positivity
  have hA := bchBoxCoordinateBound_nonneg s d H (B := 1) (by norm_num)
  have hA1 : 0 < bchBoxCoordinateBound s d H 1 + 1 := by linarith
  have hr := bchInjectivityRadius_pos s d H l
  calc
    _ ≤ (bchBoxCoordinateBound s d H 1 + 1) * (2 * bchInjectivityRadius s d H l) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 1 / (2 * ((l : ℝ) + 1)) := by
      unfold bchInjectivityRadius
      field_simp
      ring
    _ < 1 / (l : ℝ) := one_div_lt_one_div_of_lt hl' (by linarith)

namespace NilpotentLieBCHGroup

open Module

theorem quotient_coordinate_injOn
    {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
    [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
    [ContinuousSMul ℝ L] [T2Space L]
    {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)
    (z : NilpotentLieBCHGroup L s hnil) :
    Set.InjOn (fun v : ι → ℝ => (QuotientGroup.mk (z * (basisHomeomorph e).symm v) : _ ⧸ Γ))
      {v | ∀ i, |v i| ≤ bchInjectivityRadius s (Fintype.card ι) H l} :=
  quotient_coordinate_injOn_of_radius e c hstructure hc Γ l hl hgrid
    (bchInjectivityRadius_pos _ _ _ _).le (bchInjectivityRadius_le_one _ _ _ _)
    (bchInjectivityRadius_separation _ _ _ _ hl) z

end NilpotentLieBCHGroup

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

theorem enlarged_power_dominates_twice_add_sixteen {p : ℝ} (hp : 0 ≤ p)
    (C : ℕ) (hC : 2 ≤ C) :
    2 * (p + C) ^ C + 16 ≤ (p + (C + 5 : ℕ)) ^ (C + 5) := by
  let t : ℝ := p + (C + 5 : ℕ)
  have ht : 7 ≤ t := by
    have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
    dsimp [t]
    push_cast
    linarith
  have hpow : 1 ≤ t ^ C := one_le_pow₀ (by linarith)
  have hq : (p + C) ^ C ≤ t ^ C := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [t]
    push_cast
    linarith
  calc
    _ ≤ 18 * t ^ C := by linarith
    _ ≤ t ^ 2 * t ^ C := mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    _ = t ^ (C + 2) := by rw [← pow_add, Nat.add_comm]
    _ ≤ t ^ (C + 5) := pow_le_pow_right₀ (by linarith) (by omega)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem bchBoxCoordinateBound_le_bchBoxMetricConstant (s d H : ℕ) (B : ℝ≥0) :
    bchBoxCoordinateBound s d H B ≤ (bchBoxMetricConstant s d H B : ℝ) := by
  change bchBoxCoordinateBound s d H B ≤ ((d : ℝ) + 1) * bchBoxCoordinateBound s d H B
  have := bchBoxCoordinateBound_nonneg s d H B.coe_nonneg
  nlinarith [Nat.cast_nonneg (α := ℝ) d]

theorem exists_bchInverseBoxConstant_exp_bound (s a : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ (d H : ℕ) (B : ℝ≥0) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (B : ℝ) ≤ Real.exp ((p + 2) ^ a) →
      (bchInverseBoxConstant s d H B : ℝ) ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C₁, hC₁, hbox⟩ := exists_bchBoxMetricConstant_exp_bound s a
  obtain ⟨C₂, hC₂, hone⟩ := exists_bchBoxMetricConstant_exp_bound s 0
  let C := C₁ + C₂ + a + 4
  have hC : 2 ≤ C := by dsimp [C]; omega
  refine ⟨C + 5, by omega, ?_⟩
  intro d H B p hp hd hH hB
  let q := (p + C) ^ C
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
  have hBq : (B : ℝ) ≤ Real.exp q := by
    apply hB.trans
    apply Real.exp_le_exp.mpr
    apply (pow_le_pow_left₀ (by linarith) (show p + 2 ≤ p + C by linarith) a).trans
    exact pow_le_pow_right₀ (by linarith) (by dsimp [C]; omega)
  have hAq : bchBoxCoordinateBound s d H B ≤ Real.exp q :=
    (bchBoxCoordinateBound_le_bchBoxMetricConstant s d H B).trans
      ((hbox d H B p hp hd hH hB).trans (Real.exp_le_exp.mpr
        (shifted_power_self_mono (C := C₁) (D := C) hp (by omega) (by dsimp [C]; omega))))
  have hA1q : bchBoxCoordinateBound s d H 1 ≤ Real.exp q := by
    apply (bchBoxCoordinateBound_le_bchBoxMetricConstant s d H 1).trans
    have hunit : ((1 : ℝ≥0) : ℝ) ≤ Real.exp ((p + 2) ^ 0) := by
      simpa only [NNReal.coe_one, pow_zero] using
        Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
    apply (hone d H 1 p hp hd hH hunit).trans
    exact Real.exp_le_exp.mpr
      (shifted_power_self_mono (C := C₂) (D := C) hp (by omega) (by dsimp [C]; omega))
  have hnum : bchBoxCoordinateBound s d H B + 2 * (B : ℝ) ≤ 3 * Real.exp q := by linarith
  have hden : bchBoxCoordinateBound s d H 1 + 1 ≤ 2 * Real.exp q := by
    linarith [Real.one_le_exp hq]
  have h6 : (6 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  change (bchBoxCoordinateBound s d H B + 2 * (B : ℝ)) *
    (bchBoxCoordinateBound s d H 1 + 1) ≤ _
  calc
    _ ≤ (3 * Real.exp q) * (2 * Real.exp q) :=
      mul_le_mul hnum hden (by have := bchBoxCoordinateBound_nonneg s d H (B := 1) (by norm_num); linarith)
        (by positivity)
    _ = 6 * Real.exp (2 * q) := by rw [show 2 * q = q + q by ring, Real.exp_add]; ring
    _ ≤ Real.exp 16 * Real.exp (2 * q) := mul_le_mul_of_nonneg_right h6 (Real.exp_nonneg _)
    _ = Real.exp (2 * q + 16) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (enlarged_power_dominates_twice_add_sixteen hp C hC)

namespace NilpotentLieBCHGroup

open Module

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedImageMask
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal BigOperators

noncomputable def maskedIntegerImageDensity {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (P : I → ℝ) (f : (I → ℝ) → ℝ)
    (v : I → ℤ) : ℝ := by
  classical
  exact if v ∈ pivotFullImage A B then
    ((pivotFullImage A B).toAddSubgroup.index : ℝ) * f (fun i => (v i : ℝ) / P i) else 0

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DualIdealSteps
namespace OAI

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem dualConstant_infinitesimal_lie (x y : L) :
    ⁅dualConstantLie x, dualInfinitesimal y⁆ = dualInfinitesimal ⁅x, y⁆ := by
  change ⁅(1 : DualNumber ℚ) ⊗ₜ[ℚ] x, DualNumber.eps ⊗ₜ[ℚ] y⁆ = _
  rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul]
  rfl

theorem dualInfinitesimal_constant_lie (x y : L) :
    ⁅dualInfinitesimal x, dualConstantLie y⁆ = dualInfinitesimal ⁅x, y⁆ := by
  change ⁅DualNumber.eps ⊗ₜ[ℚ] x, (1 : DualNumber ℚ) ⊗ₜ[ℚ] y⁆ = _
  rw [LieAlgebra.ExtendScalars.bracket_tmul, mul_one]
  rfl

theorem dualTangentLinear_lie (x y : DualLieAlgebra L) :
    dualTangentLinear ⁅x, y⁆ =
      ⁅dualBaseLinear x, dualTangentLinear y⁆ + ⁅dualTangentLinear x, dualBaseLinear y⁆ := by
  have he := congrArg₂ (fun a b : DualLieAlgebra L => ⁅a, b⁆)
    (dualLie_decomposition x) (dualLie_decomposition y)
  calc
    _ = dualTangentLinear ⁅dualConstantLie (dualBaseLinear x) + dualInfinitesimal (dualTangentLinear x),
      dualConstantLie (dualBaseLinear y) + dualInfinitesimal (dualTangentLinear y)⁆ :=
      congrArg dualTangentLinear he
    _ = _ := by
      rw [LieRing.add_lie (dualConstantLie (dualBaseLinear x)) (dualInfinitesimal (dualTangentLinear x))
        (dualConstantLie (dualBaseLinear y) + dualInfinitesimal (dualTangentLinear y))]
      rw [LieRing.lie_add (dualConstantLie (dualBaseLinear x)) (dualConstantLie (dualBaseLinear y))
        (dualInfinitesimal (dualTangentLinear y))]
      rw [LieRing.lie_add (dualInfinitesimal (dualTangentLinear x)) (dualConstantLie (dualBaseLinear y))
        (dualInfinitesimal (dualTangentLinear y))]
      rw [dualConstant_infinitesimal_lie, dualInfinitesimal_constant_lie, dualInfinitesimal_lie,
        ← dualConstantLie.map_lie]
      simp only [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal,
        zero_add, add_zero]

noncomputable def dualIdealSubalgebra (I : LieIdeal ℚ L) : LieSubalgebra ℚ (DualLieAlgebra L) :=
  { I.toSubmodule.comap dualTangentLinear with
    lie_mem' := by
      intro x y hx hy
      change dualTangentLinear ⁅x, y⁆ ∈ I
      rw [dualTangentLinear_lie]
      exact I.add_mem (I.lie_mem hy) (lie_mem_left ℚ L I _ _ hx) }

@[simp] theorem mem_dualIdealSubalgebra (I : LieIdeal ℚ L) (x : DualLieAlgebra L) :
    x ∈ dualIdealSubalgebra I ↔ dualTangentLinear x ∈ I := Iff.rfl

noncomputable def dualIdealRealization (I J : LieIdeal ℚ L)
    (hIJ : ∀ x ∈ I, ∀ y ∈ I, ⁅x, y⁆ ∈ J) : dualIdealSubalgebra I →ₗ⁅ℚ⁆ L ⧸ J :=
  { toLinearMap := (lieQuotientMap J).toLinearMap.comp
      ((dualBaseLinear + dualTangentLinear).comp (dualIdealSubalgebra I).incl.toLinearMap)
    map_lie' := by
      intro x y
      change lieQuotientMap J (dualBaseLinear ⁅x.val, y.val⁆ + dualTangentLinear ⁅x.val, y.val⁆) =
        ⁅lieQuotientMap J (dualBaseLinear x.val + dualTangentLinear x.val),
          lieQuotientMap J (dualBaseLinear y.val + dualTangentLinear y.val)⁆
      rw [← (lieQuotientMap J).map_lie]
      rw [← sub_eq_zero, ← map_sub]
      apply (lieQuotientMap_eq_zero J _).mpr
      rw [dualBaseLinear_lie, dualTangentLinear_lie, LieRing.add_lie, LieRing.lie_add,
        LieRing.lie_add]
      have he : ⁅dualBaseLinear x.val, dualBaseLinear y.val⁆ +
          (⁅dualBaseLinear x.val, dualTangentLinear y.val⁆ +
            ⁅dualTangentLinear x.val, dualBaseLinear y.val⁆) -
          (⁅dualBaseLinear x.val, dualBaseLinear y.val⁆ +
            ⁅dualBaseLinear x.val, dualTangentLinear y.val⁆ +
              (⁅dualTangentLinear x.val, dualBaseLinear y.val⁆ +
                ⁅dualTangentLinear x.val, dualTangentLinear y.val⁆)) =
          -⁅dualTangentLinear x.val, dualTangentLinear y.val⁆ := by abel
      rw [he]
      exact J.neg_mem (hIJ _ x.property _ y.property) }

@[simp] theorem dualIdealRealization_apply (I J : LieIdeal ℚ L)
    (hIJ : ∀ x ∈ I, ∀ y ∈ I, ⁅x, y⁆ ∈ J) (x : dualIdealSubalgebra I) :
    dualIdealRealization I J hIJ x =
      lieQuotientMap J (dualBaseLinear x.val + dualTangentLinear x.val) := rfl

noncomputable def dualQuotientEvaluate (J : LieIdeal ℚ L) : DualLieAlgebra L →ₗ[ℚ] L ⧸ J :=
  (lieQuotientMap J).toLinearMap.comp (dualBaseLinear + dualTangentLinear)

@[simp] theorem dualQuotientEvaluate_apply (J : LieIdeal ℚ L) (x : DualLieAlgebra L) :
    dualQuotientEvaluate J x = lieQuotientMap J (dualBaseLinear x + dualTangentLinear x) := rfl

@[simp] theorem dualQuotientEvaluate_constant (J : LieIdeal ℚ L) (x : L) :
    dualQuotientEvaluate J (dualConstantLie x) = lieQuotientMap J x := by
  rw [dualQuotientEvaluate_apply, dualBaseLinear_constant, dualTangentLinear_constant, add_zero]

@[simp] theorem dualQuotientEvaluate_infinitesimal (J : LieIdeal ℚ L) (x : L) :
    dualQuotientEvaluate J (dualInfinitesimal x) = lieQuotientMap J x := by
  rw [dualQuotientEvaluate_apply, dualBaseLinear_infinitesimal, dualTangentLinear_infinitesimal, zero_add]

theorem dualQuotientEvaluate_lieBCH (I J : LieIdeal ℚ L)
    (hIJ : ∀ x ∈ I, ∀ y ∈ I, ⁅x, y⁆ ∈ J) (s : ℕ) {x y : DualLieAlgebra L}
    (hx : x ∈ dualIdealSubalgebra I) (hy : y ∈ dualIdealSubalgebra I) :
    dualQuotientEvaluate J (lieBCH s x y) =
      lieBCH s (dualQuotientEvaluate J x) (dualQuotientEvaluate J y) := by
  let a : dualIdealSubalgebra I := ⟨x, hx⟩
  let b : dualIdealSubalgebra I := ⟨y, hy⟩
  calc
    _ = dualQuotientEvaluate J ((dualIdealSubalgebra I).incl (lieBCH s a b)) :=
      congrArg (dualQuotientEvaluate J) (map_lieBCH (dualIdealSubalgebra I).incl s a b).symm
    _ = _ := map_lieBCH (dualIdealRealization I J hIJ) s a b

end Erdos3

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualAdjoint_conjugation_mod (I J : LieIdeal ℚ L)
    (hIJ : ∀ a ∈ I, ∀ b ∈ I, ⁅a, b⁆ ∈ J)
    (g : NilpotentLieBCHGroup L s hnil) (x : L) (hx : x ∈ I) :
    lieQuotientMap J (dualAdjoint g x) =
      lieQuotientMap J (g * (⟨x⟩ : NilpotentLieBCHGroup L s hnil) * g⁻¹).coord := by
  have hc : dualConstantLie g.coord ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (dualConstantLie g.coord) ∈ I
    rw [dualTangentLinear_constant]
    exact I.zero_mem
  have ht : dualInfinitesimal x ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (dualInfinitesimal x) ∈ I
    rwa [dualTangentLinear_infinitesimal]
  calc
    _ = dualQuotientEvaluate J
        (dualConstantHom g * dualTangentElement x * (dualConstantHom g)⁻¹).coord := by
      rw [dualAdjoint_spec]
      exact (dualQuotientEvaluate_infinitesimal J _).symm
    _ = _ := by
      change dualQuotientEvaluate J
        (lieBCH s (lieBCH s (dualConstantLie g.coord) (dualInfinitesimal x))
          (-dualConstantLie g.coord)) =
        lieQuotientMap J (lieBCH s (lieBCH s g.coord x) (-g.coord))
      rw [dualQuotientEvaluate_lieBCH I J hIJ s
        (lieBCH_mem (dualIdealSubalgebra I) s hc ht) ((dualIdealSubalgebra I).neg_mem hc),
        dualQuotientEvaluate_lieBCH I J hIJ s hc ht,
        map_neg, dualQuotientEvaluate_constant, dualQuotientEvaluate_infinitesimal,
        map_lieBCH, map_lieBCH, map_neg]

theorem dualAdjoint_eq_conjugation_of_abelian_ideal (I : LieIdeal ℚ L)
    (hI : ∀ a ∈ I, ∀ b ∈ I, ⁅a, b⁆ = 0)
    (g : NilpotentLieBCHGroup L s hnil) (x : L) (hx : x ∈ I) :
    dualAdjoint g x = (g * (⟨x⟩ : NilpotentLieBCHGroup L s hnil) * g⁻¹).coord := by
  have he := dualAdjoint_conjugation_mod I ⊥
    (fun a ha b hb => (Submodule.mem_bot ℚ).mpr (hI a ha b hb)) g x hx
  have hz : lieQuotientMap (⊥ : LieIdeal ℚ L)
      (dualAdjoint g x - (g * (⟨x⟩ : NilpotentLieBCHGroup L s hnil) * g⁻¹).coord) = 0 := by
    rw [map_sub, he, sub_self]
  exact sub_eq_zero.mp ((Submodule.mem_bot ℚ).mp ((lieQuotientMap_eq_zero _ _).mp hz))

end Erdos3.NilpotentLieBCHGroup

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def dualCoordinates : DualLieAlgebra L ≃ₗ[ℚ] L × L where
  toLinearMap := dualBaseLinear.prod dualTangentLinear
  invFun x := dualConstantLie x.1 + dualInfinitesimal x.2
  left_inv x := (dualLie_decomposition x).symm
  right_inv x := by ext <;> simp

@[simp] theorem dualCoordinates_apply (x : DualLieAlgebra L) :
    dualCoordinates x = (dualBaseLinear x, dualTangentLinear x) := rfl

@[simp] theorem dualCoordinates_symm_apply (x : L × L) :
    dualCoordinates.symm x = dualConstantLie x.1 + dualInfinitesimal x.2 := rfl

end Erdos3

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def dualFirstOrderIdeal (I J : LieIdeal ℚ L)
    (hIJ : ∀ x ∈ I, ∀ y ∈ I, ⁅x, y⁆ ∈ J) : LieIdeal ℚ (dualIdealSubalgebra I) :=
  { (I.toSubmodule.comap (dualBaseLinear.comp (dualIdealSubalgebra I).incl.toLinearMap)) ⊓
      (J.toSubmodule.comap (dualTangentLinear.comp (dualIdealSubalgebra I).incl.toLinearMap)) with
    lie_mem := by
      intro x y hy
      change dualBaseLinear ⁅x.val, y.val⁆ ∈ I ∧ dualTangentLinear ⁅x.val, y.val⁆ ∈ J
      rw [dualBaseLinear_lie, dualTangentLinear_lie]
      exact ⟨I.lie_mem hy.1, J.add_mem (J.lie_mem hy.2) (hIJ _ x.property _ hy.1)⟩ }

def DualFirstOrderCongruent (I J : LieIdeal ℚ L) (x y : DualLieAlgebra L) : Prop :=
  dualBaseLinear (x - y) ∈ I ∧ dualTangentLinear (x - y) ∈ J

theorem dualFirstOrderCongruent_lieBCH (I J : LieIdeal ℚ L)
    (hIJ : ∀ x ∈ I, ∀ y ∈ I, ⁅x, y⁆ ∈ J) (s : ℕ)
    {a b c d : DualLieAlgebra L}
    (ha : a ∈ dualIdealSubalgebra I) (hb : b ∈ dualIdealSubalgebra I)
    (hc : c ∈ dualIdealSubalgebra I) (hd : d ∈ dualIdealSubalgebra I)
    (hac : DualFirstOrderCongruent I J a c) (hbd : DualFirstOrderCongruent I J b d) :
    DualFirstOrderCongruent I J (lieBCH s a b) (lieBCH s c d) := by
  let K := dualFirstOrderIdeal I J hIJ
  let a' : dualIdealSubalgebra I := ⟨a, ha⟩
  let b' : dualIdealSubalgebra I := ⟨b, hb⟩
  let c' : dualIdealSubalgebra I := ⟨c, hc⟩
  let d' : dualIdealSubalgebra I := ⟨d, hd⟩
  have heac : lieQuotientMap K a' = lieQuotientMap K c' := by
    rw [← sub_eq_zero, ← map_sub]
    exact (lieQuotientMap_eq_zero K _).mpr hac
  have hebd : lieQuotientMap K b' = lieQuotientMap K d' := by
    rw [← sub_eq_zero, ← map_sub]
    exact (lieQuotientMap_eq_zero K _).mpr hbd
  have he : lieBCH s a' b' - lieBCH s c' d' ∈ K := by
    apply (lieQuotientMap_eq_zero K _).mp
    rw [map_sub, map_lieBCH, map_lieBCH, heac, hebd, sub_self]
  have hv : (lieBCH s a' b' - lieBCH s c' d').val = lieBCH s a b - lieBCH s c d := by
    change (dualIdealSubalgebra I).incl (lieBCH s a' b' - lieBCH s c' d') = _
    rw [map_sub, map_lieBCH, map_lieBCH]
    rfl
  change dualBaseLinear (lieBCH s a' b' - lieBCH s c' d').val ∈ I ∧
    dualTangentLinear (lieBCH s a' b' - lieBCH s c' d').val ∈ J at he
  rw [hv] at he
  exact he

theorem dualFirstOrderCongruent_constant (I J : LieIdeal ℚ L) {x y : L}
    (hxy : x - y ∈ I) : DualFirstOrderCongruent I J (dualConstantLie x) (dualConstantLie y) := by
  constructor
  · simpa only [map_sub, dualBaseLinear_constant] using hxy
  · simp only [map_sub, dualTangentLinear_constant, sub_self]
    exact J.zero_mem

theorem dualFirstOrderCongruent_infinitesimal (I J : LieIdeal ℚ L) {x y : L}
    (hxy : x - y ∈ J) : DualFirstOrderCongruent I J (dualInfinitesimal x) (dualInfinitesimal y) := by
  constructor
  · simp only [map_sub, dualBaseLinear_infinitesimal, sub_self]
    exact I.zero_mem
  · simpa only [map_sub, dualTangentLinear_infinitesimal] using hxy

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualLogDerivative_sub_mem (I J : LieIdeal ℚ L)
    (hIJ : ∀ x ∈ I, ∀ y ∈ I, ⁅x, y⁆ ∈ J) (z z' : DualGroup hnil)
    (hz : dualTangentLinear z.coord ∈ I) (hz' : dualTangentLinear z'.coord ∈ I)
    (he : DualFirstOrderCongruent I J z.coord z'.coord) :
    dualLogDerivative z - dualLogDerivative z' ∈ J := by
  have hbase : -dualBaseLinear z.coord - -dualBaseLinear z'.coord ∈ I := by
    have hh := I.neg_mem he.1
    rw [map_sub, neg_sub] at hh
    rw [neg_sub_neg]
    exact hh
  have hconst := dualFirstOrderCongruent_constant I J hbase
  rw [map_neg, map_neg] at hconst
  have hc (x : L) : -dualConstantLie x ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (-dualConstantLie x) ∈ I
    rw [map_neg, dualTangentLinear_constant, neg_zero]
    exact I.zero_mem
  have hh := dualFirstOrderCongruent_lieBCH I J hIJ s hz (hc _) hz' (hc _) he hconst
  have ht := hh.2
  rw [map_sub] at ht
  exact ht

theorem dualAdjoint_sub_mem (I J : LieIdeal ℚ L)
    (hIJ : ∀ x ∈ I, ∀ y ∈ I, ⁅x, y⁆ ∈ J)
    (g g' : NilpotentLieBCHGroup L s hnil) (x x' : L)
    (hx : x ∈ I) (hx' : x' ∈ I) (hg : g.coord - g'.coord ∈ I) (hxx' : x - x' ∈ J) :
    dualAdjoint g x - dualAdjoint g' x' ∈ J := by
  have hc (a : L) : dualConstantLie a ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (dualConstantLie a) ∈ I
    rw [dualTangentLinear_constant]
    exact I.zero_mem
  have ht : dualInfinitesimal x ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (dualInfinitesimal x) ∈ I
    rwa [dualTangentLinear_infinitesimal]
  have ht' : dualInfinitesimal x' ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (dualInfinitesimal x') ∈ I
    rwa [dualTangentLinear_infinitesimal]
  have hcc := dualFirstOrderCongruent_constant I J hg
  have htt := dualFirstOrderCongruent_infinitesimal I J hxx'
  have hp := dualFirstOrderCongruent_lieBCH I J hIJ s (hc _) ht (hc _) ht' hcc htt
  have hneg : -g.coord - -g'.coord ∈ I := by
    rw [neg_sub_neg]
    have hh := I.neg_mem hg
    rwa [neg_sub] at hh
  have hcc' := dualFirstOrderCongruent_constant I J hneg
  rw [map_neg, map_neg] at hcc'
  have hh := dualFirstOrderCongruent_lieBCH I J hIJ s
    (lieBCH_mem (dualIdealSubalgebra I) s (hc _) ht) ((dualIdealSubalgebra I).neg_mem (hc _))
    (lieBCH_mem (dualIdealSubalgebra I) s (hc _) ht') ((dualIdealSubalgebra I).neg_mem (hc _)) hp hcc'
  have he := hh.2
  rw [map_sub] at he
  exact he

end NilpotentLieBCHGroup
end Erdos3

namespace Erdos3

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem dual_ext {x y : DualLieAlgebra M}
    (hb : dualBaseLinear x = dualBaseLinear y) (ht : dualTangentLinear x = dualTangentLinear y) : x = y := by
  calc
    x = dualConstantLie (dualBaseLinear x) + dualInfinitesimal (dualTangentLinear x) := dualLie_decomposition x
    _ = dualConstantLie (dualBaseLinear y) + dualInfinitesimal (dualTangentLinear y) := by rw [hb, ht]
    _ = y := (dualLie_decomposition y).symm

noncomputable def dualLinearLift (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M) :
    DualLieAlgebra L →ₗ[ℚ] DualLieAlgebra M :=
  dualConstantLie.toLinearMap.comp (B.toLinearMap.comp dualBaseLinear) +
    dualInfinitesimal.comp (T.comp dualTangentLinear)

@[simp] theorem dualLinearLift_apply (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M) (x : DualLieAlgebra L) :
    dualLinearLift B T x = dualConstantLie (B (dualBaseLinear x)) +
      dualInfinitesimal (T (dualTangentLinear x)) := rfl

@[simp] theorem dualLinearLift_base (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M) (x : DualLieAlgebra L) :
    dualBaseLinear (dualLinearLift B T x) = B (dualBaseLinear x) := by
  rw [dualLinearLift_apply, map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]

@[simp] theorem dualLinearLift_tangent (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M) (x : DualLieAlgebra L) :
    dualTangentLinear (dualLinearLift B T x) = T (dualTangentLinear x) := by
  rw [dualLinearLift_apply, map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add]

@[simp] theorem dualLinearLift_constant (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M) (x : L) :
    dualLinearLift B T (dualConstantLie x) = dualConstantLie (B x) := by
  rw [dualLinearLift_apply, dualBaseLinear_constant, dualTangentLinear_constant, map_zero,
    map_zero, add_zero]

@[simp] theorem dualLinearLift_infinitesimal (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M) (x : L) :
    dualLinearLift B T (dualInfinitesimal x) = dualInfinitesimal (T x) := by
  rw [dualLinearLift_apply, dualBaseLinear_infinitesimal, dualTangentLinear_infinitesimal, map_zero,
    map_zero, zero_add]

variable (I : LieIdeal ℚ L) (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M)
  (hT : ∀ x y, y ∈ I → T ⁅x, y⁆ = ⁅B x, T y⁆)

include hT in
theorem dualIdealMorphism_left {x y : L} (hx : x ∈ I) : T ⁅x, y⁆ = ⁅T x, B y⁆ := by
  calc
    T ⁅x, y⁆ = T (-⁅y, x⁆) := congrArg T (lie_skew x y).symm
    _ = -⁅B y, T x⁆ := by rw [map_neg, hT y x hx]
    _ = ⁅T x, B y⁆ := lie_skew _ _

noncomputable def dualIdealMorphism : dualIdealSubalgebra I →ₗ⁅ℚ⁆ DualLieAlgebra M :=
  { toLinearMap := (dualLinearLift B T).comp (dualIdealSubalgebra I).incl.toLinearMap
    map_lie' := by
      intro x y
      apply dual_ext
      · change dualBaseLinear (dualLinearLift B T ⁅x.val, y.val⁆) =
          dualBaseLinear ⁅dualLinearLift B T x.val, dualLinearLift B T y.val⁆
        rw [dualLinearLift_base, dualBaseLinear_lie, dualBaseLinear_lie,
          dualLinearLift_base, dualLinearLift_base, B.map_lie]
      · change dualTangentLinear (dualLinearLift B T ⁅x.val, y.val⁆) =
          dualTangentLinear ⁅dualLinearLift B T x.val, dualLinearLift B T y.val⁆
        rw [dualLinearLift_tangent, dualTangentLinear_lie, dualTangentLinear_lie,
          dualLinearLift_base, dualLinearLift_base, dualLinearLift_tangent, dualLinearLift_tangent,
          map_add, hT _ _ y.property, dualIdealMorphism_left I B T hT x.property] }

include hT in
theorem dualLinearLift_lieBCH (s : ℕ) {x y : DualLieAlgebra L}
    (hx : x ∈ dualIdealSubalgebra I) (hy : y ∈ dualIdealSubalgebra I) :
    dualLinearLift B T (lieBCH s x y) = lieBCH s (dualLinearLift B T x) (dualLinearLift B T y) := by
  let a : dualIdealSubalgebra I := ⟨x, hx⟩
  let b : dualIdealSubalgebra I := ⟨y, hy⟩
  calc
    _ = dualLinearLift B T ((dualIdealSubalgebra I).incl (lieBCH s a b)) :=
      congrArg (dualLinearLift B T) (map_lieBCH (dualIdealSubalgebra I).incl s a b).symm
    _ = _ := map_lieBCH (dualIdealMorphism I B T hT) s a b

end Erdos3

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

noncomputable instance dualRealModule : Module ℝ (DualLieAlgebra L) :=
  (dualCoordinates (L := L)).toAddEquiv.module ℝ

noncomputable def dualRealCoordinates : DualLieAlgebra L ≃ₗ[ℝ] L × L :=
  (dualCoordinates (L := L)).toAddEquiv.linearEquiv ℝ

@[simp] theorem dualRealCoordinates_apply (x : DualLieAlgebra L) :
    dualRealCoordinates x = (dualBaseLinear x, dualTangentLinear x) := rfl

@[simp] theorem dualRealCoordinates_symm_apply (x : L × L) :
    dualRealCoordinates.symm x = dualConstantLie x.1 + dualInfinitesimal x.2 := rfl

@[simp] theorem dualBaseLinear_smul_real (r : ℝ) (x : DualLieAlgebra L) :
    dualBaseLinear (r • x) = r • dualBaseLinear x :=
  congrArg Prod.fst (dualRealCoordinates.map_smul r x)

@[simp] theorem dualTangentLinear_smul_real (r : ℝ) (x : DualLieAlgebra L) :
    dualTangentLinear (r • x) = r • dualTangentLinear x :=
  congrArg Prod.snd (dualRealCoordinates.map_smul r x)

instance dualRealScalarTower [IsScalarTower ℚ ℝ L] : IsScalarTower ℚ ℝ (DualLieAlgebra L) where
  smul_assoc q r x := by
    apply dualCoordinates.injective
    ext <;> simp [smul_assoc]

noncomputable instance dualRealLieAlgebra : LieAlgebra ℝ (DualLieAlgebra L) where
  lie_smul r x y := by
    apply dualCoordinates.injective
    ext
    · simp only [dualCoordinates_apply, dualBaseLinear_lie, dualBaseLinear_smul_real, lie_smul]
    · simp only [dualCoordinates_apply, dualTangentLinear_lie, dualTangentLinear_smul_real,
        dualBaseLinear_smul_real, lie_smul, smul_add]

end Erdos3

namespace Erdos3.NilpotentLieBCHGroup

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  (hM : LieModule.lowerCentralSeries ℚ M M s = ⊥)
  (I : LieIdeal ℚ L) (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M)
  (hT : ∀ x y, y ∈ I → T ⁅x, y⁆ = ⁅B x, T y⁆)

include hT in
theorem dualLinearLift_logDerivative (z : DualGroup hL)
    (hz : dualTangentLinear z.coord ∈ I) :
    T (dualLogDerivative z) =
      dualLogDerivative (hnil := hM) (⟨dualLinearLift B T z.coord⟩ : DualGroup hM) := by
  have hc : -dualConstantLie (dualBaseLinear z.coord) ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (-dualConstantLie (dualBaseLinear z.coord)) ∈ I
    rw [map_neg, dualTangentLinear_constant, neg_zero]
    exact I.zero_mem
  have hh := dualLinearLift_lieBCH I B T hT s hz hc
  have ht := congrArg dualTangentLinear hh
  rw [dualLinearLift_tangent, map_neg, dualLinearLift_constant] at ht
  change T (dualLogDerivative z) =
    dualTangentLinear (lieBCH s (dualLinearLift B T z.coord)
      (-dualConstantLie (dualBaseLinear (dualLinearLift B T z.coord))))
  rw [dualLinearLift_base]
  exact ht

include hT in
theorem dualLinearLift_adjoint (g : NilpotentLieBCHGroup L s hL) (x : L) (hx : x ∈ I) :
    T (dualAdjoint g x) = dualAdjoint (map (hM := hM) B g) (T x) := by
  have hc : dualConstantLie g.coord ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (dualConstantLie g.coord) ∈ I
    rw [dualTangentLinear_constant]
    exact I.zero_mem
  have ht : dualInfinitesimal x ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (dualInfinitesimal x) ∈ I
    rwa [dualTangentLinear_infinitesimal]
  have hh := dualLinearLift_lieBCH I B T hT s
    (lieBCH_mem (dualIdealSubalgebra I) s hc ht) ((dualIdealSubalgebra I).neg_mem hc)
  rw [dualLinearLift_lieBCH I B T hT s hc ht, dualLinearLift_constant,
    dualLinearLift_infinitesimal, map_neg, dualLinearLift_constant] at hh
  have he := congrArg dualTangentLinear hh
  rw [dualLinearLift_tangent] at he
  exact he

include hT in
theorem dualLinearLift_logDerivative_eq (z : DualGroup hL)
    (hz : dualTangentLinear z.coord ∈ I) (z' : DualGroup hM)
    (he : dualLinearLift B T z.coord = z'.coord) :
    T (dualLogDerivative z) = dualLogDerivative (hnil := hM) z' := by
  have hg : (⟨dualLinearLift B T z.coord⟩ : DualGroup hM) = z' := NilpotentLieBCHGroup.ext he
  exact (dualLinearLift_logDerivative hM I B T hT z hz).trans
    (congrArg (dualLogDerivative (hnil := hM)) hg)

include hT in
theorem dualLinearLift_adjoint_eq (g : NilpotentLieBCHGroup L s hL) (x : L) (hx : x ∈ I)
    (g' : NilpotentLieBCHGroup M s hM) (x' : M)
    (hg : B g.coord = g'.coord) (hxx' : T x = x') :
    T (dualAdjoint g x) = dualAdjoint g' x' := by
  have hmap : map (hM := hM) B g = g' := NilpotentLieBCHGroup.ext hg
  have he := dualLinearLift_adjoint hM I B T hT g x hx
  rw [hmap, hxx'] at he
  exact he

end Erdos3.NilpotentLieBCHGroup

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def dualInvariantSubalgebra (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) : LieSubalgebra ℚ (DualLieAlgebra L) :=
  { U.toSubmodule.comap dualBaseLinear ⊓ V.comap dualTangentLinear with
    lie_mem' := by
      intro x y hx hy
      constructor
      · change dualBaseLinear ⁅x, y⁆ ∈ U
        rw [dualBaseLinear_lie]
        exact U.lie_mem hx.1 hy.1
      · change dualTangentLinear ⁅x, y⁆ ∈ V
        rw [dualTangentLinear_lie]
        apply V.add_mem (hUV _ hx.1 _ hy.2)
        rw [← lie_skew]
        exact V.neg_mem (hUV _ hy.1 _ hx.2) }

@[simp] theorem mem_dualInvariantSubalgebra (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (x : DualLieAlgebra L) :
    x ∈ dualInvariantSubalgebra U V hUV ↔ dualBaseLinear x ∈ U ∧ dualTangentLinear x ∈ V :=
  Iff.rfl

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualAdjoint_mem_of_invariant (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) (x : L) (hx : x ∈ V) :
    dualAdjoint g x ∈ V := by
  let S := dualInvariantSubalgebra U V hUV
  have hc : dualConstantLie g.coord ∈ S := by
    change dualBaseLinear (dualConstantLie g.coord) ∈ U ∧
      dualTangentLinear (dualConstantLie g.coord) ∈ V
    simpa only [dualBaseLinear_constant, dualTangentLinear_constant] using And.intro hg V.zero_mem
  have ht : dualInfinitesimal x ∈ S := by
    change dualBaseLinear (dualInfinitesimal x) ∈ U ∧ dualTangentLinear (dualInfinitesimal x) ∈ V
    simpa only [dualBaseLinear_infinitesimal, dualTangentLinear_infinitesimal] using And.intro U.zero_mem hx
  exact (lieBCH_mem S s (lieBCH_mem S s hc ht) (S.neg_mem hc)).2

theorem dualLogDerivative_mem_of_invariant (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (z : DualGroup hnil)
    (hb : dualBaseLinear z.coord ∈ U) (ht : dualTangentLinear z.coord ∈ V) :
    dualLogDerivative z ∈ V := by
  let S := dualInvariantSubalgebra U V hUV
  have hz : z.coord ∈ S := ⟨hb, ht⟩
  have hc : dualConstantLie (dualBaseLinear z.coord) ∈ S := by
    change dualBaseLinear (dualConstantLie (dualBaseLinear z.coord)) ∈ U ∧
      dualTangentLinear (dualConstantLie (dualBaseLinear z.coord)) ∈ V
    simpa only [dualBaseLinear_constant, dualTangentLinear_constant] using And.intro hb V.zero_mem
  exact (lieBCH_mem S s hz (S.neg_mem hc)).2

end NilpotentLieBCHGroup
end Erdos3

namespace Erdos3

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} (hL : LieModule.lowerCentralSeries ℚ L L s = ⊥)
  (hM : LieModule.lowerCentralSeries ℚ M M t = ⊥)
  (I : LieIdeal ℚ L) (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M)
  (hT : ∀ x y, y ∈ I → T ⁅x, y⁆ = ⁅B x, T y⁆)

include hL hM hT in
theorem dualLinearLift_lieBCH_of_steps {x y : DualLieAlgebra L}
    (hx : x ∈ dualIdealSubalgebra I) (hy : y ∈ dualIdealSubalgebra I) :
    dualLinearLift B T (lieBCH s x y) =
      lieBCH t (dualLinearLift B T x) (dualLinearLift B T y) := by
  let a : dualIdealSubalgebra I := ⟨x, hx⟩
  let b : dualIdealSubalgebra I := ⟨y, hy⟩
  calc
    _ = dualLinearLift B T ((dualIdealSubalgebra I).incl (lieBCH s a b)) :=
      congrArg (dualLinearLift B T) (map_lieBCH (dualIdealSubalgebra I).incl s a b).symm
    _ = _ := map_lieBCH_of_nilpotent_steps (dualIdealMorphism I B T hT)
      (lie_subalgebra_lowerCentralSeries_eq_bot (dualLie_lowerCentralSeries_eq_bot hL)
        (dualIdealSubalgebra I))
      (dualLie_lowerCentralSeries_eq_bot hM) a b

namespace NilpotentLieBCHGroup

include hT in
theorem dualLinearLift_adjoint_of_steps (g : NilpotentLieBCHGroup L s hL)
    (x : L) (hx : x ∈ I) :
    T (dualAdjoint g x) = dualAdjoint (mapOfSteps (hM := hM) B g) (T x) := by
  have hc : dualConstantLie g.coord ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (dualConstantLie g.coord) ∈ I
    rw [dualTangentLinear_constant]
    exact I.zero_mem
  have ht : dualInfinitesimal x ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (dualInfinitesimal x) ∈ I
    rwa [dualTangentLinear_infinitesimal]
  have hh := dualLinearLift_lieBCH_of_steps hL hM I B T hT
    (lieBCH_mem (dualIdealSubalgebra I) s hc ht) ((dualIdealSubalgebra I).neg_mem hc)
  rw [dualLinearLift_lieBCH_of_steps hL hM I B T hT hc ht, dualLinearLift_constant,
    dualLinearLift_infinitesimal, map_neg, dualLinearLift_constant] at hh
  have he := congrArg dualTangentLinear hh
  rw [dualLinearLift_tangent] at he
  exact he

end NilpotentLieBCHGroup
end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DualAdjointFiltration
namespace OAI

namespace Erdos3

namespace NilpotentLieBCHGroup

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

theorem map_dualAdjoint (φ : L →ₗ⁅ℚ⁆ M) (g : NilpotentLieBCHGroup L s hL) (x : L) :
    φ (dualAdjoint g x) = dualAdjoint (map (hM := hM) φ g) (φ x) :=
  dualLinearLift_adjoint hM ⊤ φ φ.toLinearMap (fun a b _ => φ.map_lie a b) g x (by trivial)

theorem dualAdjoint_eq_self_of_lie_eq_zero (g : NilpotentLieBCHGroup L s hL) (x : L)
    (hgx : ⁅g.coord, x⁆ = 0) : dualAdjoint g x = x := by
  have hc : Commute (dualConstantHom g) (dualTangentElement x) := by
    apply commute_of_lie_eq_zero
    change ⁅dualConstantLie g.coord, dualInfinitesimal x⁆ = 0
    rw [dualConstant_infinitesimal_lie, hgx, map_zero]
  apply dualTangentElement_injective (hnil := hL)
  rw [← dualAdjoint_spec, hc.eq, mul_assoc, mul_inv_cancel, mul_one]

theorem dualAdjoint_sub_mem_ideal (I : LieIdeal ℚ L) (g : NilpotentLieBCHGroup L s hL)
    (x : L) (hgx : ⁅g.coord, x⁆ ∈ I) : dualAdjoint g x - x ∈ I := by
  have hz : ⁅(quotientHom I g).coord, lieQuotientMap I x⁆ = 0 := by
    rw [quotientHom_coord, ← LieHom.map_lie]
    exact (lieQuotientMap_eq_zero I _).mpr hgx
  apply (lieQuotientMap_eq_zero I _).mp
  rw [map_sub, map_dualAdjoint (hM := lie_quotient_lowerCentralSeries_eq_bot hL I)]
  exact sub_eq_zero.mpr (dualAdjoint_eq_self_of_lie_eq_zero (quotientHom I g) _ hz)

end NilpotentLieBCHGroup

namespace NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ} (F : NilpotentLieFiltration L s)

theorem dualAdjoint_sub_mem_layer {i j : ℕ} (g : F.Group) (hg : g.coord ∈ F.layer i)
    (x : L) (hx : x ∈ F.layer j) : dualAdjoint g x - x ∈ F.layer (i + j) :=
  dualAdjoint_sub_mem_ideal (F.layerIdeal (i + j)) g x (F.lie_mem hg hx)

theorem dualAdjoint_sub_mem_next_layer (j : ℕ) (g : F.Group) (x : L) (hx : x ∈ F.layer j) :
    dualAdjoint g x - x ∈ F.layer (j + 1) := by
  have hg : g.coord ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  simpa only [Nat.add_comm 1 j] using F.dualAdjoint_sub_mem_layer g hg x hx

end NilpotentLieFiltration
end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FilteredAdjointFirstBracket
namespace OAI

section

namespace Erdos3

namespace NilpotentAlgebraFiltration

variable {A : Type*} [Ring A] [Algebra ℚ A] (F : NilpotentAlgebraFiltration A 2)

theorem mul_eq_zero_of_degrees {i j : ℕ} {a b : A}
    (ha : a ∈ F.layer i) (hb : b ∈ F.layer j) (hij : 3 ≤ i + j) : a * b = 0 := by
  have h := F.antitone hij (F.mul_mem ha hb)
  simpa only [F.terminal, Submodule.mem_bot] using h

theorem exp_eq_quadratic {a : A} (ha : a ∈ F.layer 1) :
    IsNilpotent.exp a = 1 + a + (1 / 2 : ℚ) • a ^ 2 := by
  rw [IsNilpotent.exp_eq_sum (F.pow_eq_zero le_rfl ha)]
  norm_num [Finset.sum_range_succ]

theorem nilpotentBCH_eq_quadratic {a b : A} (ha : a ∈ F.layer 1)
    (hb : b ∈ F.layer 1) :
    nilpotentBCH a b = a + b + (1 / 2 : ℚ) • (a * b - b * a) := by
  have ha2 : a ^ 2 ∈ F.layer 2 := by simpa using F.pow_mem ha 2
  have hb2 : b ^ 2 ∈ F.layer 2 := by simpa using F.pow_mem hb 2
  have hab2 := F.mul_eq_zero_of_degrees ha hb2 (by decide)
  have ha2b := F.mul_eq_zero_of_degrees ha2 hb (by decide)
  have ha2b2 := F.mul_eq_zero_of_degrees ha2 hb2 (by decide)
  let q := (1 / 2 : ℚ) • a ^ 2 + a * b + (1 / 2 : ℚ) • b ^ 2
  have hq : q ∈ F.layer 2 :=
    (F.layer 2).add_mem ((F.layer 2).add_mem ((F.layer 2).smul_mem _ ha2)
      (F.mul_mem ha hb)) ((F.layer 2).smul_mem _ hb2)
  have hab : a + b ∈ F.layer 1 := (F.layer 1).add_mem ha hb
  have hp : IsNilpotent.exp a * IsNilpotent.exp b - 1 = a + b + q := by
    rw [F.exp_eq_quadratic ha, F.exp_eq_quadratic hb]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
      hab2, ha2b, ha2b2, smul_zero]
    dsimp [q]
    module
  have hq1 : q ∈ F.layer 1 := F.antitone (by decide) hq
  have hp2 : (a + b + q) ^ 2 = (a + b) ^ 2 := by
    rw [pow_two, add_mul (a + b) q (a + b + q),
      mul_add (a + b) (a + b) q, mul_add q (a + b) q,
      F.mul_eq_zero_of_degrees hab hq (by decide),
      F.mul_eq_zero_of_degrees hq hab (by decide),
      F.mul_eq_zero_of_degrees hq hq (by decide)]
    simp only [add_zero, pow_two]
  rw [nilpotentBCH, hp,
    nilpotentLog_eq_sum (F.pow_eq_zero le_rfl ((F.layer 1).add_mem hab hq1))]
  norm_num [Finset.sum_range_succ, hp2]
  dsimp [q]
  simp only [pow_two, add_mul, mul_add, smul_add, smul_sub]
  module

end NilpotentAlgebraFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
attribute [local instance] LieRing.ofAssociativeRing

theorem lieBCH_eq_quadratic_of_step_two {s : ℕ} (hs : 2 ≤ s)
    (hnil : LieModule.lowerCentralSeries ℚ L L 2 = ⊥) (a b : L) :
    lieBCH s a b = a + b + (1 / 2 : ℚ) • ⁅a, b⁆ := by
  let x : Fin 2 → FreeLieAlgebra ℚ (Fin 2) := FreeLieAlgebra.of ℚ
  let F := truncatedSeriesFiltration (A := FreeAlgebra ℚ (Fin 2)) 2
  have hx (i : Fin 2) : scaledFreeGenerator 2 i ∈ F.layer 1 :=
    scaledFreeGenerator_mem_layer 2 i
  have h : scaledFreeLieEval 2 (lieBCH s (x 0) (x 1)) =
      scaledFreeLieEval 2 (x 0 + x 1 + (1 / 2 : ℚ) • ⁅x 0, x 1⁆) := by
    simp only [map_lieBCH, map_add, map_smul, LieHom.map_lie, x, scaledFreeLieEval_of]
    rw [(F.extend hs).lieBCH_eq (hx 0) (hx 1)]
    exact F.nilpotentBCH_eq_quadratic (hx 0) (hx 1)
  have he := lie_lift_eq_of_scaledFreeLieEval_eq ![a, b] hnil h
  simpa only [map_lieBCH, map_add, map_smul, LieHom.map_lie, x,
    FreeLieAlgebra.lift_of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using he

end Erdos3

end

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

def centralPairSpan (a b : L) : Submodule ℚ L :=
  Submodule.span ℚ {a, b, ⁅a, b⁆}

theorem centralPairSpan_lie_mem (a b : L) (ha : ⁅a, ⁅a, b⁆⁆ = 0)
    (hb : ⁅b, ⁅a, b⁆⁆ = 0) {x y : L}
    (hx : x ∈ centralPairSpan a b) (hy : y ∈ centralPairSpan a b) :
    ⁅x, y⁆ ∈ Submodule.span ℚ {⁅a, b⁆} := by
  let W := Submodule.span ℚ {⁅a, b⁆}
  have hc : ⁅a, b⁆ ∈ W := Submodule.subset_span (by simp)
  have hba : ⁅b, a⁆ = -⁅a, b⁆ := (lie_skew b a).symm
  have hca : ⁅⁅a, b⁆, a⁆ = 0 := by rw [← lie_skew ⁅a, b⁆ a, ha, neg_zero]
  have hcb : ⁅⁅a, b⁆, b⁆ = 0 := by rw [← lie_skew ⁅a, b⁆ b, hb, neg_zero]
  change x ∈ Submodule.span ℚ {a, b, ⁅a, b⁆} at hx
  change y ∈ Submodule.span ℚ {a, b, ⁅a, b⁆} at hy
  change ⁅x, y⁆ ∈ W
  induction hx using Submodule.span_induction generalizing y with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        try simp only [lie_self, ha, hb, hba, hca, hcb]
      all_goals first | exact W.zero_mem | exact hc | exact W.neg_mem hc
    | zero => simpa only [lie_zero] using W.zero_mem
    | add y z _ _ hy hz => simpa only [lie_add] using W.add_mem hy hz
    | smul r y _ hy => simpa only [lie_smul] using W.smul_mem r hy
  | zero => simpa only [zero_lie] using W.zero_mem
  | add x z _ _ hx hz => simpa only [add_lie] using W.add_mem (hx hy) (hz hy)
  | smul r x _ hx => simpa only [smul_lie] using W.smul_mem r (hx hy)

theorem centralPairSpan_lie_eq_zero (a b : L) (ha : ⁅a, ⁅a, b⁆⁆ = 0)
    (hb : ⁅b, ⁅a, b⁆⁆ = 0) {x y : L}
    (hx : x ∈ centralPairSpan a b) (hy : y ∈ Submodule.span ℚ {⁅a, b⁆}) :
    ⁅x, y⁆ = 0 := by
  have hc : ⁅x, ⁅a, b⁆⁆ = 0 := by
    change x ∈ Submodule.span ℚ {a, b, ⁅a, b⁆} at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact lie_self _
    | zero => exact zero_lie _
    | add x y _ _ hx hy => rw [add_lie, hx, hy, add_zero]
    | smul r x _ hx => rw [smul_lie, hx, smul_zero]
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [lie_smul, hc, smul_zero]

def centralPairSubalgebra (a b : L) (ha : ⁅a, ⁅a, b⁆⁆ = 0)
    (hb : ⁅b, ⁅a, b⁆⁆ = 0) : LieSubalgebra ℚ L :=
  { centralPairSpan a b with
    lie_mem' := fun hx hy =>
      (Submodule.span_mono (by simp)) (centralPairSpan_lie_mem a b ha hb hx hy) }

theorem centralPairSubalgebra_step_two (a b : L) (ha : ⁅a, ⁅a, b⁆⁆ = 0)
    (hb : ⁅b, ⁅a, b⁆⁆ = 0) :
    let K := centralPairSubalgebra a b ha hb
    LieModule.lowerCentralSeries ℚ K K 2 = ⊥ := by
  intro K
  have hcenter : LieModule.lowerCentralSeries ℚ K K 1 ≤ LieAlgebra.center ℚ K := by
    rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lie_le_iff]
    intro x _ y _
    rw [LieModule.mem_maxTrivSubmodule]
    intro z
    apply Subtype.ext
    exact centralPairSpan_lie_eq_zero a b ha hb z.property
      (centralPairSpan_lie_mem a b ha hb x.property y.property)
  apply bot_unique
  rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lie_le_iff]
  intro x _ y hy
  exact (LieSubmodule.mem_bot _).mpr ((hcenter hy) x)

theorem lieBCH_eq_quadratic_of_central_commutator {s : ℕ} (hs : 2 ≤ s)
    (a b : L) (ha : ⁅a, ⁅a, b⁆⁆ = 0) (hb : ⁅b, ⁅a, b⁆⁆ = 0) :
    lieBCH s a b = a + b + (1 / 2 : ℚ) • ⁅a, b⁆ := by
  let K := centralPairSubalgebra a b ha hb
  have haK : a ∈ K := Submodule.subset_span (by simp)
  have hbK : b ∈ K := Submodule.subset_span (by simp)
  have h := congrArg K.incl (lieBCH_eq_quadratic_of_step_two hs
    (centralPairSubalgebra_step_two a b ha hb) (⟨a, haK⟩ : K) (⟨b, hbK⟩ : K))
  simp only [map_lieBCH, map_add, map_smul, LieHom.map_lie] at h
  exact h

theorem lieBCH_conjugation_of_central_commutator {s : ℕ} (hs : 2 ≤ s)
    (a b : L) (ha : ⁅a, ⁅a, b⁆⁆ = 0) (hb : ⁅b, ⁅a, b⁆⁆ = 0) :
    lieBCH s (lieBCH s a b) (-a) = b + ⁅a, b⁆ := by
  have hba : ⁅b, a⁆ = -⁅a, b⁆ := (lie_skew b a).symm
  have hca : ⁅⁅a, b⁆, a⁆ = 0 := by rw [← lie_skew ⁅a, b⁆ a, ha, neg_zero]
  have hc : ⁅a + b + (1 / 2 : ℚ) • ⁅a, b⁆, -a⁆ = ⁅a, b⁆ := by
    simp only [add_lie, lie_neg, lie_self, smul_lie, hca,
      smul_zero, hba, neg_neg, zero_add, add_zero]
  have hu : ⁅a + b + (1 / 2 : ℚ) • ⁅a, b⁆, ⁅a, b⁆⁆ = 0 := by
    simp only [add_lie, ha, hb, smul_lie, lie_self, smul_zero, add_zero]
  rw [lieBCH_eq_quadratic_of_central_commutator hs a b ha hb,
    lieBCH_eq_quadratic_of_central_commutator hs _ _
      (by rw [hc, hu]) (by rw [hc, neg_lie, ha, neg_zero]), hc]
  module

theorem lieBCH_conjugation_sub_mem {s : ℕ} (hs : 2 ≤ s) (I : LieIdeal ℚ L)
    (a b : L) (ha : ⁅a, ⁅a, b⁆⁆ ∈ I) (hb : ⁅b, ⁅a, b⁆⁆ ∈ I) :
    lieBCH s (lieBCH s a b) (-a) - (b + ⁅a, b⁆) ∈ I := by
  apply (lieQuotientMap_eq_zero I _).mp
  rw [map_sub, map_add, map_lieBCH, map_lieBCH, map_neg, LieHom.map_lie]
  apply sub_eq_zero.mpr
  apply lieBCH_conjugation_of_central_commutator hs
  · rw [← LieHom.map_lie, ← LieHom.map_lie]
    exact (lieQuotientMap_eq_zero I _).mpr ha
  · rw [← LieHom.map_lie, ← LieHom.map_lie]
    exact (lieQuotientMap_eq_zero I _).mpr hb

end Erdos3

end

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def dualBaseSubalgebra (U : LieSubalgebra ℚ L) :
    LieSubalgebra ℚ (DualLieAlgebra L) :=
  dualInvariantSubalgebra U ⊤ (fun _ _ _ _ => trivial)

noncomputable def dualInvariantTangentIdeal (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) : LieIdeal ℚ (dualBaseSubalgebra U) :=
  { (dualBaseLinear.comp (dualBaseSubalgebra U).incl.toLinearMap).ker ⊓
      V.comap (dualTangentLinear.comp (dualBaseSubalgebra U).incl.toLinearMap) with
    lie_mem := by
      intro x y hy
      change dualBaseLinear ⁅x.val, y.val⁆ = 0 ∧ dualTangentLinear ⁅x.val, y.val⁆ ∈ V
      change dualBaseLinear y.val = 0 ∧ dualTangentLinear y.val ∈ V at hy
      simp only [dualBaseLinear_lie, dualTangentLinear_lie, hy.1, lie_zero, add_zero]
      exact ⟨trivial, hUV _ x.property.1 _ hy.2⟩ }

@[simp] theorem mem_dualInvariantTangentIdeal (U : LieSubalgebra ℚ L)
    (V : Submodule ℚ L) (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (z : dualBaseSubalgebra U) :
    z ∈ dualInvariantTangentIdeal U V hUV ↔
      dualBaseLinear z.val = 0 ∧ dualTangentLinear z.val ∈ V := Iff.rfl

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualAdjoint_eq_add_lie (hs : 2 ≤ s)
    (g : NilpotentLieBCHGroup L s hnil) (x : L) (hgx : ⁅g.coord, ⁅g.coord, x⁆⁆ = 0) :
    dualAdjoint g x = x + ⁅g.coord, x⁆ := by
  change dualTangentLinear
    (lieBCH s (lieBCH s (dualConstantLie g.coord) (dualInfinitesimal x))
      (-dualConstantLie g.coord)) = _
  rw [lieBCH_conjugation_of_central_commutator hs _ _
    (by rw [dualConstant_infinitesimal_lie, dualConstant_infinitesimal_lie, hgx, map_zero])
    (by rw [dualConstant_infinitesimal_lie, dualInfinitesimal_lie]),
    dualConstant_infinitesimal_lie, map_add, dualTangentLinear_infinitesimal,
    dualTangentLinear_infinitesimal]

theorem dualAdjoint_sub_first_bracket_mem (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) (x : L)
    (hgx : ⁅g.coord, ⁅g.coord, x⁆⁆ ∈ V) :
    dualAdjoint g x - (x + ⁅g.coord, x⁆) ∈ V := by
  let S := dualBaseSubalgebra U
  let I := dualInvariantTangentIdeal U V hUV
  let a : S := ⟨dualConstantLie g.coord, by
    change dualBaseLinear (dualConstantLie g.coord) ∈ U ∧ _
    exact ⟨by simpa only [dualBaseLinear_constant] using hg, by trivial⟩⟩
  let b : S := ⟨dualInfinitesimal x, by
    change dualBaseLinear (dualInfinitesimal x) ∈ U ∧ _
    exact ⟨by simpa only [dualBaseLinear_infinitesimal] using U.zero_mem, by trivial⟩⟩
  have ha : ⁅a, ⁅a, b⁆⁆ ∈ I := by
    change dualBaseLinear ⁅dualConstantLie g.coord,
        ⁅dualConstantLie g.coord, dualInfinitesimal x⁆⁆ = 0 ∧
      dualTangentLinear ⁅dualConstantLie g.coord,
        ⁅dualConstantLie g.coord, dualInfinitesimal x⁆⁆ ∈ V
    rw [dualConstant_infinitesimal_lie, dualConstant_infinitesimal_lie,
      dualBaseLinear_infinitesimal, dualTangentLinear_infinitesimal]
    exact ⟨rfl, hgx⟩
  have hb : ⁅b, ⁅a, b⁆⁆ ∈ I := by
    have he : ⁅b, ⁅a, b⁆⁆ = 0 := by
      apply Subtype.ext
      change ⁅dualInfinitesimal x, ⁅dualConstantLie g.coord, dualInfinitesimal x⁆⁆ = 0
      rw [dualConstant_infinitesimal_lie, dualInfinitesimal_lie]
    rw [he]
    exact I.zero_mem
  have h := (lieBCH_conjugation_sub_mem hs I a b ha hb).2
  change dualTangentLinear (S.incl
    (lieBCH s (lieBCH s a b) (-a) - (b + ⁅a, b⁆))) ∈ V at h
  simp only [map_sub, map_add, map_lieBCH, map_neg, LieHom.map_lie] at h
  change dualTangentLinear
      (lieBCH s (lieBCH s (dualConstantLie g.coord) (dualInfinitesimal x))
        (-dualConstantLie g.coord)) -
    (dualTangentLinear (dualInfinitesimal x) +
      dualTangentLinear ⁅dualConstantLie g.coord, dualInfinitesimal x⁆) ∈ V at h
  simp only [dualConstant_infinitesimal_lie, dualTangentLinear_infinitesimal] at h
  exact h

theorem dualAdjoint_current_bracket_relation (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) (r k p : L)
    (hr : ⁅g.coord, r - k⁆ ∈ V) (hp : ⁅g.coord - p, k⁆ ∈ V)
    (hk : ⁅g.coord, ⁅g.coord, k⁆⁆ ∈ V) :
    ⁅p, k⁆ - (dualAdjoint g r - r) ∈ V := by
  have hdouble : ⁅g.coord, ⁅g.coord, r⁆⁆ ∈ V := by
    have h := V.add_mem (hUV _ hg _ hr) hk
    simp only [lie_sub] at h
    simpa only [sub_add_cancel] using h
  have hmain := dualAdjoint_sub_first_bracket_mem hs U V hUV g hg r hdouble
  have hdelta : ⁅g.coord, r⁆ - ⁅p, k⁆ ∈ V := by
    have h := V.add_mem hr hp
    simp only [lie_sub, sub_lie] at h
    convert h using 1; abel
  convert V.neg_mem (V.add_mem hmain hdelta) using 1; abel

end NilpotentLieBCHGroup

namespace NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {s : ℕ} (F : NilpotentLieFiltration L s)

theorem dualAdjoint_sub_first_bracket_mem_layer (hs : 2 ≤ s) {i j : ℕ}
    (g : F.Group) (hg : g.coord ∈ F.layer i) (x : L) (hx : x ∈ F.layer j) :
    dualAdjoint g x - (x + ⁅g.coord, x⁆) ∈ F.layer (2 * i + j) := by
  apply dualAdjoint_sub_first_bracket_mem hs ⊤ (F.layerIdeal (2 * i + j)).toSubmodule
    (fun _ _ _ hv => (F.layerIdeal _).lie_mem hv) g (by trivial) x
  change ⁅g.coord, ⁅g.coord, x⁆⁆ ∈ F.layer (2 * i + j)
  simpa only [two_mul, Nat.add_assoc] using F.lie_mem hg (F.lie_mem hg hx)

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def polynomialDualEval : VectorPolynomial Unit ℚ L →ₗ⁅ℚ⁆ DualLieAlgebra L where
  toLinearMap := (MvPolynomial.aeval (fun _ : Unit => (DualNumber.eps : DualNumber ℚ))).toLinearMap.rTensor L
  map_lie' {p q} := by
    let e : VectorPolynomial Unit ℚ L →ₗ[ℚ] DualLieAlgebra L :=
      (MvPolynomial.aeval (fun _ : Unit => (DualNumber.eps : DualNumber ℚ))).toLinearMap.rTensor L
    change e ⁅p, q⁆ = ⁅e p, e q⁆
    induction p using TensorProduct.induction_on with
    | zero => refine (congrArg _ (zero_lie (L := VectorPolynomial Unit ℚ L) (M := VectorPolynomial Unit ℚ L) _)).trans ?_; first | (simp; done) | (rw [map_zero]; exact (zero_lie (L := DualLieAlgebra L) (M := DualLieAlgebra L) _).symm) | exact (zero_lie (L := DualLieAlgebra L) (M := DualLieAlgebra L) _).symm
    | tmul a x =>
      induction q using TensorProduct.induction_on with
      | zero => refine (congrArg _ (lie_zero (L := VectorPolynomial Unit ℚ L) (M := VectorPolynomial Unit ℚ L) _)).trans ?_; first | (simp; done) | (rw [map_zero]; exact (lie_zero (L := DualLieAlgebra L) (M := DualLieAlgebra L) _).symm) | exact (lie_zero (L := DualLieAlgebra L) (M := DualLieAlgebra L) _).symm
      | tmul b y =>
        simp only [e, LieAlgebra.ExtendScalars.bracket_tmul, LinearMap.rTensor_tmul,
          AlgHom.toLinearMap_apply, map_mul]
      | add q q' hq hq' =>
        simp only [LieRing.lie_add, map_add, hq, hq']
        exact (LieRing.lie_add (e (a ⊗ₜ[ℚ] x)) (e q) (e q')).symm
    | add p p' hp hp' =>
      simp only [LieRing.add_lie, map_add, hp, hp']
      exact (LieRing.add_lie (e p) (e p') (e q)).symm

theorem polynomialDualEval_constant (x : L) :
    polynomialDualEval (monomial (0 : Unit →₀ ℕ) x) = dualConstantLie x := by
  change MvPolynomial.aeval (fun _ : Unit => (DualNumber.eps : DualNumber ℚ))
    (1 : MvPolynomial Unit ℚ) ⊗ₜ[ℚ] x = _
  rw [map_one]
  rfl

theorem polynomialDualEval_linear (x : L) :
    polynomialDualEval (monomial (Finsupp.single () 1) x) = dualInfinitesimal x := by
  change MvPolynomial.aeval (fun _ : Unit => (DualNumber.eps : DualNumber ℚ))
    (MvPolynomial.X ()) ⊗ₜ[ℚ] x = _
  rw [MvPolynomial.aeval_X]
  rfl

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem conjugation_polynomial (g : NilpotentLieBCHGroup L s hnil) (x : L) :
    lieBCH s (lieBCH s (monomial (R := ℚ) (0 : Unit →₀ ℕ) g.coord)
      (monomial (Finsupp.single () 1) x)) (-monomial 0 g.coord) =
        monomial (Finsupp.single () 1) (conjugationCoord g x) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval_zero
  intro a
  simp only [map_sub, eval_lieBCH, map_neg, eval_monomial,
    Finsupp.prod_zero_index, one_smul, Finsupp.prod_single_index, pow_zero, pow_one]
  exact sub_eq_zero.mpr (conjugationCoord_rat_smul g (a ()) x)

theorem dualAdjoint_eq_conjugationCoord (g : NilpotentLieBCHGroup L s hnil) (x : L) :
    dualAdjoint g x = conjugationCoord g x := by
  have he := congrArg (polynomialDualEval (L := L)) (conjugation_polynomial g x)
  rw [map_lieBCH, map_lieBCH, map_neg, polynomialDualEval_constant,
    polynomialDualEval_linear, polynomialDualEval_linear] at he
  have ht := congrArg (dualTangentLinear (L := L)) he
  exact ht.trans (dualTangentLinear_infinitesimal _)

theorem conjugationCoord_eq_add_lie (hs : 2 ≤ s)
    (g : NilpotentLieBCHGroup L s hnil) (x : L) (hx : ⁅g.coord, ⁅g.coord, x⁆⁆ = 0) :
    conjugationCoord g x = x + ⁅g.coord, x⁆ := by
  rw [← dualAdjoint_eq_conjugationCoord]
  exact dualAdjoint_eq_add_lie hs g x hx

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)
  (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
  (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)

include hUV

theorem invariant_sup_layer (j : ℕ) :
    ∀ u ∈ U, ∀ v ∈ V ⊔ F.layer j, ⁅u, v⁆ ∈ V ⊔ F.layer j := by
  intro u hu v hv
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  rw [lie_add]
  exact (V ⊔ F.layer j).add_mem (Submodule.mem_sup_left (hUV _ hu _ hx))
    (Submodule.mem_sup_right ((F.layerIdeal j).lie_mem hy))

theorem lie_mem_invariant_sup_next_layer (j : ℕ) {u v : L} (hu : u ∈ U)
    (hv : v ∈ V ⊔ F.layer j) : ⁅u, v⁆ ∈ V ⊔ F.layer (j + 1) := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  rw [lie_add]
  apply (V ⊔ F.layer (j + 1)).add_mem (Submodule.mem_sup_left (hUV _ hu _ hx))
  apply Submodule.mem_sup_right
  have hu1 : u ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  simpa only [Nat.add_comm 1 j] using F.lie_mem hu1 hy

theorem adjoint_current_layer_relation (hs : 2 ≤ s) {j : ℕ} (hj : 1 ≤ j)
    (g : F.Group) (hg : g.coord ∈ U) (r k p : L)
    (hp : p ∈ F.layer (j - 1)) (hk : k ∈ F.layer 1)
    (hr : r - k ∈ V ⊔ F.layer j)
    (hlower : ⁅g.coord - p, k⁆ ∈ V ⊔ F.layer (j + 1)) :
    ⁅p, k⁆ - (dualAdjoint g r - r) ∈ V ⊔ F.layer (j + 1) := by
  have hW := F.invariant_sup_layer U V hUV (j + 1)
  apply dualAdjoint_current_bracket_relation hs U (V ⊔ F.layer (j + 1)) hW g hg r k p
    (F.lie_mem_invariant_sup_next_layer U V hUV j hg hr) hlower
  have hpk : ⁅p, k⁆ ∈ F.layer j := by
    simpa only [Nat.sub_add_cancel hj] using F.lie_mem hp hk
  have hg1 : g.coord ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have hhigh : ⁅g.coord, ⁅p, k⁆⁆ ∈ F.layer (j + 1) := by
    simpa only [Nat.add_comm 1 j] using F.lie_mem hg1 hpk
  have h := (V ⊔ F.layer (j + 1)).add_mem (hW _ hg _ hlower) (Submodule.mem_sup_right hhigh)
  simpa only [sub_lie, lie_sub, sub_add_cancel] using h

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DualDerivativeRemoval
namespace OAI

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualLogDerivative_sub_tangent_mem (hs : 1 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (z : DualGroup hnil) (hb : dualBaseLinear z.coord ∈ U)
    (hbr : ⁅dualBaseLinear z.coord, dualTangentLinear z.coord⁆ ∈ V) :
    dualLogDerivative z - dualTangentLinear z.coord ∈ V := by
  let S := dualBaseSubalgebra U
  let I := dualInvariantTangentIdeal U V hUV
  let a : S := ⟨z.coord, ⟨hb, by trivial⟩⟩
  let b : S := ⟨-dualConstantLie (dualBaseLinear z.coord), by
    change dualBaseLinear (-dualConstantLie (dualBaseLinear z.coord)) ∈ U ∧ _
    constructor
    · rw [map_neg, dualBaseLinear_constant]
      exact U.neg_mem hb
    · trivial⟩
  have hab : ⁅a, b⁆ ∈ I := by
    change dualBaseLinear ⁅z.coord, -dualConstantLie (dualBaseLinear z.coord)⁆ = 0 ∧
      dualTangentLinear ⁅z.coord, -dualConstantLie (dualBaseLinear z.coord)⁆ ∈ V
    simp only [dualBaseLinear_lie, dualTangentLinear_lie, map_neg,
      dualBaseLinear_constant, dualTangentLinear_constant, neg_zero, lie_zero,
      zero_add, lie_neg, lie_self]
    rw [lie_skew]
    exact ⟨trivial, hbr⟩
  have he : lieBCH s a b - (a + b) ∈ I := by
    apply (lieQuotientMap_eq_zero I _).mp
    rw [map_sub, map_add, map_lieBCH]
    have hzero : ⁅lieQuotientMap I a, lieQuotientMap I b⁆ = 0 := by
      rw [← LieHom.map_lie]
      exact (lieQuotientMap_eq_zero I _).mpr hab
    rw [lieBCH_eq_add_of_lie_eq_zero_pos hs hzero, sub_self]
  have h := he.2
  change dualTangentLinear (S.incl (lieBCH s a b - (a + b))) ∈ V at h
  simp only [map_sub, map_add, map_lieBCH] at h
  change dualTangentLinear
      (lieBCH s z.coord (-dualConstantLie (dualBaseLinear z.coord))) -
    (dualTangentLinear z.coord +
      dualTangentLinear (-dualConstantLie (dualBaseLinear z.coord))) ∈ V at h
  simp only [map_neg, dualTangentLinear_constant, neg_zero, add_zero] at h
  exact h

end NilpotentLieBCHGroup

namespace NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {s : ℕ} (F : NilpotentLieFiltration L s)

theorem dualLogDerivative_sub_tangent_mem_layer (hs : 1 ≤ s) {i j : ℕ}
    (z : DualGroup F.lowerCentralSeries_eq_bot)
    (hb : dualBaseLinear z.coord ∈ F.layer i)
    (ht : dualTangentLinear z.coord ∈ F.layer j) :
    dualLogDerivative z - dualTangentLinear z.coord ∈ F.layer (i + j) := by
  exact dualLogDerivative_sub_tangent_mem hs ⊤ (F.layerIdeal (i + j)).toSubmodule
    (fun _ _ _ hv => (F.layerIdeal _).lie_mem hv) z (by trivial) (F.lie_mem hb ht)

theorem logDerivative_current_layer_relation (hs : 1 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (j : ℕ)
    (z : DualGroup F.lowerCentralSeries_eq_bot) (hb : dualBaseLinear z.coord ∈ U)
    (hbr : ⁅dualBaseLinear z.coord, dualTangentLinear z.coord⁆ ∈ V ⊔ F.layer (j + 1)) :
    dualLogDerivative z - dualTangentLinear z.coord ∈ V ⊔ F.layer (j + 1) :=
  dualLogDerivative_sub_tangent_mem hs U (V ⊔ F.layer (j + 1))
    (F.invariant_sup_layer U V hUV (j + 1)) z hb hbr

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3

namespace NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

@[simp] theorem dualLogDerivative_one : dualLogDerivative (1 : DualGroup hnil) = 0 := by
  simp only [dualLogDerivative, map_one, inv_one, mul_one, coord_one, map_zero]

theorem dualLogDerivative_inv (z : DualGroup hnil) :
    dualLogDerivative z⁻¹ = -dualAdjoint (dualBaseHom z)⁻¹ (dualLogDerivative z) := by
  have h := dualLogDerivative_mul z z⁻¹
  rw [mul_inv_cancel, dualLogDerivative_one] at h
  have he := congrArg (dualAdjoint (dualBaseHom z)⁻¹) h
  rw [dualAdjoint_zero, dualAdjoint_add, dualAdjoint_inv_cancel] at he
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [add_comm] using he.symm

theorem dualLogDerivative_remove (a z c : DualGroup hnil) :
    dualLogDerivative (a⁻¹ * z * c⁻¹) =
      dualAdjoint (dualBaseHom a)⁻¹ (dualLogDerivative z - dualLogDerivative a) -
        dualAdjoint (dualBaseHom (a⁻¹ * z * c⁻¹)) (dualLogDerivative c) := by
  simp only [dualLogDerivative_mul, dualLogDerivative_inv, map_mul, map_inv,
    dualAdjoint_mul, dualAdjoint_neg, dualAdjoint_sub]
  abel

end NilpotentLieBCHGroup

namespace NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

end NilpotentLieFiltration
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedFlagBasis
namespace OAI

section

namespace Erdos3

open Module

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

theorem span_image_inl_of_basis_extension
    {P R : Submodule K V} (hRP : R ≤ P) {κ μ : Type*}
    (bP : Basis κ K P) (bV : Basis (κ ⊕ μ) K V)
    (hext : ∀ i, bV (Sum.inl i) = (bP i : V)) (s : Set κ)
    (hspan : R.comap P.subtype = Submodule.span K (bP '' s)) :
    R = Submodule.span K (bV '' (Sum.inl '' s)) := by
  have himage : P.subtype '' (bP '' s) = bV '' (Sum.inl '' s) := by
    ext x
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨Sum.inl i, ⟨i, hi, rfl⟩, hext i⟩
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨bP i, ⟨i, hi, rfl⟩, (hext i).symm⟩
  calc
    R = (R.comap P.subtype).map P.subtype :=
      (Submodule.map_comap_eq_self (by
        simpa [Submodule.range_subtype] using hRP)).symm
    _ = (Submodule.span K (bP '' s)).map P.subtype := by rw [hspan]
    _ = Submodule.span K (P.subtype '' (bP '' s)) := by rw [Submodule.map_span]
    _ = Submodule.span K (bV '' (Sum.inl '' s)) := by rw [himage]

theorem span_range_inl_complement_basis {P Q : Submodule K V} (hPQ : IsCompl P Q)
    {κ μ : Type*} (bP : Basis κ K P) (bQ : Basis μ K Q) :
    let bV := (bP.prod bQ).map (P.prodEquivOfIsCompl Q hPQ)
    P = Submodule.span K (bV '' Set.range Sum.inl) := by
  classical
  let bV := (bP.prod bQ).map (P.prodEquivOfIsCompl Q hPQ)
  apply le_antisymm
  · intro x hx
    have hxp : (⟨x, hx⟩ : P) ∈ Submodule.span K (Set.range bP) := by
      rw [bP.span_eq]
      exact Submodule.mem_top
    exact Submodule.span_induction (R := K) (s := Set.range bP)
      (p := fun y _ => (y : V) ∈ Submodule.span K (bV '' Set.range Sum.inl))
      (fun y hy => by
        obtain ⟨i, rfl⟩ := hy
        apply Submodule.subset_span
        refine ⟨Sum.inl i, ⟨i, rfl⟩, ?_⟩
        simp [bV])
      (Submodule.zero_mem _)
      (fun _ _ _ _ hy hz => Submodule.add_mem _ hy hz)
      (fun a _ _ hy => Submodule.smul_mem _ a hy) hxp
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simp

theorem exists_basis_with_nested_supports (n : ℕ) :
    ∀ {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (P : Fin n → Submodule K V), Antitone P →
      ∃ (κ : Type) (_ : Fintype κ) (b : Basis κ K V) (s : Fin n → Set κ),
        Antitone s ∧ ∀ i, P i = Submodule.span K (b '' s i) := by
  induction n with
  | zero =>
      intro V _ _ _ P _
      refine ⟨Fin (finrank K V), inferInstance, finBasis K V, Fin.elim0, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ n ih =>
      intro V _ _ _ P hanti
      classical
      let P₀ : Submodule K V := P 0
      let tail : Fin n → Submodule K P₀ := fun i => (P i.succ).comap P₀.subtype
      have htail : Antitone tail := by
        intro i j hij
        apply Submodule.comap_mono
        exact hanti (by simpa using hij)
      obtain ⟨κ, instκ, bP, sP, hsP, hbP⟩ := ih tail htail
      let : Fintype κ := instκ
      obtain ⟨Q, hPQ⟩ := Submodule.exists_isCompl P₀
      let bQ := finBasis K Q
      let e : (P₀ × Q) ≃ₗ[K] V := P₀.prodEquivOfIsCompl Q hPQ
      let b : Basis (κ ⊕ Fin (finrank K Q)) K V := (bP.prod bQ).map e
      let s : Fin (n + 1) → Set (κ ⊕ Fin (finrank K Q)) :=
        Fin.cases (Set.range Sum.inl) (fun j => Sum.inl '' sP j)
      refine ⟨κ ⊕ Fin (finrank K Q), inferInstance, b, s, ?_, ?_⟩
      · intro i j hij
        obtain rfl | ⟨i', rfl⟩ := i.eq_zero_or_eq_succ
        · obtain rfl | ⟨j', rfl⟩ := j.eq_zero_or_eq_succ
          · exact fun _ hx => hx
          · rintro x ⟨k, _, rfl⟩
            exact Set.mem_range.mpr ⟨k, rfl⟩
        · obtain rfl | ⟨j', rfl⟩ := j.eq_zero_or_eq_succ
          · exact False.elim ((not_le_of_gt (Fin.succ_pos i')) hij)
          · exact Set.image_mono (hsP (by simpa using hij))
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact span_range_inl_complement_basis hPQ bP bQ
        · apply span_image_inl_of_basis_extension
            (P := P₀) (R := P j.succ) (hanti (Fin.zero_le j.succ))
            bP b (fun k => by simp [b, e]) (sP j)
          simpa [tail, P₀] using hbP j

end Erdos3

end

section

namespace Erdos3

open Module

variable {κ : Type*} {n : ℕ}

noncomputable def nestedSupportWeight (S : Fin n → Set κ) (x : κ) : ℕ :=
  by classical exact (Finset.univ.filter fun i => x ∈ S i).card

theorem nestedSupportWeight_le (S : Fin n → Set κ) (x : κ) :
    nestedSupportWeight S x ≤ n := by
  classical
  simpa only [nestedSupportWeight, Finset.card_univ, Fintype.card_fin] using
    Finset.card_filter_le (s := (Finset.univ : Finset (Fin n))) (p := fun i => x ∈ S i)

theorem mem_nestedSupport_iff (S : Fin n → Set κ) (hS : Antitone S) (i : Fin n) (x : κ) :
    x ∈ S i ↔ i.val < nestedSupportWeight S x := by
  classical
  let A := Finset.univ.filter fun j => x ∈ S j
  constructor
  · intro hx
    have hle : Finset.Iic i ⊆ A := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS (Finset.mem_Iic.mp hj) hx⟩
    have hcard := Finset.card_le_card hle
    rw [Fin.card_Iic] at hcard
    exact hcard
  · intro hi
    by_contra hx
    have hle : A ⊆ Finset.Iio i := by
      intro j hj
      apply Finset.mem_Iio.mpr
      by_contra hij
      exact hx (hS (le_of_not_gt hij) (Finset.mem_filter.mp hj).2)
    have hcard := Finset.card_le_card hle
    rw [Fin.card_Iio] at hcard
    exact Nat.not_lt_of_ge hcard hi

theorem exists_sorted_weighted_flag_basis {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (P : Fin n → Submodule K V) (hP : Antitone P) :
    ∃ (e : Basis (Fin (finrank K V)) K V) (w : Fin (finrank K V) → ℕ),
      Monotone w ∧ (∀ j, w j ≤ n) ∧
      ∀ i, P i = Submodule.span K (e '' {j | i.val < w j}) := by
  classical
  obtain ⟨κ, instκ, b, S, hS, hb⟩ := exists_basis_with_nested_supports n P hP
  let : Fintype κ := instκ
  let ρ : κ ≃ Fin (finrank K V) := Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm
  let u : Fin (finrank K V) → ℕ := fun j => nestedSupportWeight S (ρ.symm j)
  let σ := Tuple.sort u
  let e := b.reindex (ρ.trans σ.symm)
  let w : Fin (finrank K V) → ℕ := fun j => u (σ j)
  refine ⟨e, w, Tuple.monotone_sort u, fun j => nestedSupportWeight_le S _, ?_⟩
  intro i
  rw [hb i]
  congr 1
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨σ.symm (ρ k), ?_, ?_⟩
    · simpa only [Set.mem_ofPred_eq, w, u, Equiv.apply_symm_apply, Equiv.symm_apply_apply] using
        (mem_nestedSupport_iff S hS i k).mp hk
    · simp [e, Basis.reindex_apply]
  · rintro ⟨j, hj, rfl⟩
    refine ⟨ρ.symm (σ j), (mem_nestedSupport_iff S hS i _).mpr hj, ?_⟩
    simp [e, Basis.reindex_apply]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BoundedAdaptedBasis
namespace OAI

section

namespace Erdos3

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem span_inter_eq_of_spanning_family {η : Type*} (P : Submodule K V)
    (v : η → P) (hspan : Submodule.span K (Set.range v) = ⊤)
    (S : Set V) (hv : ∀ i, (v i : V) ∈ S) :
    Submodule.span K (S ∩ (P : Set V)) = P := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun _ hx => hx.2)
  · have hmap := congrArg (Submodule.map P.subtype) hspan
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at hmap
    conv_lhs => rw [← hmap]
    apply Submodule.span_mono
    rintro x ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨hv i, (v i).property⟩

theorem exists_sorted_flag_basis_from_spanning_set [FiniteDimensional K V] {n : ℕ}
    (P : Fin n → Submodule K V) (hP : Antitone P) (S : Set V)
    (hS : Submodule.span K S = ⊤)
    (hspan : ∀ i, Submodule.span K (S ∩ (P i : Set V)) = P i) :
    ∃ (e : Basis (Fin (finrank K V)) K V) (w : Fin (finrank K V) → ℕ),
      Monotone w ∧ (∀ j, w j ≤ n) ∧ (∀ j, e j ∈ S) ∧
      ∀ i, P i = Submodule.span K (e '' {j | i.val < w j}) := by
  classical
  obtain ⟨B, hBS, hBli, hBspan, T, hT, hTB, hTspan⟩ :=
    exists_nested_independent_spanning_sets n P S hP hspan
  have hsp : ⊤ ≤ Submodule.span K (Set.range ((↑) : B → V)) := by
    simp only [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hBspan, hS, le_refl]
  let b : Basis B K V := Basis.mk hBli.linearIndependent_restrict hsp
  let : Finite B := Module.Finite.finite_basis b
  let : Fintype B := Fintype.ofFinite B
  let ρ : B ≃ Fin (finrank K V) := Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm
  let u : Fin (finrank K V) → ℕ := fun j => nestedSupportWeight T (ρ.symm j).val
  let σ := Tuple.sort u
  let e := b.reindex (ρ.trans σ.symm)
  let w : Fin (finrank K V) → ℕ := fun j => u (σ j)
  have he (j : Fin (finrank K V)) : e j = (ρ.symm (σ j)).val := by
    simp [e, b, Basis.reindex_apply]
  refine ⟨e, w, Tuple.monotone_sort u, fun j => nestedSupportWeight_le T _, ?_, ?_⟩
  · intro j
    rw [he]
    exact hBS (ρ.symm (σ j)).property
  · intro i
    rw [← hTspan i]
    congr 1
    ext x
    constructor
    · intro hx
      let k : B := ⟨x, hTB i hx⟩
      refine ⟨σ.symm (ρ k), ?_, ?_⟩
      · simpa only [Set.mem_ofPred_eq, w, u, Equiv.apply_symm_apply,
          Equiv.symm_apply_apply] using (mem_nestedSupport_iff T hT i x).mp hx
      · simp only [he, Equiv.apply_symm_apply, Equiv.symm_apply_apply, k]
    · rintro ⟨j, hj, rfl⟩
      rw [he]
      exact (mem_nestedSupport_iff T hT i _).mpr hj

end Erdos3

end

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}

def basisTail (e : Basis (Fin d) ℚ L) (i : ℕ) : Submodule ℚ L where
  carrier := {x | ∀ j : Fin d, j.val < i → e.repr x j = 0}
  zero_mem' := by simp
  add_mem' hx hy := by
    intro j hj
    simp only [map_add, Finsupp.add_apply, hx j hj, hy j hj, zero_add]
  smul_mem' c x hx := by
    intro j hj
    simp only [map_smul, Finsupp.smul_apply, hx j hj, smul_zero]

theorem basisTail_antitone (e : Basis (Fin d) ℚ L) : Antitone (basisTail e) :=
  fun _ _ hij _ hx k hk => hx k (lt_of_lt_of_le hk hij)

theorem basisTail_zero (e : Basis (Fin d) ℚ L) : basisTail e 0 = ⊤ := by
  apply top_unique
  intro x _ j hj
  omega

theorem basisTail_terminal (e : Basis (Fin d) ℚ L) : basisTail e d = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply e.repr.injective
  ext j
  simpa only [map_zero, Finsupp.zero_apply] using hx j j.isLt

theorem basisTail_eq_span (e : Basis (Fin d) ℚ L) (i : ℕ) :
    basisTail e i = Submodule.span ℚ (e '' {j : Fin d | i ≤ j.val}) := by
  ext x
  rw [e.mem_span_image]
  constructor
  · intro hx j hj
    by_contra h
    exact (Finsupp.mem_support_iff.mp hj) (hx j (Nat.lt_of_not_ge h))
  · intro hx j hj
    by_contra h
    exact (not_le_of_gt hj) (hx (Finsupp.mem_support_iff.mpr h))

theorem basis_mem_tail (e : Basis (Fin d) ℚ L) (j : Fin d) {i : ℕ} (hij : i ≤ j.val) :
    e j ∈ basisTail e i := by
  rw [basisTail_eq_span]
  exact Submodule.subset_span ⟨j, hij, rfl⟩

theorem mem_basisTail_succ_iff (e : Basis (Fin d) ℚ L) (j : Fin d) (x : L) :
    x ∈ basisTail e (j.val + 1) ↔ x ∈ basisTail e j.val ∧ e.repr x j = 0 := by
  constructor
  · intro hx
    exact ⟨basisTail_antitone e (Nat.le_succ j.val) hx, hx j (Nat.lt_succ_self j.val)⟩
  · rintro ⟨hx, hj⟩ k hk
    by_cases hkj : k = j
    · simpa only [hkj] using hj
    · apply hx k
      have hne : k.val ≠ j.val := fun h => hkj (Fin.ext h)
      omega

def IsCentralLieBasis (e : Basis (Fin d) ℚ L) : Prop :=
  ∀ (j : Fin d) (a : L), ⁅a, e j⁆ ∈ basisTail e (j.val + 1)

namespace IsCentralLieBasis

variable {e : Basis (Fin d) ℚ L} (he : IsCentralLieBasis e)
include he

theorem lie_mem_tail_succ (i : ℕ) (a : L) {b : L} (hb : b ∈ basisTail e i) :
    ⁅a, b⁆ ∈ basisTail e (i + 1) := by
  classical
  rw [← e.sum_repr b, lie_sum]
  apply Submodule.sum_mem
  intro j _
  rw [lie_smul]
  by_cases hj : j.val < i
  · rw [hb j hj, zero_smul]
    exact (basisTail e (i + 1)).zero_mem
  · exact (basisTail e (i + 1)).smul_mem _
      (basisTail_antitone e (Nat.add_le_add_right (Nat.le_of_not_gt hj) 1) (he j a))

def tailIdeal (i : ℕ) : LieIdeal ℚ L :=
  { basisTail e i with
    lie_mem := by
      intro a b hb
      exact basisTail_antitone e (Nat.le_succ i) (he.lie_mem_tail_succ i a hb) }

end IsCentralLieBasis

theorem centralLieBasis_of_sorted_filtration {s : ℕ} (F : NilpotentLieFiltration L s)
    (e : Basis (Fin d) ℚ L) (w : Fin d → ℕ) (hw : Monotone w)
    (hlayer : ∀ i, F.layer i = Submodule.span ℚ (e '' {j | i ≤ w j})) :
    IsCentralLieBasis e := by
  intro j a
  have ha : a ∈ F.layer 1 := by simp [F.one_eq_top]
  have hj : e j ∈ F.layer (w j) := by
    rw [hlayer]
    exact Submodule.subset_span ⟨j, by simp, rfl⟩
  have hbr := F.lie_mem ha hj
  rw [hlayer] at hbr
  rw [basisTail_eq_span]
  apply Submodule.span_mono (Set.image_mono ?_) hbr
  intro k hk
  change j.val + 1 ≤ k.val
  change 1 + w j ≤ w k at hk
  by_contra h
  have hkj : k ≤ j := by change k.val ≤ j.val; omega
  have hweight := hw hkj
  omega

end Erdos3

end

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d n : ℕ}

theorem finite_flag_weight_le (P : ℕ → Submodule ℚ L) (e : Basis (Fin d) ℚ L)
    (w : Fin d → ℕ) (hn : P n = ⊥)
    (hspan : P n = Submodule.span ℚ (e '' {j | n < w j})) (j : Fin d) : w j ≤ n := by
  by_contra h
  have hj : e j ∈ P n := by
    rw [hspan]
    exact Submodule.subset_span ⟨j, Nat.lt_of_not_ge h, rfl⟩
  rw [hn] at hj
  exact e.ne_zero j (by simpa only [Submodule.mem_bot] using hj)

theorem centralLieBasis_of_finite_flag (P : ℕ → Submodule ℚ L)
    (e : Basis (Fin d) ℚ L) (w : Fin d → ℕ)
    (hzero : P 0 = ⊤) (hterminal : P n = ⊥)
    (hstep : ∀ i, ∀ {x y : L}, y ∈ P i → ⁅x, y⁆ ∈ P (i + 1))
    (hw : Monotone w)
    (hspan : ∀ i : Fin (n + 1), P i.val = Submodule.span ℚ (e '' {j | i.val < w j})) :
    IsCentralLieBasis e := by
  intro j a
  have hjn : w j ≤ n := finite_flag_weight_le P e w hterminal (hspan ⟨n, by omega⟩) j
  have hbr : ⁅a, e j⁆ ∈ P (w j) := by
    cases hweight : w j with
    | zero => simp only [hzero, Submodule.mem_top]
    | succ k =>
        apply hstep k
        rw [hspan ⟨k, by omega⟩]
        exact Submodule.subset_span ⟨j, by change k < w j; omega, rfl⟩
  rw [hspan ⟨w j, by omega⟩] at hbr
  rw [basisTail_eq_span]
  apply Submodule.span_mono (Set.image_mono ?_) hbr
  intro k hk
  change j.val + 1 ≤ k.val
  change w j < w k at hk
  by_contra h
  have hkj : k ≤ j := by change k.val ≤ j.val; omega
  exact (not_lt_of_ge (hw hkj)) hk

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [FiniteDimensional ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s)

include F

omit [FiniteDimensional ℚ L] in
theorem layer_eq_span_of_weighted_flag {d : ℕ} (e : Basis (Fin d) ℚ L) (w : Fin d → ℕ)
    (hbound : ∀ j, w j ≤ s + 1)
    (hlayer : ∀ i : Fin (s + 1),
      F.layer (i.val + 1) = Submodule.span ℚ (e '' {j | i.val < w j})) :
    ∀ i, F.layer i = Submodule.span ℚ (e '' {j | i ≤ w j}) := by
  intro i
  cases i with
  | zero =>
      have hzero : F.layer 0 = ⊤ := by
        apply top_unique
        rw [← F.one_eq_top]
        exact F.antitone (by omega)
      simp only [hzero, Nat.zero_le, Set.ofPred_true, Set.image_univ, e.span_eq]
  | succ i =>
      by_cases hi : i < s + 1
      · simpa only [Nat.succ_le_iff] using hlayer ⟨i, hi⟩
      · have htail : F.layer (i + 1) = ⊥ := by
          apply bot_unique
          simpa only [F.terminal] using F.antitone (show s + 1 ≤ i + 1 by omega)
        have hempty : {j | i + 1 ≤ w j} = (∅ : Set (Fin d)) := by
          ext j
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          have := hbound j
          omega
        rw [htail, hempty, Set.image_empty, Submodule.span_empty]

theorem exists_sorted_adapted_basis :
    ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ),
      Monotone w ∧ (∀ j, w j ≤ s + 1) ∧
      ∀ i, F.layer i = Submodule.span ℚ (e '' {j | i ≤ w j}) := by
  let P : Fin (s + 1) → Submodule ℚ L := fun i => F.layer (i.val + 1)
  have hP : Antitone P := fun i j hij => F.antitone (Nat.add_le_add_right hij 1)
  obtain ⟨e, w, hw, hbound, hlayer⟩ := exists_sorted_weighted_flag_basis P hP
  exact ⟨e, w, hw, hbound, F.layer_eq_span_of_weighted_flag e w hbound hlayer⟩

theorem exists_central_basis :
    ∃ e : Basis (Fin (finrank ℚ L)) ℚ L, IsCentralLieBasis e := by
  obtain ⟨e, w, hw, _, hlayer⟩ := F.exists_sorted_adapted_basis
  exact ⟨e, centralLieBasis_of_sorted_filtration F e w hw hlayer⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module

noncomputable def weightCut {d : ℕ} (w : Fin d → ℕ) (k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j => w j ≤ k)).card

theorem weightCut_le {d : ℕ} (w : Fin d → ℕ) (k : ℕ) : weightCut w k ≤ d := by
  classical
  simpa only [weightCut, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_filter_le (s := (Finset.univ : Finset (Fin d))) (p := fun j => w j ≤ k))

theorem weight_gt_iff_cut_le {d : ℕ} (w : Fin d → ℕ) (hw : Monotone w) (k : ℕ) (j : Fin d) :
    k < w j ↔ weightCut w k ≤ j.val := by
  classical
  let A := Finset.univ.filter (fun i => w i ≤ k)
  constructor
  · intro hj
    have hA : A ⊆ Finset.Iio j := by
      intro i hi
      apply Finset.mem_Iio.mpr
      have hiw : w i ≤ k := (Finset.mem_filter.mp hi).2
      by_contra h
      have := hw (le_of_not_gt h)
      omega
    have hcard := Finset.card_le_card hA
    simpa only [A, Fin.card_Iio, weightCut] using hcard
  · intro hj
    by_contra h
    have hjw : w j ≤ k := le_of_not_gt h
    have hA : Finset.Iic j ⊆ A := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hw (Finset.mem_Iic.mp hi)).trans hjw⟩
    have hcard := Finset.card_le_card hA
    rw [Fin.card_Iic] at hcard
    change j.val + 1 ≤ weightCut w k at hcard
    omega

theorem span_weight_gt_eq_basisTail {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    (b : Basis (Fin d) ℚ L) (w : Fin d → ℕ) (hw : Monotone w) (k : ℕ) :
    Submodule.span ℚ (b '' {j | k < w j}) = basisTail b (weightCut w k) := by
  rw [basisTail_eq_span]
  apply congrArg (Submodule.span ℚ)
  apply congrArg (fun S : Set (Fin d) => b '' S)
  ext j
  exact weight_gt_iff_cut_le w hw k j

end Erdos3

end

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {d : ℕ}

def realBasisTail (e : Basis (Fin d) ℝ L) (i : ℕ) : Submodule ℝ L where
  carrier := {x | ∀ j : Fin d, j.val < i → e.repr x j = 0}
  zero_mem' := by simp
  add_mem' hx hy := by
    intro j hj
    simp only [map_add, Finsupp.add_apply, hx j hj, hy j hj, zero_add]
  smul_mem' c x hx := by
    intro j hj
    simp only [map_smul, Finsupp.smul_apply, hx j hj, smul_zero]

theorem realBasisTail_antitone (e : Basis (Fin d) ℝ L) : Antitone (realBasisTail e) :=
  fun _ _ hij _ hx k hk => hx k (lt_of_lt_of_le hk hij)

def IsRealCentralLieBasis (e : Basis (Fin d) ℝ L) : Prop :=
  ∀ (j : Fin d) (a : L), ⁅a, e j⁆ ∈ realBasisTail e (j.val + 1)

namespace IsRealCentralLieBasis

variable {e : Basis (Fin d) ℝ L} (he : IsRealCentralLieBasis e)
include he

theorem lie_mem_tail_succ (i : ℕ) (a : L) {b : L} (hb : b ∈ realBasisTail e i) :
    ⁅a, b⁆ ∈ realBasisTail e (i + 1) := by
  classical
  rw [← e.sum_repr b, lie_sum]
  apply Submodule.sum_mem
  intro j _
  rw [lie_smul]
  by_cases hj : j.val < i
  · rw [hb j hj, zero_smul]
    exact (realBasisTail e (i + 1)).zero_mem
  · exact (realBasisTail e (i + 1)).smul_mem _
      (realBasisTail_antitone e (Nat.add_le_add_right (Nat.le_of_not_gt hj) 1) (he j a))

noncomputable def tailIdeal [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L] (i : ℕ) : LieIdeal ℚ L :=
  { (realBasisTail e i).restrictScalars ℚ with
    lie_mem := by
      intro a b hb
      exact realBasisTail_antitone e (Nat.le_succ i) (he.lie_mem_tail_succ i a hb) }

end IsRealCentralLieBasis

end Erdos3

namespace Erdos3

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L)

theorem exists_bounded_sorted_adapted_basis {η : Fin (s + 1) → Type*}
    (v : ∀ i, η i → F.layer (i.val + 1))
    (hspan : ∀ i, Submodule.span ℚ (Set.range (v i)) = ⊤) {H : ℕ}
    (hv : ∀ i j k, RationalHeightLE (e.repr (v i j : L) k) H) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ),
      Monotone w ∧ (∀ j, w j ≤ s + 1) ∧ IsCentralLieBasis b ∧
      (∀ j k, RationalHeightLE (e.repr (b j) k) H) ∧
      ∀ i, F.layer i = Submodule.span ℚ (b '' {j | i ≤ w j}) := by
  let : FiniteDimensional ℚ L := e.finiteDimensional_of_finite
  let S : Set L := {x | ∀ k, RationalHeightLE (e.repr x k) H}
  let P : Fin (s + 1) → Submodule ℚ L := fun i => F.layer (i.val + 1)
  have hP : Antitone P := fun i j hij => F.antitone (Nat.add_le_add_right hij 1)
  have hSP (i : Fin (s + 1)) : Submodule.span ℚ (S ∩ (P i : Set L)) = P i :=
    span_inter_eq_of_spanning_family (P i) (v i) (hspan i) S (hv i)
  have hS : Submodule.span ℚ S = ⊤ := by
    apply top_unique
    calc
      ⊤ = P 0 := F.one_eq_top.symm
      _ = Submodule.span ℚ (S ∩ (P 0 : Set L)) := (hSP 0).symm
      _ ≤ Submodule.span ℚ S := Submodule.span_mono Set.inter_subset_left
  obtain ⟨b, w, hw, hbound, hbS, hbP⟩ :=
    exists_sorted_flag_basis_from_spanning_set P hP S hS hSP
  have hlayer := F.layer_eq_span_of_weighted_flag b w hbound hbP
  exact ⟨b, w, hw, hbound, centralLieBasis_of_sorted_filtration F b w hw hlayer, hbS, hlayer⟩

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHOrderedReduction
namespace OAI

section

namespace Erdos3.IsCentralLieBasis

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  {e : Basis (Fin d) ℚ L} (he : IsCentralLieBasis e)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

include he hnil

theorem bch_remainder_mem_tail (i : ℕ) (a : L) {b : L} (hb : b ∈ basisTail e i) :
    lieBCH s a b - (a + b) ∈ basisTail e (i + 1) :=
  lieBCH_sub_add_mem hnil (he.tailIdeal (i + 1)) a b (he.lie_mem_tail_succ i a hb)

theorem bch_low_coordinate (i : ℕ) (a : L) {b : L} (hb : b ∈ basisTail e i)
    (k : Fin d) (hk : k.val ≤ i) :
    e.repr (lieBCH s a b) k = e.repr a k + e.repr b k := by
  have h := he.bch_remainder_mem_tail hnil i a hb k (Nat.lt_succ_of_le hk)
  rw [map_sub, Finsupp.sub_apply, map_add, Finsupp.add_apply] at h
  exact sub_eq_zero.mp h

end Erdos3.IsCentralLieBasis

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeOrderedGenerators
namespace OAI

section

namespace Erdos3.IsCentralLieBasis

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  {e : Basis (Fin d) ℚ L} (he : IsCentralLieBasis e)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))

include he

def leadingCoordinateSubgroup (j : Fin d) : AddSubgroup ℚ where
  carrier := {q | ∃ g ∈ Γ, g.coord ∈ basisTail e j.val ∧ e.repr g.coord j = q}
  zero_mem' := ⟨1, Γ.one_mem, (basisTail e j.val).zero_mem, by simp⟩
  add_mem' := by
    rintro a b ⟨g, hg, hgt, rfl⟩ ⟨h, hh, hht, rfl⟩
    refine ⟨g * h, Γ.mul_mem hg hh, ?_, ?_⟩
    · exact (NilpotentLieBCHGroup.subgroup (he.tailIdeal j.val).toLieSubalgebra).mul_mem hgt hht
    · exact he.bch_low_coordinate hnil j.val g.coord hht j le_rfl
  neg_mem' := by
    rintro a ⟨g, hg, hgt, rfl⟩
    exact ⟨g⁻¹, Γ.inv_mem hg, (basisTail e j.val).neg_mem hgt, by simp⟩

theorem leadingCoordinateSubgroup_le_zmultiples (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) (j : Fin d) :
    he.leadingCoordinateSubgroup hnil Γ j ≤ AddSubgroup.zmultiples ((l : ℚ)⁻¹) := by
  rintro q ⟨g, hg, _, rfl⟩
  obtain ⟨z, hz⟩ := (mem_denominatorGrid_iff l hl _).mp
    (hgrid ((bchSubgroupCoordinates_repr e Γ g).mpr hg))
  apply AddSubgroup.mem_zmultiples_iff.mpr
  refine ⟨z j, ?_⟩
  simpa only [zsmul_eq_mul, div_eq_mul_inv, Basis.equivFun_apply] using (hz j).symm

theorem leadingCoordinateSubgroup_isAddCyclic (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) (j : Fin d) :
    IsAddCyclic (he.leadingCoordinateSubgroup hnil Γ j) :=
  AddSubgroup.isAddCyclic_of_le (he.leadingCoordinateSubgroup_le_zmultiples hnil Γ l hl hgrid j)

theorem exists_tail_generator (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) (j : Fin d) :
    ∃ a ∈ Γ, a.coord ∈ basisTail e j.val ∧
      ∀ g ∈ Γ, g.coord ∈ basisTail e j.val →
        ∃ n : ℤ, ((a ^ n)⁻¹ * g).coord ∈ basisTail e (j.val + 1) := by
  let H := he.leadingCoordinateSubgroup hnil Γ j
  let : IsAddCyclic H := he.leadingCoordinateSubgroup_isAddCyclic hnil Γ l hl hgrid j
  obtain ⟨q, hq⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top H).mp inferInstance
  have hqmem : q ∈ H := hq ▸ AddSubgroup.mem_zmultiples q
  obtain ⟨a, ha, hat, haq⟩ := hqmem
  refine ⟨a, ha, hat, ?_⟩
  intro g hg hgt
  have hcoord : e.repr g.coord j ∈ H := ⟨g, hg, hgt, rfl⟩
  rw [← hq] at hcoord
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hcoord
  refine ⟨n, (mem_basisTail_succ_iff e j _).mpr ⟨?_, ?_⟩⟩
  · let T := NilpotentLieBCHGroup.subgroup (hnil := hnil) (he.tailIdeal j.val).toLieSubalgebra
    exact T.mul_mem (T.inv_mem (T.zpow_mem hat n)) hgt
  · change e.repr (lieBCH s (-((a ^ n).coord)) g.coord) j = 0
    rw [he.bch_low_coordinate hnil j.val _ hgt j le_rfl]
    simp only [map_neg, Finsupp.neg_apply, NilpotentLieBCHGroup.coord_zpow,
      map_zsmul, Finsupp.smul_apply, haq, hn, neg_add_cancel]

end Erdos3.IsCentralLieBasis

end

section

namespace Erdos3.IsCentralLieBasis

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  {e : Basis (Fin d) ℚ L} (he : IsCentralLieBasis e)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))

include he

theorem exists_ordered_lattice_generators (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    ∃ a : Fin d → NilpotentLieBCHGroup L s hnil,
      (∀ j, a j ∈ Γ) ∧ (∀ j, (a j).coord ∈ basisTail e j.val) ∧
      ∀ g ∈ Γ, ∃ z : Fin d → ℤ, orderedZpowProduct a z = g := by
  classical
  choose a ha hat hpeel using fun j => he.exists_tail_generator hnil Γ l hl hgrid j
  have hfactor (k i : ℕ) (hik : i + k = d)
      (g : NilpotentLieBCHGroup L s hnil) (hg : g ∈ Γ) (hgt : g.coord ∈ basisTail e i) :
      ∃ z : Fin d → ℤ, orderedGroupTailProduct (fun j => a j ^ z j) i = g := by
    induction k generalizing i g with
    | zero =>
        have hi : i = d := by omega
        subst i
        refine ⟨fun _ => 0, ?_⟩
        rw [orderedGroupTailProduct_terminal _ le_rfl]
        apply NilpotentLieBCHGroup.ext
        have hz : g.coord = 0 := by
          simpa only [basisTail_terminal, Submodule.mem_bot] using hgt
        exact hz.symm
    | succ k ih =>
        have hi : i < d := by omega
        let j : Fin d := ⟨i, hi⟩
        obtain ⟨n, hn⟩ := hpeel j g hg hgt
        let r := (a j ^ n)⁻¹ * g
        have hr : r ∈ Γ := Γ.mul_mem (Γ.inv_mem (Γ.zpow_mem (ha j) n)) hg
        obtain ⟨z, hz⟩ := ih (i + 1) (by omega) r hr hn
        let u := Function.update z j n
        have huj : u j = n := by simp [u]
        have hu : orderedGroupTailProduct (fun j => a j ^ u j) (i + 1) =
            orderedGroupTailProduct (fun j => a j ^ z j) (i + 1) := by
          apply orderedGroupTailProduct_congr
          intro v hv
          have hvj : v ≠ j := by
            intro h
            subst v
            change i + 1 ≤ i at hv
            omega
          change a v ^ Function.update z j n v = a v ^ z v
          rw [Function.update_of_ne hvj]
        refine ⟨u, ?_⟩
        change orderedGroupTailProduct (fun j => a j ^ u j) j.val = g
        rw [orderedGroupTailProduct_step, huj]
        change a j ^ n * orderedGroupTailProduct (fun j => a j ^ u j) (i + 1) = g
        rw [hu, hz]
        exact mul_inv_cancel_left (a j ^ n) g
  refine ⟨a, ha, hat, ?_⟩
  intro g hg
  exact hfactor d 0 (by omega) g hg (by simp [basisTail_zero])

theorem exists_surjective_orderedZpowProduct (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    ∃ a : Fin d → Γ, Function.Surjective (orderedZpowProduct a) := by
  obtain ⟨a, ha, _, hgen⟩ := he.exists_ordered_lattice_generators hnil Γ l hl hgrid
  refine ⟨fun j => ⟨a j, ha j⟩, ?_⟩
  intro g
  obtain ⟨z, hz⟩ := hgen g g.property
  refine ⟨z, Subtype.ext ?_⟩
  change Γ.subtype (orderedZpowProduct (fun j => ⟨a j, ha j⟩) z) = g.val
  rw [orderedZpowProduct_map]
  exact hz

end Erdos3.IsCentralLieBasis

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CentralBasisPowerCover
namespace OAI

section

namespace Erdos3.IsCentralLieBasis

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  {e : Basis (Fin d) ℚ L} (he : IsCentralLieBasis e)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))

include he

theorem subgroupPowerCover_index_le (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) (m : ℕ) (hm : 0 < m) :
    ((subgroupPowerCover Γ m).subgroupOf Γ).FiniteIndex ∧
      (subgroupPowerCover Γ m).relIndex Γ ≤ m ^ d := by
  obtain ⟨a, ha⟩ := he.exists_surjective_orderedZpowProduct hnil Γ l hl hgrid
  have h := powerSubgroup_index_le_of_ordered_generators a ha m hm
  simpa only [Subgroup.relIndex, subgroupPowerCover_subgroupOf] using h

end Erdos3.IsCentralLieBasis

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FilteredLatticePowerIndex
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s)

theorem subgroupPowerCover_index_le (e : Basis ι ℚ L) (Γ : Subgroup F.Group)
    (l : ℕ) (hl : 0 < l) (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (m : ℕ) (hm : 0 < m) :
    ((subgroupPowerCover Γ m).subgroupOf Γ).FiniteIndex ∧
      (subgroupPowerCover Γ m).relIndex Γ ≤ m ^ Fintype.card ι := by
  let : FiniteDimensional ℚ L := Module.Finite.of_basis e
  obtain ⟨b, hb⟩ := F.exists_central_basis
  obtain ⟨N, hN, hgrid⟩ := exists_bchSubgroup_outer_grid_change_basis e b Γ l hl houter
  simpa only [finrank_eq_card_basis e] using
    hb.subgroupPowerCover_index_le F.lowerCentralSeries_eq_bot Γ N hN hgrid m hm

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledSurjectiveReconstruction
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s)

theorem exists_sharp_normal_cover (e : Basis ι ℚ L) (Γ Λ₀ : Subgroup F.Group)
    (l m₀ : ℕ) (hl : 0 < l) (hm₀ : 0 < m₀)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (htarget : scaledIntegerGrid m₀ ⊆ bchSubgroupCoordinates e Λ₀) :
    ∃ Λ : Subgroup F.Group,
      Λ ≤ Λ₀ ∧ Λ ≤ Γ ∧ (Λ.subgroupOf Γ).Characteristic ∧ (Λ.subgroupOf Γ).Normal ∧
      (Λ.subgroupOf Γ).FiniteIndex ∧ Λ.relIndex Γ ≤ (l * m₀) ^ Fintype.card ι ∧
      scaledIntegerGrid ((l * m₀) * l) ⊆ bchSubgroupCoordinates e Λ ∧
      bchSubgroupCoordinates e Λ ⊆ denominatorGrid ((l * m₀) * l) := by
  let m := l * m₀
  obtain ⟨hfinite, hindex⟩ := F.subgroupPowerCover_index_le e Γ l hl houter m
    (Nat.mul_pos hl hm₀)
  exact ⟨subgroupPowerCover Γ m,
    subgroupPowerCover_le_of_grid e Γ Λ₀ l m₀ m houter htarget dvd_rfl,
    subgroupPowerCover_le Γ m, inferInstance, inferInstance, hfinite, hindex,
    subgroupPowerCover_grid e Γ l m hinner houter⟩

theorem exists_normal_cover_exp_quadratic (e : Basis ι ℚ L) (Γ Λ₀ : Subgroup F.Group)
    (l m₀ : ℕ) (hl : 0 < l) (hm₀ : 0 < m₀)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (htarget : scaledIntegerGrid m₀ ⊆ bchSubgroupCoordinates e Λ₀)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hlb : (l : ℝ) ≤ Real.exp p) (hm₀b : (m₀ : ℝ) ≤ Real.exp p) :
    ∃ Λ : Subgroup F.Group,
      Λ ≤ Λ₀ ∧ Λ ≤ Γ ∧ (Λ.subgroupOf Γ).Characteristic ∧ (Λ.subgroupOf Γ).Normal ∧
      (Λ.subgroupOf Γ).FiniteIndex ∧ (Λ.relIndex Γ : ℝ) ≤ Real.exp (2 * p ^ 2) ∧
      ∃ ℓ : ℕ, 0 < ℓ ∧ (ℓ : ℝ) ≤ Real.exp ((p + 2) ^ 2) ∧
        scaledIntegerGrid ℓ ⊆ bchSubgroupCoordinates e Λ ∧
        bchSubgroupCoordinates e Λ ⊆ denominatorGrid ℓ := by
  obtain ⟨Λ, hΛ₀, hΛ, hchar, hnormal, hfinite, hindex, hin, hout⟩ :=
    F.exists_sharp_normal_cover e Γ Λ₀ l m₀ hl hm₀ hinner houter htarget
  refine ⟨Λ, hΛ₀, hΛ, hchar, hnormal, hfinite, ?_, (l * m₀) * l,
    Nat.mul_pos (Nat.mul_pos hl hm₀) hl, powerCover_grid_allowance_le_exp l m₀ hp hlb hm₀b,
    hin, hout⟩
  exact (Nat.cast_le.mpr hindex).trans (powerCover_index_allowance_le_exp l m₀ _ hp hlb hm₀b hd)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ExternalPivotMaskSelection
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem sum_externalNet_masked_complex_scores
    {J X Y I : Type*} [Fintype J] [Fintype I]
    (p : FiniteProbabilityWeights J) (idx : X → I)
    (physical : J → X) (point : J → Y) (w : X → ℂ) (centers : I → Y → ℂ) :
    (∑ i, p.complexMean (fun j =>
      (if idx (physical j) = i then w (physical j) else 0) * centers i (point j))) =
    p.complexMean (fun j => w (physical j) * centers (idx (physical j)) (point j)) := by
  simp only [FiniteProbabilityWeights.complexMean]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_sum]
  simp only [ite_mul, zero_mul]
  simp

theorem exists_externalNet_large_masked_complex_score
    {J X Y I : Type*} [Fintype J] [Fintype I] [Nonempty I]
    (p : FiniteProbabilityWeights J) (F : X → Y → ℂ) (centers : I → Y → ℂ)
    {B ε δ : ℝ} (hnet : ∀ x, ∃ i, ∀ y, ‖F x y - centers i y‖ ≤ ε)
    (physical : J → X) (point : J → Y) (w : X → ℂ)
    (hB : 0 ≤ B) (hδ : 0 < δ) (herror : B * ε ≤ δ / 2)
    (hw : ∀ j, ‖w (physical j)‖ ≤ B)
    (hscore : δ ≤ ‖p.complexMean (fun j => w (physical j) * F (physical j) (point j))‖) :
    ∃ i, δ / (2 * Fintype.card I) ≤ ‖p.complexMean (fun j =>
      (if externalNetIndex F centers hnet (physical j) = i then w (physical j) else 0) *
        centers i (point j))‖ := by
  let idx := externalNetIndex F centers hnet
  let scores := fun i => p.complexMean (fun j =>
    (if idx (physical j) = i then w (physical j) else 0) * centers i (point j))
  have hnear := p.norm_complexMean_weighted_lower_of_perturbation
    (fun j => w (physical j)) (fun j => centers (idx (physical j)) (point j))
    (fun j => F (physical j) (point j)) hB hw
    (fun j => by rw [norm_sub_rev]; exact externalNetIndex_approx F centers hnet _ _) hscore
  have hsum : δ / 2 ≤ ‖∑ i, (1 : ℂ) * scores i‖ := by
    simp only [one_mul]
    rw [show (∑ i, scores i) = p.complexMean (fun j =>
      w (physical j) * centers (idx (physical j)) (point j)) from
        sum_externalNet_masked_complex_scores p idx physical point w centers]
    linarith
  obtain ⟨i, hi⟩ := exists_large_weighted_term (fun _ : I => (1 : ℂ)) scores
    (by positivity : 0 < δ / 2) (show 0 < (Fintype.card I : ℝ) from Nat.cast_pos.mpr Fintype.card_pos)
    (by simp) hsum
  refine ⟨i, ?_⟩
  simpa only [scores, idx, div_div] using hi

theorem exists_simultaneous_external_pivot_masks
    {Ω J K X Y I : Type*} [Fintype Ω] [Fintype J] [Fintype K]
    [Fintype I] [Nonempty I]
    (F : K → X → Y → ℂ) (centers : K → I → Y → ℂ)
    {B ε δ : ℝ} (hnet : ∀ k x, ∃ i, ∀ y, ‖F k x y - centers k i y‖ ≤ ε)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → K → FiniteProbabilityWeights J)
    (physical : Ω → J → X) (point : Ω → K → J → Y) (w : X → ℂ)
    (hB : 0 ≤ B) (hδ : 0 < δ) (herror : B * ε ≤ δ / 2)
    (hw : ∀ x, ‖w x‖ ≤ B)
    (hscore : ∀ a ∈ H, ∀ k, δ ≤ ‖(localLaw a k).complexMean
      (fun j => w (physical a j) * F k (physical a j) (point a k j))‖) :
    ∃ (chosen : K → I) (masked : K → X → ℂ) (H' : Finset Ω),
      (∀ k x, masked k x =
        if externalNetIndex (F k) (centers k) (hnet k) x = chosen k then w x else 0) ∧
      (∀ k x, ‖masked k x‖ ≤ B) ∧
      H' ⊆ H ∧ 0 < outer.mass H' ∧
      outer.mass H / (Fintype.card I : ℝ) ^ Fintype.card K ≤ outer.mass H' ∧
      ∀ a ∈ H', ∀ k, δ / (2 * Fintype.card I) ≤
        ‖(localLaw a k).complexMean (fun j => masked k (physical a j) *
          centers k (chosen k) (point a k j))‖ := by
  have hex (a : Ω) (ha : a ∈ H) (k : K) :=
    exists_externalNet_large_masked_complex_score (localLaw a k) (F k) (centers k)
      (hnet k) (physical a) (point a k) w hB hδ herror
      (fun j => hw _) (hscore a ha k)
  let code : Ω → K → I := fun a k =>
    if ha : a ∈ H then Classical.choose (hex a ha k) else Classical.choice inferInstance
  obtain ⟨chosen, hmass⟩ := outer.exists_code_fiber_mass H code
  let H' := H.filter (fun a => code a = chosen)
  have hsub : H' ⊆ H := Finset.filter_subset _ _
  have hmass' : outer.mass H / (Fintype.card I : ℝ) ^ Fintype.card K ≤ outer.mass H' := by
    rw [Fintype.card_fun, Nat.cast_pow] at hmass
    convert hmass using 1
    congr 1
    ext a
    simp only [H', Finset.mem_filter]
  have hpos : 0 < outer.mass H' :=
    (div_pos hH (pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _)).trans_le hmass'
  let masked := fun k x =>
    if externalNetIndex (F k) (centers k) (hnet k) x = chosen k then w x else 0
  refine ⟨chosen, masked, H', fun _ _ => rfl, ?_, hsub, hpos, hmass', ?_⟩
  · intro k x
    dsimp only [masked]
    split_ifs
    · exact hw x
    · simpa only [norm_zero] using hB
  · intro a ha k
    have hcode : code a = chosen := (Finset.mem_filter.mp ha).2
    have he := Classical.choose_spec (hex a (hsub ha) k)
    have hc : code a k = Classical.choose (hex a (hsub ha) k) := by
      simp only [code, dif_pos (hsub ha)]
    rw [← hc, hcode] at he
    exact he

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteBoundedListEnumeration
namespace OAI

section

namespace Erdos3

theorem exists_boundedList_option_padding {α : Type*} {M : ℕ}
    (c : Fin M → α) (P : α → Prop)
    (hcover : ∀ x, P x → ∃ i, c i = x) :
    ∀ (N : ℕ) (l : List α), l.length ≤ N → (∀ x ∈ l, P x) →
      ∃ v : Fin N → Option (Fin M),
        (List.ofFn v).filterMap (Option.map c) = l := by
  intro N
  induction N with
  | zero =>
      intro l hlen hP
      have hl : l = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
      subst l
      exact ⟨fun i => Fin.elim0 i, by simp⟩
  | succ N ih =>
      intro l hlen hP
      cases l with
      | nil =>
          exact ⟨fun _ => none, by simp [List.ofFn_const]⟩
      | cons x l =>
          obtain ⟨i, hi⟩ := hcover x (hP x (by simp))
          have hlen' : l.length ≤ N := Nat.le_of_succ_le_succ hlen
          obtain ⟨v, hv⟩ := ih l hlen' (fun y hy => hP y (by simp [hy]))
          refine ⟨Fin.cons (some i) v, ?_⟩
          simpa [List.ofFn_succ, hi] using congrArg (List.cons x) hv

end Erdos3

end

section

namespace Erdos3

theorem exists_finite_bounded_list_enumeration {α : Type*} {M : ℕ}
    (c : Fin M → α) (P : α → Prop)
    (hvalid : ∀ i, P (c i)) (hcover : ∀ x, P x → ∃ i, c i = x) (N : ℕ) :
    ∃ n : ℕ, n ≤ (M + 1) ^ N ∧ ∃ candidates : Fin n → List α,
      (∀ j, (candidates j).length ≤ N) ∧
      (∀ j x, x ∈ candidates j → P x) ∧
      ∀ l : List α, l.length ≤ N → (∀ x, x ∈ l → P x) →
        ∃ j, candidates j = l := by
  classical
  let V := Fin N → Option (Fin M)
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let decode : V → List α := fun v => (List.ofFn v).filterMap (Option.map c)
  refine ⟨Fintype.card V, ?_, (fun j => decode (e.symm j)), ?_, ?_, ?_⟩
  · simp [V]
  · intro j
    exact (List.length_filterMap_le _ _).trans (by simp)
  · intro j x hx
    obtain ⟨o, _, ho⟩ := List.mem_filterMap.mp hx
    obtain ⟨i, _, hi⟩ := Option.map_eq_some_iff.mp ho
    exact hi ▸ hvalid i
  · intro l hlen hl
    obtain ⟨v, hv⟩ := exists_boundedList_option_padding c P hcover N l hlen hl
    refine ⟨e v, ?_⟩
    simpa only [Equiv.symm_apply_apply] using hv

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteProductCellMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteCellMean {X A : Type*} [Fintype X] [DecidableEq A]
    (p : FiniteProbabilityWeights X) (C : X → A) (f : X → ℝ) (a : A) : ℝ :=
  p.mean (fun x => if C x = a then f x else 0)

theorem finiteCellMean_sum {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
    (p : FiniteProbabilityWeights X) (C : X → A) (f : X → ℝ) :
    (∑ a, finiteCellMean p C f a) = p.mean f := by
  unfold finiteCellMean
  rw [← p.mean_sum]
  congr 1
  funext x
  simp

noncomputable def finiteCellWeights {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
    (p : FiniteProbabilityWeights X) (C : X → A) : FiniteProbabilityWeights A where
  weight a := finiteCellMean p C (fun _ => 1) a
  nonneg a := p.mean_nonneg (fun x => by split_ifs <;> norm_num)
  total := by rw [finiteCellMean_sum, p.mean_const]

noncomputable def finiteCellResidueMean {X A R : Type*}
    [Fintype X] [DecidableEq A] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (C : X → A) (F : X → R) (e : X → ℝ) (a : A) (r : R) : ℝ :=
  p.mean (fun x => if C x = a ∧ F x = r then e x else 0)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {X T A B : Type*} [Fintype X] [Fintype T] [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteSeriesCoefficientBounds
namespace OAI

section

namespace Erdos3

variable {X : Type*}

def finiteSeriesWeight (s : ℕ) (i : Fin 2 × Fin (s + 1)) : ℚ :=
  if i.1 = 0 then (i.2.val.factorial : ℚ)⁻¹ else (-1 : ℚ) ^ (i.2.val + 1) / i.2.val

def finiteSeriesDenominator (s : ℕ) : ℕ := arrayDenominator (finiteSeriesWeight s)

def finiteSeriesNumerator (s : ℕ) (i : Fin 2 × Fin (s + 1)) : ℤ :=
  clearedArray (finiteSeriesWeight s) i

def finiteSeriesNumeratorBound (s : ℕ) : ℕ :=
  1 + ∑ i, (finiteSeriesNumerator s i).natAbs

theorem finiteSeriesDenominator_pos (s : ℕ) : 0 < finiteSeriesDenominator s :=
  arrayDenominator_pos _

theorem finiteSeriesNumerator_cast (s : ℕ) (i : Fin 2 × Fin (s + 1)) :
    (finiteSeriesNumerator s i : ℚ) = (finiteSeriesDenominator s : ℚ) * finiteSeriesWeight s i :=
  clearedArray_cast _ _

theorem finiteSeriesNumerator_le (s : ℕ) (i : Fin 2 × Fin (s + 1)) :
    (finiteSeriesNumerator s i).natAbs ≤ finiteSeriesNumeratorBound s := by
  have h := Finset.single_le_sum (f := fun j => (finiteSeriesNumerator s j).natAbs)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact h.trans (Nat.le_add_left _ 1)

theorem finiteExp_freeCoefficientBound (s : ℕ) (x : X) :
    FreeCoefficientBound s (finiteSeriesDenominator s)
      ((s + 1) * finiteSeriesNumeratorBound s) (finiteExp (s + 1) (FreeAlgebra.ι ℚ x)) := by
  have hterm : ∀ i ∈ Finset.range (s + 1),
      FreeCoefficientBound s (finiteSeriesDenominator s) (finiteSeriesNumeratorBound s)
        ((i.factorial : ℚ)⁻¹ • (FreeAlgebra.ι ℚ x) ^ i) := by
    intro i hi
    let j : Fin 2 × Fin (s + 1) := (0, ⟨i, Finset.mem_range.mp hi⟩)
    have h := (FreeCoefficientBound.word s ((FreeMonoid.of x) ^ i)).smul
      (finiteSeriesNumerator_cast s j) (finiteSeriesNumerator_le s j)
    simpa only [j, finiteSeriesWeight, ite_true, mul_one, map_pow, freeWord_of] using h
  simpa only [finiteExp, Finset.card_range] using
    FreeCoefficientBound.sum_finset (Finset.range (s + 1)) _ hterm

theorem finiteLog_freeCoefficientBound {s D M : ℕ} {p : FreeAlgebra ℚ X}
    (hp : FreeCoefficientBound s D M p) :
    FreeCoefficientBound s (finiteSeriesDenominator s * D ^ s)
      ((s + 1) * finiteSeriesNumeratorBound s * (D + (s + 1) * M) ^ s) (finiteLog (s + 1) p) := by
  have hterm : ∀ i ∈ Finset.range (s + 1),
      FreeCoefficientBound s (finiteSeriesDenominator s * D ^ s)
        (finiteSeriesNumeratorBound s * (D + (s + 1) * M) ^ s)
        (((-1 : ℚ) ^ (i + 1) / i) • p ^ i) := by
    intro i hi
    have his : i ≤ s := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    let j : Fin 2 × Fin (s + 1) := (1, ⟨i, Finset.mem_range.mp hi⟩)
    have h := ((hp.pow i).smul (finiteSeriesNumerator_cast s j)
      (finiteSeriesNumerator_le s j)).enlarge_denominator (D ^ (s - i))
    have hden : D ^ (s - i) * (finiteSeriesDenominator s * D ^ i) = finiteSeriesDenominator s * D ^ s := by
      rw [mul_left_comm, ← pow_add, Nat.sub_add_cancel his]
    rw [hden] at h
    have hmass : D ^ (s - i) * (finiteSeriesNumeratorBound s * (((s + 1) * M) ^ i)) ≤
        finiteSeriesNumeratorBound s * (D + (s + 1) * M) ^ s := by
      calc
        _ = finiteSeriesNumeratorBound s * (D ^ (s - i) * (((s + 1) * M) ^ i)) := by ring
        _ ≤ finiteSeriesNumeratorBound s *
            ((D + (s + 1) * M) ^ (s - i) * (D + (s + 1) * M) ^ i) := by
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.le_add_right _ _) _)
            (Nat.pow_le_pow_left (Nat.le_add_left _ _) _)
        _ = _ := by rw [← pow_add, Nat.sub_add_cancel his]
    simpa only [j, finiteSeriesWeight, show (1 : Fin 2) ≠ 0 from by decide, ite_false] using h.mono hmass
  simpa only [finiteLog, Finset.card_range, mul_assoc] using
    FreeCoefficientBound.sum_finset (Finset.range (s + 1)) _ hterm

def bchProductDenominator (s n : ℕ) : ℕ :=
  finiteSeriesDenominator s * (finiteSeriesDenominator s ^ n) ^ s

def bchProductNumeratorBound (s n : ℕ) : ℕ :=
  (s + 1) * finiteSeriesNumeratorBound s *
    (finiteSeriesDenominator s ^ n + (s + 1) *
      ((((s + 1) * ((s + 1) * finiteSeriesNumeratorBound s)) ^ n) + finiteSeriesDenominator s ^ n)) ^ s

theorem bchProductDenominator_pos (s n : ℕ) : 0 < bchProductDenominator s n := by
  unfold bchProductDenominator
  exact Nat.mul_pos (finiteSeriesDenominator_pos s) (pow_pos (pow_pos (finiteSeriesDenominator_pos s) _) _)

theorem bchProductPolynomial_coefficient_bound (s : ℕ) (xs : List X) :
    FreeCoefficientBound s (bchProductDenominator s xs.length) (bchProductNumeratorBound s xs.length)
      (bchProductPolynomial s xs) := by
  have hprod := FreeCoefficientBound.list_prod
    (xs.map (fun x => finiteExp (s + 1) (FreeAlgebra.ι ℚ x))) (by
      intro p hp
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hp
      exact finiteExp_freeCoefficientBound s x)
  simp only [List.length_map] at hprod
  have hone := (FreeCoefficientBound.one (X := X) s).enlarge_denominator
    (finiteSeriesDenominator s ^ xs.length)
  simp only [mul_one] at hone
  have hsub := hprod.add_same hone.neg
  rw [← sub_eq_add_neg] at hsub
  exact finiteLog_freeCoefficientBound hsub

end Erdos3

end

end OAI

end


