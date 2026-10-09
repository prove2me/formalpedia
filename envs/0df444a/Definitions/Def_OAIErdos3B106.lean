-- Prove2me | Definitions.Def_OAIErdos3B106
-- name    : OAIErdos3B106
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T00:20:38.657993+00:00
-- url     : https://prove2.me/theorems/39ddda6b-c0e6-4f65-bc15-6c90c6fedfc7
-- title:
--   OpenAI Erdős-3 split, definitions bundle 107 of 132
-- statement:
--   Definitions bundle 107 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B105`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 107 available.
--
--   Modules: `OAI.Erdos3.DegreeRankLieFiltration.lie_realLayer_le`, `OAI.Erdos3.DegreeRankLieFiltration.nativeHorizontalCoefficientHom`, `OAI.Erdos3.DegreeRankLieFiltration.nativeHorizontalCoefficientHom_apply`, `OAI.Erdos3.DegreeRankLieFiltration.nativeHorizontalCoefficientHom_tensor`, `OAI.Erdos3.DegreeRankLieFiltration.nativeHorizontalCoefficientHom_translate`, `OAI.Erdos3.DegreeRankLieFiltration.projectedHorizontalSymbolCoefficient_native`, `OAI.Erdos3.DegreeRankLieFiltration.rational_inclusion_mem_realLayer`, `OAI.Erdos3.DegreeRankLieFiltration.realLayer`, `OAI.Erdos3.DegreeRankLieFiltration.realLayer_congr`, `OAI.Erdos3.DegreeRankLieFiltration.realLayer_lex_antitone`, `OAI.Erdos3.DegreeRankLieFiltration.realLayer_lie_mem`, `OAI.Erdos3.DegreeRankLieFiltration.realLayer_one`, `OAI.Erdos3.DegreeRankLieFiltration.realLayer_overshoot`, `OAI.Erdos3.DegreeRankLieFiltration.realLayer_rank_zero_eq_one`, `OAI.Erdos3.DegreeRankLieFiltration.realLayer_terminal`, `OAI.Erdos3.DegreeRankLieFiltration.realification`, `OAI.Erdos3.DegreeRankLieFiltration.realification_associatedDegree`, `OAI.Erdos3.DegreeRankLieFiltration.withRank`, `OAI.Erdos3.KernelProjectionPresentPivot`, `OAI.Erdos3.NilpotentLieFiltration.PolynomialOrbit.translate`, `OAI.Erdos3.NilpotentLieFiltration.adaptedTranslateLinear`, `OAI.Erdos3.NilpotentLieFiltration.adaptedTranslateLinear_coe`, `OAI.Erdos3.NilpotentLieFiltration.frequency_zero_on_refilteredLayer_of_real`, `OAI.Erdos3.NilpotentLieFiltration.mem_prod_layer`, `OAI.Erdos3.NilpotentLieFiltration.optionFiltrations`, `OAI.Erdos3.NilpotentLieFiltration.optionFiltrations_none`, `OAI.Erdos3.NilpotentLieFiltration.optionFiltrations_some`, `OAI.Erdos3.NilpotentLieFiltration.pivotAnnihilatorIdeal_presentPivots`, `OAI.Erdos3.NilpotentLieFiltration.pivotAnnihilatorIdeal_presentPivots_toSubmodule`, `OAI.Erdos3.NilpotentLieFiltration.pivotProductQuotientFiltration`, `OAI.Erdos3.NilpotentLieFiltration.pivotQuotientFiltration`, `OAI.Erdos3.NilpotentLieFiltration.pivotQuotientFiltration_layer`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbitEval_translate`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSymbolMap_adaptedTranslateLinear`, `OAI.Erdos3.NilpotentLieFiltration.prod`, `OAI.Erdos3.NilpotentLieFiltration.prod_layer`, `OAI.Erdos3.NilpotentLieFiltration.realFilteredPolynomialSymbolMap_extended`, `OAI.Erdos3.NilpotentLieFiltration.realFilteredPolynomialSymbolMap_polynomial`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolMap_translate`, `OAI.Erdos3.NilpotentLieFiltration.realSquarePairHom`, `OAI.Erdos3.PatchKernel.weightBounded`, `OAI.Erdos3.PatchKernel.weightBounded_lip`, `OAI.Erdos3.PolynomialPatch.recoveredPatch`, `OAI.Erdos3.PolynomialPatch.recoveredPatch_lip`, `OAI.Erdos3.PolynomialPatch.recursiveRecoveredPatch`, `OAI.Erdos3.PolynomialPatch.recursiveRecoveredPatch_lip`, `OAI.Erdos3.PolynomialPatch.recursiveRecoveredPatch_value`, `OAI.Erdos3.PolynomialPatch.withRecoveredWeight`, `OAI.Erdos3.PositiveCyclicModel`, `OAI.Erdos3.PositiveCyclicNiltest.model_nonempty`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.ComplexityLE`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.ComplexityLE.mono`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.casesOn`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.orbitEquiv`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.orbitEquiv_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.realSubgroup`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.realSubgroup_le_degree`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.real_associated`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.withRank`, `OAI.Erdos3.RationalFilteredNilmanifold.DegreeRankStructure.withRank_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.exists_controlled_vertical_decomposition`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.exists_vertical_decomposition_preserving_bounds`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.raiseStep_rank_vertical`, `OAI.Erdos3.RationalFilteredNilmanifold.cyclicOrbitPoint_translate`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_adapted_basis`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_central_actions`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_square_geometry`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_controlled_vertical_decomposition`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_fixed_observable_correlators`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_coordinateBox_cover`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_degree_rank_structure`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_factor_partitions`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_frozen_parameter_fiber`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_group_parameter_cover`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_niltest_partition`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_positive_partition`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_quotient_parameter_cover`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_raised_degree_rank_structure`, `OAI.Erdos3.RationalFilteredNilmanifold.integerOrbitPoint`, `OAI.Erdos3.RationalFilteredNilmanifold.lowered_productProjectionHom_realificationMap`, `OAI.Erdos3.RationalFilteredNilmanifold.optionComplementFactors`, `OAI.Erdos3.RationalFilteredNilmanifold.optionComplementOrbits`, `OAI.Erdos3.RationalFilteredNilmanifold.optionMarkedLieMap_native_logHeight`, `OAI.Erdos3.RationalFilteredNilmanifold.optionMarkedLieMap_piRealOrbit_log`, `OAI.Erdos3.RationalFilteredNilmanifold.optionProductSpaceEquiv`, `OAI.Erdos3.RationalFilteredNilmanifold.optionProductSpaceEquiv_apply`, `OAI.Erdos3.RationalFilteredNilmanifold.optionProductSpaceEquiv_realificationMap`, `OAI.Erdos3.RationalFilteredNilmanifold.optionProductSpaceEquiv_symm_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.productMetricBound_singleton`, `OAI.Erdos3.RationalFilteredNilmanifold.productMetricBound_singleton_le_exp`, `OAI.Erdos3.RationalFilteredNilmanifold.productProjectionHom_realificationMap`, `OAI.Erdos3.RationalFilteredNilmanifold.productSpaceEquiv_singletonProductSpace`, `OAI.Erdos3.RationalFilteredNilmanifold.raiseStep_rankSubgroup_eq_bot`, `OAI.Erdos3.RationalFilteredNilmanifold.singletonProductSpace`, `OAI.Erdos3.RationalFilteredNilmanifold.singletonProductSpace_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.singletonProductSpace_realificationMap`, `OAI.Erdos3.complex_partition_approximation_mean_error`, `OAI.Erdos3.euclidean_graph_gram`, `OAI.Erdos3.euclidean_section_basis_norm_le_gram_sqrt`, `OAI.Erdos3.euclidean_section_gram`, `OAI.Erdos3.euclidean_section_gram_sub_one_posSemidef`, `OAI.Erdos3.euclidean_section_norm_le_gram_sqrt`, `OAI.Erdos3.exists_biased_linear_coefficient_splitting`, `OAI.Erdos3.exists_bounded_complex_partition_approximation`, `OAI.Erdos3.exists_bounded_frequency_kernel_spanning`, `OAI.Erdos3.exists_common_frequency_kernel`, `OAI.Erdos3.exists_complex_partition_approximation`, `OAI.Erdos3.exists_correlating_summand_of_mean`, `OAI.Erdos3.exists_frequency_basis_code`, `OAI.Erdos3.exists_frequency_code_kernel_basis_logHeight`, `OAI.Erdos3.exists_frequency_kernel_basis_logHeight`, `OAI.Erdos3.exists_large_unit_coordinate`, `OAI.Erdos3.exists_linear_frequency_splitting`, `OAI.Erdos3.finiteFrequencyKernel_presentPivots`, `OAI.Erdos3.frequencyCodeKernel`, `OAI.Erdos3.gram_linearMap_quadratic`, `OAI.Erdos3.instFintypeKernelProjectionPresentPivot`, `OAI.Erdos3.kernelProjectionPresentPivot_card_le`, `OAI.Erdos3.kernelProjectionSelectedPivot`, `OAI.Erdos3.kernelProjectionSelectedPivot_spec`, `OAI.Erdos3.mean_error_mul_bounded`, `OAI.Erdos3.mem_frequencyCodeKernel`, `OAI.Erdos3.norm_correlation_sub_le_mean`, `OAI.Erdos3.norm_le_sqrt_gram_det_mul`, `OAI.Erdos3.norm_positive_partition_sum_le_one`, `OAI.Erdos3.norm_sub_positive_sum_le`, `OAI.Erdos3.one_le_euclidean_section_gram_sqrt`, `OAI.Erdos3.optionComplementMap`, `OAI.Erdos3.optionComplementMaps`, `OAI.Erdos3.optionMarkedComponents`, `OAI.Erdos3.optionMarkedLieMap`, `OAI.Erdos3.optionMarkedLieMap_mem_layer`, `OAI.Erdos3.optionMarkedLieMap_none`, `OAI.Erdos3.optionMarkedLieMap_some`, `OAI.Erdos3.optionMarkedPolynomialProjection_none`, `OAI.Erdos3.pi_fin_card_le_exp`, `OAI.Erdos3.realBCHPiEquiv_optionMarkedLieMap_none`, `OAI.Erdos3.realBCHPiEquiv_optionMarkedLieMap_some`, `OAI.Erdos3.realIntegerMatrix`, `OAI.Erdos3.realification_optionMarkedLieMap_none`, `OAI.Erdos3.realification_optionMarkedLieMap_some`, `OAI.Erdos3.realifyFunctional_denominator_grid`, `OAI.Erdos3.realifyFunctional_zero`, `OAI.Erdos3.recoveredCellKernel`, `OAI.Erdos3.recoveredCellKernel_lip`, `OAI.Erdos3.recoveredCellKernel_value`, `OAI.Erdos3.recoveredIntegerLift`, `OAI.Erdos3.recoveredSmallLift`, `OAI.Erdos3.recoveredSmallLift_lipschitz`, `OAI.Erdos3.scalarFunctionalDenominator_le`, `OAI.Erdos3.scalarFunctionalDenominator_pos`, `OAI.Erdos3.squareGeometryBudget`, `OAI.Erdos3.squareGeometryBudget_nonneg`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B034

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineResidualRecovery
namespace OAI

section

namespace Erdos3

open scoped NNReal

def recoveredIntegerLift {d m : ℕ} (M : Fin m → Fin d → ℤ) (c : Fin m → ℤ)
    (k : Fin d → ℤ) : Fin m → ℤ := fun i => c i + ∑ j, M i j * k j

noncomputable def realIntegerMatrix {d m : ℕ} (M : Fin m → Fin d → ℤ)
    (x : Fin d → ℝ) : Fin m → ℝ := fun i => ∑ j, (M i j : ℝ) * x j

noncomputable def recoveredSmallLift {d m : ℕ} (M : Fin m → Fin d → ℤ)
    (a : Fin d → ℝ) (c : Fin m → ℤ) (e : Fin d → ℝ) : Fin m → ℝ :=
  fun i => (∑ j, (M i j : ℝ) * (a j - e j)) - c i

theorem recoveredSmallLift_lipschitz {d m : ℕ} (M : Fin m → Fin d → ℤ)
    (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) : LipschitzWith K (recoveredSmallLift M a c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg K.coe_nonneg dist_nonneg)).mpr
  intro i
  simp only [recoveredSmallLift, Real.dist_eq]
  rw [sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, |(M i j : ℝ) * (a j - x j) - (M i j : ℝ) * (a j - y j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |(M i j : ℝ)| * dist x y := by
      apply Finset.sum_le_sum
      intro j _
      rw [← mul_sub, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [sub_sub_sub_cancel_left, abs_sub_comm, Real.dist_eq] using dist_le_pi_dist x y j
    _ = (∑ j, |(M i j : ℝ)|) * dist x y := (Finset.sum_mul _ _ _).symm
    _ ≤ K * dist x y := mul_le_mul_of_nonneg_right (hM i) dist_nonneg

noncomputable def recoveredCellKernel {d m : ℕ} (Φ : PatchKernel d) (Ψ : PatchKernel m)
    (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) : PatchKernel d :=
  Φ.weightAlong Ψ (recoveredSmallLift M a c) K (recoveredSmallLift_lipschitz M a c K hM)

@[simp] theorem recoveredCellKernel_lip {d m : ℕ} (Φ : PatchKernel d) (Ψ : PatchKernel m)
    (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) :
    (recoveredCellKernel Φ Ψ M a c K hM).lip = Φ.lip + Ψ.lip * K := rfl

@[simp] theorem recoveredCellKernel_value {d m : ℕ} (Φ : PatchKernel d) (Ψ : PatchKernel m)
    (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (e : Fin d → ℝ) :
    (recoveredCellKernel Φ Ψ M a c K hM).value e = Φ.value e * Ψ.value (recoveredSmallLift M a c e) := rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FixedObservableCorrelation
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_coordinateBox_cover {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s d H : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    (B : ℝ≥0) (hB : 1 ≤ B) {ε : ℝ} (hε : 0 < ε) :
    let n := (boxCoverMeshCount B (bchBoxMetricConstant s d H B) ε + 1) ^ d
    ∃ centers : Fin n → coordinateBox
        (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ) B,
      letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.basis.baseChange ℝ)
      ∀ x : coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
          (D.basis.baseChange ℝ) B, ∃ j, dist x (centers j) ≤ ε := by
  classical
  have hcover := exists_coordinateBox_metric_cover
    (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ) (lieStructureConstants D.basis)
    (fun i j k => (realLieBasis_structure D.basis i j k).symm) hc B hB hε
  change ∃ centers : (Fin d → Fin (boxCoverMeshCount B
      (bchBoxMetricConstant s (Fintype.card (Fin d)) H B) ε + 1)) →
      coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ) B,
      letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      ∀ x : coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.basis.baseChange ℝ) B, ∃ j, dist x (centers j) ≤ ε at hcover
  rw [Fintype.card_fin] at hcover
  obtain ⟨c, hc⟩ := hcover
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let N := boxCoverMeshCount B (bchBoxMetricConstant s d H B) ε
  let I := Fin d → Fin (N + 1)
  have hcard : Fintype.card I = (N + 1) ^ d := by simp only [I, Fintype.card_fun, Fintype.card_fin]
  let e : I ≃ Fin ((N + 1) ^ d) := Fintype.equivFinOfCardEq hcard
  refine ⟨fun i => c (e.symm i), ?_⟩
  intro x
  obtain ⟨j, hj⟩ := hc x
  refine ⟨e j, ?_⟩
  simpa only [e.symm_apply_apply] using hj

theorem exists_native_group_parameter_cover (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) (B : ℝ≥0) {p ε : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → 1 ≤ B →
      (B : ℝ) ≤ Real.exp ((p + 2) ^ r) → 0 < ε → 1 / ε ≤ Real.exp p →
      let A := coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.basis.baseChange ℝ) B
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ centers : Fin n → A,
          letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
            (D.basis.baseChange ℝ)
          ∀ x : A, ∃ j, dist x (centers j) ≤ ε := by
  obtain ⟨C₀, _, hsize⟩ := exists_bchBoxCover_count_budget s r
  refine ⟨1 + C₀ + 2, by omega, ?_⟩
  intro L _ _ _ _ _ _ d D B p ε hp hD hB hBp hε hεinv
  let H := ⌈Real.exp p⌉₊
  have hh : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)
  obtain ⟨c, hc⟩ := D.exists_native_coordinateBox_cover hh B hB hε
  have hcount := hsize d H B (p := p + 1) (by linarith) (by linarith [hD.1])
    (ceil_exp_le_exp_add_one hp)
    (hBp.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) r))) hε
    (hεinv.trans (Real.exp_le_exp.mpr (by linarith)))
  have hshift : ((p + 1) + C₀) ^ C₀ ≤ (p + (1 + C₀ + 2 : ℕ)) ^ (1 + C₀ + 2) := by
    simpa only [Nat.cast_one] using shifted_center_power_bound 1 C₀ hp
  exact ⟨_, by positivity, hcount.trans (Real.exp_le_exp.mpr hshift), c, hc⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_frozen_parameter_fiber (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p ε : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → 0 < ε → 1 / ε ≤ Real.exp p →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∀ (H : Finset G) (a u : G → D.RealGroup), H.Nonempty →
      (∀ h ∈ H, ∀ i, |(D.basis.baseChange ℝ).repr (a h).coord i| ≤ Real.exp ((p + 2) ^ k)) →
      (∀ h ∈ H, ∀ i, |(D.basis.baseChange ℝ).repr (u h).coord i| ≤ Real.exp ((p + 2) ^ k)) →
      (∀ h ∈ H, (D.basis.baseChange ℝ).equivFun (u h).coord ∈ realDenominatorGrid q) →
      ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        ∃ a₀ u₀ : D.RealGroup,
          (∀ i, |(D.basis.baseChange ℝ).repr a₀.coord i| ≤ Real.exp ((p + 2) ^ k)) ∧
          (∀ i, |(D.basis.baseChange ℝ).repr u₀.coord i| ≤ Real.exp ((p + 2) ^ k)) ∧
          (D.basis.baseChange ℝ).equivFun u₀.coord ∈ realDenominatorGrid q ∧
          letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
            (D.basis.baseChange ℝ)
          ∀ h ∈ H', dist (a h) a₀ ≤ ε ∧ u h = u₀ := by
  obtain ⟨b, _, hcover⟩ := exists_native_group_parameter_cover s k
  let A := k + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + Polynomial.C b) ^ b +
      (Polynomial.X + Polynomial.C (A + 5)) ^ (A + 5))
  refine ⟨C, hC, ?_⟩
  intro G L _ _ _ _ _ _ d D p ε hp hD hε hεp q hq hqp H a u hH ha hu hugrid
  classical
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let B : ℝ≥0 := ⟨Real.exp ((p + 2) ^ k), (Real.exp_pos _).le⟩
  have hB : 1 ≤ B := by
    change (1 : ℝ) ≤ Real.exp ((p + 2) ^ k)
    exact Real.one_le_exp (pow_nonneg (by linarith) _)
  obtain ⟨n, hn, hnp, centers, hnet⟩ := hcover D B hp hD hB le_rfl hε hεp
  have hac (h : {h // h ∈ H}) : a h ∈ coordinateBox
      (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ) B :=
    ha h h.property
  choose index hindex using fun h : {h // h ∈ H} => hnet ⟨a h, hac h⟩
  let label (h : G) : Fin n := if hh : h ∈ H then index ⟨h, hh⟩ else ⟨0, hn⟩
  have hlabel (h : G) (hh : h ∈ H) : dist (a h) (centers (label h)).val ≤ ε := by
    simpa only [label, dif_pos hh, Subtype.dist_eq] using hindex ⟨h, hh⟩
  let S : Set (Fin d → ℝ) := {v | (∀ i, |v i| ≤ B) ∧ v ∈ realDenominatorGrid q}
  have hA : 2 ≤ A := by dsimp [A]; omega
  have hpow : (p + 2) ^ k ≤ (p + A) ^ A := by
    have hAr : (2 : ℝ) ≤ A := by exact_mod_cast hA
    exact (pow_le_pow_left₀ (by linarith) (by linarith) k).trans
      (pow_le_pow_right₀ (by linarith) (by dsimp [A]; omega))
  obtain ⟨hS, hScard⟩ := finite_card_real_grid_box S q
    ⌈(q : ℝ) * Real.exp ((p + A) ^ A)⌉₊ hq (fun _ hv => hv.2)
    (fun v hv i => (hv.1 i).trans (Real.exp_le_exp.mpr hpow)) (Nat.le_ceil _)
  have hScount : (S.ncard : ℝ) ≤ Real.exp ((p + (A + 5 : ℕ)) ^ (A + 5)) := by
    apply (Nat.cast_le.mpr (by simpa only [Fintype.card_fin] using hScard)).trans
    simpa only [Nat.cast_add, Nat.cast_ofNat] using grid_box_count_le_exp A d q hA hp hD.1 hqp
  let colors : Set (Fin n × (Fin d → ℝ)) := Set.univ ×ˢ S
  have hcolors : colors.Finite := (Set.toFinite (Set.univ : Set (Fin n))).prod hS
  let code (h : G) : Fin n × (Fin d → ℝ) :=
    (label h, (D.basis.baseChange ℝ).equivFun (u h).coord)
  have hcode (h : G) (hh : h ∈ H) : code h ∈ colors :=
    ⟨Set.mem_univ _, hu h hh, hugrid h hh⟩
  have hcost : (p + b) ^ b + (p + (A + 5 : ℕ)) ^ (A + 5) ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  have hcount : (colors.ncard : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [colors, Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin, Nat.cast_mul]
    exact (mul_le_mul hnp hScount (Nat.cast_nonneg _) (Real.exp_pos _).le).trans
      (by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr hcost)
  obtain ⟨⟨j, z⟩, _, H', hsub, hnonempty, hconstant, hdense⟩ :=
    exists_exponential_constant_fiber H hH code colors hcolors hcode hcount
  obtain ⟨h₀, hh₀⟩ := hnonempty
  refine ⟨H', hsub, ⟨h₀, hh₀⟩, hdense, (centers j).val, u h₀,
    (centers j).property, hu h₀ (hsub hh₀), hugrid h₀ (hsub hh₀), ?_⟩
  intro h hh
  have hi : label h = j := congrArg Prod.fst (hconstant h hh)
  refine ⟨by simpa only [hi] using hlabel h (hsub hh), ?_⟩
  apply NilpotentLieBCHGroup.ext
  apply (D.basis.baseChange ℝ).equivFun.injective
  exact (congrArg Prod.snd (hconstant h hh)).trans (congrArg Prod.snd (hconstant h₀ hh₀)).symm

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_quotient_parameter_cover (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p ε : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → 0 < ε → 1 / ε ≤ Real.exp p →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ ∃ centers : Fin n → D.Space,
        letI := D.metricSpace
        ∀ x : D.Space, ∃ j, dist x (centers j) ≤ ε := by
  obtain ⟨A, hA, hrep⟩ := exists_realification_representatives_exp_bound s
  obtain ⟨C₀, _, hsize⟩ := exists_bchBoxCover_count_budget s A
  refine ⟨(A + 1) + C₀ + 2, by omega, ?_⟩
  intro L _ _ _ _ _ _ d D p ε hp hD hε hεinv
  let H := ⌈Real.exp p⌉₊
  let B : ℝ≥0 := ⟨Real.exp (((p + 1) + A) ^ A), (Real.exp_pos _).le⟩
  have hB : 1 ≤ B := Real.one_le_exp (pow_nonneg (by positivity) _)
  have hh : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)
  have hr := hrep D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice D.grid H (p + 1)
    D.grid_pos D.inner_grid hh (by linarith)
    (by simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 1 by linarith))
    (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
  obtain ⟨c, hc⟩ := D.exists_native_coordinateBox_cover hh B hB hε
  let t := p + (A + 1 : ℕ)
  have hpt : p ≤ t := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hp1t : p + 1 ≤ t := by dsimp [t]; push_cast; linarith
  have hBt : (B : ℝ) ≤ Real.exp ((t + 2) ^ A) := by
    apply Real.exp_le_exp.mpr
    apply pow_le_pow_left₀ (by positivity)
    dsimp [t]
    push_cast
    linarith
  have hcount := hsize d H B (p := t) (hp.trans hpt) (hD.1.trans hpt)
    ((ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hp1t)) hBt hε
    (hεinv.trans (Real.exp_le_exp.mpr hpt))
  have hshift : (t + C₀) ^ C₀ ≤ (p + ((A + 1) + C₀ + 2 : ℕ)) ^ ((A + 1) + C₀ + 2) :=
    shifted_center_power_bound (A + 1) C₀ hp
  refine ⟨_, by positivity, hcount.trans (Real.exp_le_exp.mpr hshift),
    fun j => QuotientGroup.mk (c j).val, ?_⟩
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := D.metricSpace
  have hproj : LipschitzWith 1 (QuotientGroup.mk : D.RealGroup → D.Space) :=
    quotientMetricSpace_lipschitz_mk (D.basis.baseChange ℝ) D.realLattice D.realLattice_closed_discrete.1
  intro x
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨r, hr, γ, hγ, hg⟩ := hr g
    obtain ⟨j, hj⟩ := hc ⟨r, hr⟩
    refine ⟨j, ?_⟩
    change dist (QuotientGroup.mk g : D.Space) (QuotientGroup.mk (c j).val) ≤ ε
    have heq : (QuotientGroup.mk g : D.Space) = QuotientGroup.mk r := by
      rw [hg]
      exact QuotientGroup.mk_mul_of_mem r (show γ ∈ D.realLattice from hγ)
    rw [heq]
    have hdist : dist (QuotientGroup.mk r : D.Space) (QuotientGroup.mk (c j).val) ≤ dist r (c j).val := by
      simpa only [NNReal.coe_one, one_mul] using hproj.dist_le_mul r (c j).val
    exact hdist.trans hj

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_native_positive_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p ρ : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → 0 < ρ →
      1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      letI := D.metricSpace
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ ψ : Fin n → D.Space → ℝ,
          (∀ i x, 0 ≤ ψ i x ∧ ψ i x ≤ 1) ∧
          (∀ x, ∑ i, ψ i x = 1) ∧
          (∀ i, LipschitzWith K (ψ i)) ∧
          ∀ i x y, 0 < ψ i x → 0 < ψ i y → dist x y ≤ ρ := by
  obtain ⟨A, _, hcover⟩ := exists_native_quotient_parameter_cover s
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + 2) ^ a + 4
  let B := T + (T + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * B + 2)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p ρ hp hD hρ hρinv
  let t := p + (p + 2) ^ a + 4
  have hpt : p ≤ t := by dsimp [t]; linarith [pow_nonneg (show 0 ≤ p + 2 by linarith) a]
  have ht : 0 ≤ t := hp.trans hpt
  let r : ℝ≥0 := ⟨ρ / 4, (div_pos hρ (by norm_num)).le⟩
  have hr : 0 < r := div_pos hρ (by norm_num)
  have hrinv : 1 / (r : ℝ) ≤ Real.exp t := by
    calc
      _ = 4 * (1 / ρ) := by change 1 / (ρ / 4) = 4 * (1 / ρ); ring
      _ ≤ Real.exp 4 * Real.exp ((p + 2) ^ a) :=
        mul_le_mul (by linarith [Real.add_one_le_exp (4 : ℝ)]) hρinv
          (by positivity) (Real.exp_pos _).le
      _ = Real.exp (4 + (p + 2) ^ a) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [t]; linarith)
  obtain ⟨n, hn, hnb, c, hc⟩ := hcover D ht (hD.mono D hpt) (show 0 < (r : ℝ) from hr) hrinv
  let b := t + (t + A) ^ A
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have htb : t ≤ b := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hAb : (t + A) ^ A ≤ b := le_add_of_nonneg_left ht
  have hcost : 2 * b + 2 ≤ (p + C) ^ C := by
    simpa [B, T, X, b, t, Polynomial.eval₂_pow] using hbudget p hp
  have hbC : b ≤ (p + C) ^ C := by linarith
  let K : ℝ≥0 := (2 * n + 1) / r
  have hK : (K : ℝ) ≤ Real.exp ((p + C) ^ C) :=
    (metricPartition_constant_le_exp n r hb
      (hnb.trans (Real.exp_le_exp.mpr hAb))
      (hrinv.trans (Real.exp_le_exp.mpr htb))).trans (Real.exp_le_exp.mpr hcost)
  let := D.metricSpace
  let ψ := metricTentPartition c r
  refine ⟨n, hn, hnb.trans (Real.exp_le_exp.mpr (hAb.trans hbC)), K, hK, ψ,
    fun i x => ⟨metricTentPartition_nonneg c r i x, metricTentPartition_le_one c hr hc i x⟩,
    sum_metricTentPartition c hr hc, fun i => ?_, ?_⟩
  · simpa only [Fintype.card_fin] using lipschitz_metricTentPartition c hr hc i
  · intro i x y hx hy
    have hxc : dist x (c i) < 2 * (r : ℝ) := by
      by_contra h
      have hz := metricTentPartition_zero_of_far c r i x (le_of_not_gt h)
      change 0 < metricTentPartition c r i x at hx
      linarith
    have hyc : dist y (c i) < 2 * (r : ℝ) := by
      by_contra h
      have hz := metricTentPartition_zero_of_far c r i y (le_of_not_gt h)
      change 0 < metricTentPartition c r i y at hy
      linarith
    have htri := dist_triangle x (c i) y
    rw [dist_comm (c i) y] at htri
    change dist x (c i) < 2 * (ρ / 4) at hxc
    change dist y (c i) < 2 * (ρ / 4) at hyc
    linarith

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem norm_sub_positive_sum_le {I : Type*} [Fintype I]
    (w : I → ℝ) (c : I → ℂ) (t : ℂ) (error : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (herr : ∀ i, 0 < w i → ‖t - c i‖ ≤ error) :
    ‖t - ∑ i, (w i : ℂ) * c i‖ ≤ error := by
  have hsumC : (∑ i, (w i : ℂ)) = 1 := by exact_mod_cast hsum
  have hid : t - ∑ i, (w i : ℂ) * c i = ∑ i, (w i : ℂ) * (t - c i) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsumC, one_mul]
  rw [hid]
  calc
    _ ≤ ∑ i, ‖(w i : ℂ) * (t - c i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, w i * error := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
      rcases (hw i).eq_or_lt with hi | hi
      · rw [← hi, zero_mul, zero_mul]
      · exact mul_le_mul_of_nonneg_left (herr i hi) (hw i)
    _ = error := by rw [← Finset.sum_mul, hsum, one_mul]

theorem exists_complex_partition_approximation {I X : Type*} [Fintype I]
    [PseudoMetricSpace X] (w : I → X → ℝ)
    (hw : ∀ i x, 0 ≤ w i x) (hsum : ∀ x, ∑ i, w i x = 1)
    {rho : ℝ} (hdiam : ∀ i x y, 0 < w i x → 0 < w i y → dist x y ≤ rho)
    (F : X → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1) {K : ℝ≥0} (hLip : LipschitzWith K F) :
    ∃ c : I → ℂ, (∀ i, ‖c i‖ ≤ 1) ∧
      ∀ x, ‖F x - ∑ i, (w i x : ℂ) * c i‖ ≤ (K : ℝ) * rho := by
  classical
  have hchoose (i : I) : ∃ c : ℂ, ‖c‖ ≤ 1 ∧
      ∀ x, 0 < w i x → ‖F x - c‖ ≤ (K : ℝ) * rho := by
    by_cases hi : ∃ y, 0 < w i y
    · obtain ⟨y, hy⟩ := hi
      refine ⟨F y, hF y, fun x hx => ?_⟩
      have h := hLip.dist_le_mul x y
      rw [dist_eq_norm] at h
      exact h.trans (mul_le_mul_of_nonneg_left (hdiam i x y hx hy) K.coe_nonneg)
    · refine ⟨0, by norm_num, fun x hx => False.elim (hi ⟨x, hx⟩)⟩
  choose c hc herr using hchoose
  exact ⟨c, hc, fun x => norm_sub_positive_sum_le (fun i => w i x) c (F x) _
    (fun i => hw i x) (hsum x) (fun i => herr i x)⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem pi_fin_card_le_exp {α : Type*} [Fintype α] [DecidableEq α]
    (n : α → ℕ) {p q : ℝ} (hq : 0 ≤ q) (hα : (Fintype.card α : ℝ) ≤ p)
    (hn : ∀ a, (n a : ℝ) ≤ Real.exp q) :
    (Fintype.card (∀ a, Fin (n a)) : ℝ) ≤ Real.exp (p * q) := by
  rw [Fintype.card_pi, Nat.cast_prod]
  simp only [Fintype.card_fin]
  calc
    (∏ a, (n a : ℝ)) ≤ ∏ _a : α, Real.exp q :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun a _ => hn a)
    _ = Real.exp ((Fintype.card α : ℝ) * q) := by
      rw [Finset.prod_const, Finset.card_univ, Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hα hq)

namespace RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_native_factor_partitions (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {α : Type*} [Fintype α] [DecidableEq α]
      {L : α → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {d : α → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {p rho : ℝ},
      0 ≤ p → (Fintype.card α : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      0 < rho → 1 / rho ≤ Real.exp ((p + 2) ^ a) →
      letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
      ∃ n : α → ℕ, (∀ i, 0 < n i) ∧ (∀ i, (n i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ K : α → ℝ≥0, (∀ i, (K i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
          ∃ ψ : ∀ i, Fin (n i) → (D i).Space → ℝ,
            (∀ i j x, 0 ≤ ψ i j x ∧ ψ i j x ≤ 1) ∧
            (∀ i x, ∑ j, ψ i j x = 1) ∧
            (∀ i j, LipschitzWith (K i) (ψ i j)) ∧
            ∀ i j x y, 0 < ψ i j x → 0 < ψ i j y → dist x y ≤ rho := by
  obtain ⟨c, _, hpart⟩ := exists_native_positive_partition s a
  let R : Polynomial ℕ := (Polynomial.X + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Polynomial.X * R + R)
  refine ⟨C, hC, ?_⟩
  intro α _ _ L _ _ _ _ _ _ d D p rho hp hα hD hrho hscale
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  choose n hn hnb K hKb ψ hunit hsum hLip hdiam using
    (fun i => hpart (D i) hp (hD i) hrho hscale)
  have hR : 0 ≤ (p + c) ^ c := pow_nonneg (add_nonneg hp (Nat.cast_nonneg c)) _
  have hbudget' : p * (p + c) ^ c + (p + c) ^ c ≤ (p + C) ^ C := by
    simpa [R, Polynomial.eval₂_pow] using hbudget p hp
  have hsmall : (p + c) ^ c ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (mul_nonneg hp hR)).trans hbudget'
  have hlarge : p * (p + c) ^ c ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right hR).trans hbudget'
  refine ⟨n, hn, fun i => (hnb i).trans (Real.exp_le_exp.mpr hsmall),
    (pi_fin_card_le_exp n hR hα hnb).trans (Real.exp_le_exp.mpr hlarge),
    K, fun i => (hKb i).trans (Real.exp_le_exp.mpr hsmall), ψ, hunit, hsum, hLip, hdiam⟩

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_bounded_complex_partition_approximation {I X : Type*} [Fintype I]
    [PseudoMetricSpace X] (w : I → X → ℝ)
    (hw : ∀ i x, 0 ≤ w i x) (hsum : ∀ x, ∑ i, w i x = 1)
    {rho : ℝ} (hdiam : ∀ i x y, 0 < w i x → 0 < w i y → dist x y ≤ rho)
    (F : X → ℂ) (B : ℝ≥0) (hF : ∀ x, ‖F x‖ ≤ B) {K : ℝ≥0} (hLip : LipschitzWith K F) :
    ∃ c : I → ℂ, (∀ i, ‖c i‖ ≤ B) ∧
      ∀ x, ‖F x - ∑ i, (w i x : ℂ) * c i‖ ≤ (K : ℝ) * rho := by
  classical
  have hchoose (i : I) : ∃ c : ℂ, ‖c‖ ≤ B ∧
      ∀ x, 0 < w i x → ‖F x - c‖ ≤ (K : ℝ) * rho := by
    by_cases hi : ∃ y, 0 < w i y
    · obtain ⟨y, hy⟩ := hi
      refine ⟨F y, hF y, fun x hx => ?_⟩
      have h := hLip.dist_le_mul x y
      rw [dist_eq_norm] at h
      exact h.trans (mul_le_mul_of_nonneg_left (hdiam i x y hx hy) K.coe_nonneg)
    · exact ⟨0, by simpa only [norm_zero] using B.coe_nonneg,
        fun x hx => False.elim (hi ⟨x, hx⟩)⟩
  choose c hc herr using hchoose
  exact ⟨c, hc, fun x => norm_sub_positive_sum_le (fun i => w i x) c (F x) _
    (fun i => hw i x) (hsum x) (fun i => herr i x)⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem norm_positive_partition_sum_le_one {I : Type*} [Fintype I]
    (w : I → ℝ) (c : I → ℂ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (hc : ∀ i, ‖c i‖ ≤ 1) :
    ‖∑ i, (w i : ℂ) * c i‖ ≤ 1 := by
  calc
    _ ≤ ∑ i, ‖(w i : ℂ) * c i‖ := norm_sum_le _ _
    _ ≤ ∑ i, w i := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
      exact mul_le_of_le_one_right (hw i) (hc i)
    _ = 1 := hsum

theorem complex_partition_approximation_mean_error {I X : Type*}
    [Fintype I] [Fintype X] [Nonempty X]
    (E : Finset X) (w : I → X → ℝ) (c : I → X → ℂ) (T : X → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε) (hw : ∀ i x, 0 ≤ w i x)
    (hsum : ∀ x, ∑ i, w i x = 1) (hc : ∀ i x, ‖c i x‖ ≤ 1)
    (hT : ∀ x, ‖T x‖ ≤ 1)
    (hgood : ∀ i x, x ∉ E → 0 < w i x → ‖T x - c i x‖ ≤ ε) :
    (𝔼 x, ‖T x - ∑ i, (w i x : ℂ) * c i x‖) ≤
      ε + 2 * (E.card : ℝ) / Fintype.card X := by
  have hcap (x : X) : ‖T x - ∑ i, (w i x : ℂ) * c i x‖ ≤ 2 := by
    have hb := norm_positive_partition_sum_le_one (fun i => w i x) (fun i => c i x)
      (fun i => hw i x) (hsum x) (fun i => hc i x)
    exact (norm_sub_le _ _).trans (by linarith [hT x])
  have h := expect_abs_le_of_exceptional_set E
    (fun x => ‖T x - ∑ i, (w i x : ℂ) * c i x‖) hε
    (fun x => by simpa only [abs_of_nonneg (norm_nonneg _)] using hcap x)
    (fun x hx => by
      rw [abs_of_nonneg (norm_nonneg _)]
      exact norm_sub_positive_sum_le (fun i => w i x) (fun i => c i x) (T x) ε
        (fun i => hw i x) (hsum x) (fun i => hgood i x hx))
  simpa only [abs_of_nonneg (norm_nonneg _)] using h

theorem norm_correlation_sub_le_mean {X : Type*} [Fintype X]
    (f u v : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖(𝔼 x, f x * star (u x)) - (𝔼 x, f x * star (v x))‖ ≤
      𝔼 x, ‖u x - v x‖ := by
  rw [← Finset.expect_sub_distrib]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply Finset.expect_le_expect
  intro x _
  rw [← mul_sub, ← star_sub, norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _) (hf x)

theorem exists_correlating_summand_of_mean {X I : Type*} [Fintype X] [Fintype I]
    (f u : X → ℂ) (v : I → X → ℂ) {ρ M : ℝ}
    (hρ : 0 < ρ) (hM : 0 < M) (hcard : (Fintype.card I : ℝ) ≤ M)
    (hf : ∀ x, ‖f x‖ ≤ 1)
    (herr : (𝔼 x, ‖u x - ∑ i, v i x‖) ≤ ρ / 2)
    (hcorr : ρ ≤ ‖𝔼 x, f x * star (u x)‖) :
    ∃ i, ρ / (2 * M) ≤ ‖𝔼 x, f x * star (v i x)‖ := by
  have he := (norm_correlation_sub_le_mean f u (fun x => ∑ i, v i x) hf).trans herr
  have hsum : ρ / 2 ≤ ‖∑ i, 𝔼 x, f x * star (v i x)‖ := by
    have ht := norm_le_norm_add_norm_sub
      (𝔼 x, f x * star (∑ i, v i x)) (𝔼 x, f x * star (u x))
    have hm : (𝔼 x, f x * star (∑ i, v i x)) = ∑ i, 𝔼 x, f x * star (v i x) := by
      simp only [star_sum, Finset.mul_sum, Finset.expect_sum_comm]
    rw [norm_sub_rev] at ht
    rw [hm] at he ht
    linarith
  obtain ⟨i, hi⟩ := exists_large_weighted_term (fun _ : I => (1 : ℂ))
    (fun i => 𝔼 x, f x * star (v i x)) (by linarith : 0 < ρ / 2) hM
    (by simpa only [norm_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using hcard)
    (by simpa only [one_mul] using hsum)
  exact ⟨i, by simpa only [div_div] using hi⟩

theorem mean_error_mul_bounded {X : Type*} [Fintype X]
    (u v b : X → ℂ) {B ε : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, ‖b x‖ ≤ B) (he : (𝔼 x, ‖u x - v x‖) ≤ ε) :
    (𝔼 x, ‖u x * b x - v x * b x‖) ≤ B * ε := by
  calc
    _ ≤ 𝔼 x, B * ‖u x - v x‖ := by
      apply Finset.expect_le_expect
      intro x _
      rw [← sub_mul, norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
    _ = B * (𝔼 x, ‖u x - v x‖) := (Finset.mul_expect _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left he hB

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators NNReal

theorem exists_fixed_observable_correlators (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d)
      (T : G → D.Niltest (fun _ : Unit => 1)) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      (∀ h ∈ H, (T h).ComplexityLE p) → (∀ h ∈ H, (T h).normBound ≤ 1) →
      ∀ {N : ℕ} [NeZero N] (weight : G → ZMod N → ℂ),
      (∀ h ∈ H, ∀ x, ‖weight h x‖ ≤ 1) →
      (∀ h ∈ H, Real.exp (-p) ≤
        ‖𝔼 x, weight h x * star ((T h).evalCyclic N (fun _ => x))‖) →
      ∃ (H' : Finset G) (S : G → D.Niltest (fun _ : Unit => 1)),
        H' ⊆ H ∧ H'.Nonempty ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        (∀ h, (S h).orbit = (T h).orbit ∧ (S h).normBound ≤ 1 ∧
          (S h).UnitIntervalValued ∧ (S h).ComplexityLE ((p + C) ^ C)) ∧
        (∀ h k, (S h).observable = (S k).observable) ∧
        ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
          ‖𝔼 x, weight h x * star ((S h).evalCyclic N (fun _ => x))‖ := by
  classical
  obtain ⟨A, _, hpartition⟩ := exists_native_positive_partition s 2
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + (X + Polynomial.C A) ^ A + 2)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ _ _ _ _ d D T H hH p hp hD hT hcap N _ weight hweight hcorr
  let q := (p + A) ^ A
  have hq : 0 ≤ q := pow_nonneg (by positivity) _
  have hcost : p + q + 2 ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hqC : q ≤ (p + C) ^ C := by linarith
  let rho := Real.exp (-(2 * p + 1))
  have hrho : 0 < rho := Real.exp_pos _
  have hrhoinv : 1 / rho ≤ Real.exp ((p + 2) ^ 2) := by
    calc
      _ = Real.exp (2 * p + 1) := by simp only [rho, one_div, ← Real.exp_neg, neg_neg]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  let := D.metricSpace
  obtain ⟨n, hn, hnq, K, hK, ψ, hψ, hsum, hLip, hdiam⟩ :=
    hpartition D hp hD hrho hrhoinv
  let U (h : G) (i : Fin n) : D.Niltest (fun _ : Unit => 1) :=
    D.sectionNiltest (T h).orbit (fun z (_ : Unit) => ψ i z)
      (fun z _ => hψ i z) K (fun _ => hLip i) (some ())
  have hlog : Real.log (3 + (K : ℝ)) ≤ (p + C) ^ C := by
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    have h1 : 1 ≤ Real.exp q := Real.one_le_exp hq
    have h4 : (4 : ℝ) ≤ Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp (q + 2) := by
        rw [Real.exp_add]
        nlinarith [mul_le_mul_of_nonneg_left h4 (Real.exp_nonneg q)]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hU (h : G) (i : Fin n) : (U h i).orbit = (T h).orbit ∧ (U h i).normBound ≤ 1 ∧
      (U h i).UnitIntervalValued ∧ (U h i).ComplexityLE ((p + C) ^ C) := by
    refine ⟨rfl, le_rfl, ?_, ?_⟩
    · exact D.sectionNiltest_unit_interval _ _ _ _ _ _
    · exact D.sectionNiltest_complexityLE _ _ _ _ _ _ (hD.mono D hpC) hlog
  have hchoose (h : {h // h ∈ H}) : ∃ i : Fin n,
      Real.exp (-p) / (2 * Real.exp q) ≤
        ‖𝔼 x, weight h.val x * star ((U h.val i).evalCyclic N (fun _ => x))‖ := by
    obtain ⟨c, hc, happ⟩ := exists_complex_partition_approximation ψ
      (fun i z => (hψ i z).1) hsum hdiam (T h.val).observable
      (fun z => ((T h.val).norm_le z).trans (hcap h.val h.property)) (T h.val).lipschitz
    have hprecision : ((T h.val).lipBound : ℝ) * rho ≤ Real.exp (-p) / 2 := by
      have hbudgetT := Niltest.observable_budget (hT h.val h.property)
      have hlip : ((T h.val).lipBound : ℝ) ≤ Real.exp p := by
        have hnorm := (T h.val).normBound.coe_nonneg
        linarith
      calc
        _ ≤ Real.exp p * rho := mul_le_mul_of_nonneg_right hlip hrho.le
        _ = Real.exp (-p - 1) := by
          dsimp [rho]
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ _ := exp_sub_one_le_half_exp _
    obtain ⟨i, hi⟩ := exists_correlating_summand Finset.univ_nonempty (weight h.val)
      (fun x => (T h.val).evalCyclic N (fun _ => x))
      (fun i x => (U h.val i).evalCyclic N (fun _ => x) * c i)
      (Real.exp_pos (-p)) (Real.exp_pos q) (by simpa only [Fintype.card_fin] using hnq)
      (fun x _ => hweight h.val h.property x)
      (fun x _ => by
        rw [norm_sub_rev]
        exact (happ (D.cyclicOrbitPoint (T h.val).orbit N (fun _ => x))).trans hprecision)
      (hcorr h.val h.property)
    refine ⟨i, hi.trans ?_⟩
    have heq : finiteCorrelation Finset.univ (weight h.val)
        (fun x => (U h.val i).evalCyclic N (fun _ => x) * c i) =
        star (c i) * finiteCorrelation Finset.univ (weight h.val)
          (fun x => (U h.val i).evalCyclic N (fun _ => x)) := by
      simp only [finiteCorrelation, Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      simp only [star_mul]
      ring
    rw [heq, norm_mul, norm_star]
    exact (mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)).trans_eq (one_mul _)
  choose choice hchoice using hchoose
  let code : G → Fin n := fun h => if hh : h ∈ H then choice ⟨h, hh⟩ else ⟨0, hn⟩
  obtain ⟨i, _, H', hsub, hnonempty, hconstant, hdense⟩ :=
    exists_exponential_constant_fiber H hH code Set.univ (Set.toFinite _)
      (fun _ _ => Set.mem_univ _) (by simpa only [Set.ncard_univ, Nat.card_eq_fintype_card,
        Fintype.card_fin] using hnq)
  refine ⟨H', fun h => U h i, hsub, hnonempty, ?_, fun h => hU h i, fun _ _ => rfl, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    have hcode : choice ⟨h, hsub hh⟩ = i := by
      simpa only [code, dif_pos (hsub hh)] using hconstant h hh
    have hc := hchoice ⟨h, hsub hh⟩
    rw [hcode] at hc
    apply le_trans _ hc
    calc
      _ ≤ Real.exp (-(p + q) - 1) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ Real.exp (-(p + q)) / 2 := exp_sub_one_le_half_exp _
      _ = Real.exp (-p) / (2 * Real.exp q) := by
        rw [show -(p + q) = -p - q by ring, Real.exp_sub]
        ring

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProjectedNativeCoefficient
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def adaptedTranslateLinear (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h : σ → ℚ) :
    F.adaptedLieSubalgebra w →ₗ[ℚ] F.adaptedLieSubalgebra w :=
  ((VectorPolynomial.translate h).comp (F.adaptedLieSubalgebra w).incl.toLinearMap).codRestrict
    (F.adaptedLieSubalgebra w).toSubmodule (by
      intro p
      exact (F.mem_adaptedSubmodule w _).mpr
        (F.adapted_translate w hw h ((F.mem_adaptedSubmodule w _).mp p.property)))

@[simp] theorem adaptedTranslateLinear_coe (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h : σ → ℚ)
    (p : F.adaptedLieSubalgebra w) :
    (F.adaptedTranslateLinear w hw h p : VectorPolynomial σ ℚ L) = translate h p.val := rfl

theorem polynomialSymbolMap_adaptedTranslateLinear (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h : σ → ℚ)
    (p : F.adaptedLieSubalgebra w) :
    F.polynomialSymbolMap w (F.adaptedTranslateLinear w hw h p) = F.polynomialSymbolMap w p := by
  exact F.polynomialSymbolMap_translate w hw h p

theorem realPolynomialSymbolMap_translate (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h : σ → ℚ)
    (p : F.realification.adaptedLieSubalgebra w) :
    F.realPolynomialSymbolMap b ω hF w (F.realification.adaptedTranslateLinear w hw h p) =
      F.realPolynomialSymbolMap b ω hF w p := by
  apply sub_eq_zero.mp
  rw [← map_sub, F.realPolynomialSymbolMap_eq_zero_iff, map_sub, sub_eq_zero]
  exact F.realification.polynomialSymbolMap_adaptedTranslateLinear w hw h p

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem realFilteredPolynomialSymbolMap_extended (w : σ → ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ (F.realExtendedSymbolMap w x) =
      G.realExtendedSymbolMap w ((F.filteredPolynomialMap G φ hφ w).toLinearMap.baseChange ℝ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a p => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realFilteredPolynomialSymbolMap_polynomial
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (p : F.realification.adaptedLieSubalgebra w) :
    (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ
        (F.realPolynomialSymbolMap b ω hF w p) =
      G.realSymbolOfPolynomial c τ hG w
        (VectorPolynomial.map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) p.val) := by
  obtain ⟨x, rfl⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hF p
  change (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ
    (F.realSymbolOfPolynomial b ω hF w (F.realAdaptedPolynomialMap w x)) = _
  rw [F.realSymbolOfPolynomial_realAdaptedPolynomialMap,
    F.realFilteredPolynomialSymbolMap_extended,
    ← G.realSymbolOfPolynomial_realAdaptedPolynomialMap c τ hG,
    F.realFilteredPolynomialMap_polynomial]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {F : NilpotentLieFiltration L s} {w : σ → ℕ}

noncomputable def PolynomialOrbit.translate (g : F.PolynomialOrbit w)
    (hw : ∀ i, 0 < w i) (h : σ → ℤ) : F.PolynomialOrbit w :=
  polynomialOrbitOfLog (VectorPolynomial.translate (fun i => (h i : ℚ)) g.log)
    (F.adapted_translate w hw _ g.adapted)

@[simp] theorem polynomialOrbitEval_translate (g : F.PolynomialOrbit w)
    (hw : ∀ i, 0 < w i) (h x : σ → ℤ) :
    F.polynomialOrbitEval w x (g.translate hw h) = F.polynomialOrbitEval w (x + h) g := by
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.eval (fun i => (x i : ℚ))
      (VectorPolynomial.translate (fun i => (h i : ℚ)) g.log) =
    VectorPolynomial.eval (fun i => ((x + h) i : ℚ)) g.log
  rw [VectorPolynomial.eval_translate]
  simp only [Pi.add_apply, Int.cast_add]

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

noncomputable def integerOrbitPoint
    (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)) (n : ℤ) : D.Space :=
  QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
    (fun _ : Unit => 1) (fun _ => n) g)

@[simp] theorem cyclicOrbitPoint_translate
    (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (h : ℤ) (N : ℕ) [NeZero N] (x : ZMod N) :
    D.cyclicOrbitPoint (g.translate (fun _ => Nat.zero_lt_one) (fun _ => h)) N
      (fun _ : Unit => x) = D.integerOrbitPoint g ((x.val : ℤ) + h) := by
  unfold cyclicOrbitPoint integerOrbitPoint
  rw [NilpotentLieFiltration.polynomialOrbitEval_translate]
  rfl

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

noncomputable def nativeHorizontalCoefficientHom (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.associatedDegree.realification.PolynomialOrbit w →*
      Multiplicative (ℝ ⊗[ℚ] F.HigherHorizontal (Finsupp.weight w α)) :=
  (F.realHorizontalPolynomialHom hs b ω hF w α).comp
    (F.associatedDegree.realification.polynomialOrbitCoordinates w).toMonoidHom

@[simp] theorem nativeHorizontalCoefficientHom_apply (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ)
    (g : F.associatedDegree.realification.PolynomialOrbit w) :
    Multiplicative.toAdd (F.nativeHorizontalCoefficientHom hs b ω hF w α g) =
      (F.higherHorizontalSymbolCoefficient w α).baseChange ℝ
        (F.associatedDegree.realSymbolOfPolynomial b ω hF w g.log) := rfl

theorem nativeHorizontalCoefficientHom_tensor (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ)
    (g : F.associatedDegree.realification.PolynomialOrbit w)
    (x : ℝ ⊗[ℚ] F.associatedDegree.adaptedLieSubalgebra w)
    (hx : g.log = F.associatedDegree.realAdaptedPolynomialMap w x) :
    Multiplicative.toAdd (F.nativeHorizontalCoefficientHom hs b ω hF w α g) =
      (F.higherHorizontalCoefficient w α).baseChange ℝ x := by
  rw [F.nativeHorizontalCoefficientHom_apply, hx,
    F.associatedDegree.realSymbolOfPolynomial_realAdaptedPolynomialMap]
  exact F.realHorizontalSymbolCoefficient_extended w α x

theorem nativeHorizontalCoefficientHom_translate (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (α : σ →₀ ℕ)
    (g : F.associatedDegree.realification.PolynomialOrbit w) (h : σ → ℤ) :
    F.nativeHorizontalCoefficientHom hs b ω hF w α (g.translate hw h) =
      F.nativeHorizontalCoefficientHom hs b ω hF w α g := by
  change Multiplicative.ofAdd ((F.higherHorizontalSymbolCoefficient w α).baseChange ℝ
    (F.associatedDegree.realPolynomialSymbolMap b ω hF w
      (F.associatedDegree.realification.adaptedTranslateLinear w hw (fun i => (h i : ℚ))
        ⟨g.log, g.property⟩))) = _
  rw [F.associatedDegree.realPolynomialSymbolMap_translate]
  rfl

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def realSquarePairHom :
    F.squareFiltration.realification.Group →* (pi (fun _ : Bool => F)).realification.Group :=
  realificationMap (hnil := F.squareFiltration.lowerCentralSeries_eq_bot)
    (hM := (pi (fun _ : Bool => F)).lowerCentralSeries_eq_bot) F.squarePairMap

end Erdos3.NilpotentLieFiltration

namespace Erdos3

open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r) (F : NilpotentLieFiltration M t)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ k, φ x k ∈ G.layer d 1)

theorem projectedHorizontalSymbolCoefficient_native (hs : 1 ≤ s)
    (b : Basis ι ℚ M) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ L) (τ : κ → ℕ)
    (hG : ∀ j, G.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) (p : F.realification.adaptedLieSubalgebra w)
    (g : G.associatedDegree.realification.PolynomialOrbit w) (k : Fin 4)
    (hg : VectorPolynomial.map
      ((realificationLieHom ((liePiEval k).comp φ)).toLinearMap.restrictScalars ℚ) p.val = g.log) :
    (LinearMap.proj k).baseChange ℝ
        ((G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ
          (F.realPolynomialSymbolMap b ω hF w p)) =
      Multiplicative.toAdd (G.nativeHorizontalCoefficientHom hs c τ hG w α g) := by
  rw [G.real_projectedHorizontalSymbolCoefficient_component,
    G.nativeHorizontalCoefficientHom_apply]
  change (G.higherHorizontalSymbolCoefficient w α).baseChange ℝ
    ((F.filteredPolynomialSymbolMap G.associatedDegree ((liePiEval k).comp φ)
      (G.projectedComponent_mem_layer F φ hφ k) w).toLinearMap.baseChange ℝ
        (F.realPolynomialSymbolMap b ω hF w p)) = _
  rw [F.realFilteredPolynomialSymbolMap_polynomial G.associatedDegree ((liePiEval k).comp φ)
    (G.projectedComponent_mem_layer F φ hφ k) b ω hF c τ hG w p, hg]

end Erdos3.DegreeRankLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OptionMarkedSurjective
namespace OAI

section

universe u v

namespace Erdos3

open scoped TensorProduct

variable {ι : Type v} {L₀ M₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing M₀] [LieAlgebra ℚ M₀]
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}

namespace NilpotentLieFiltration

def optionFiltrations (F₀ : NilpotentLieFiltration L₀ s)
    (F : ∀ i, NilpotentLieFiltration (L i) s) :
    ∀ i : Option ι, NilpotentLieFiltration (optionLieSpace L₀ L i) s
  | none => F₀
  | some i => F i

@[simp] theorem optionFiltrations_none (F₀ : NilpotentLieFiltration L₀ s)
    (F : ∀ i, NilpotentLieFiltration (L i) s) : optionFiltrations F₀ F none = F₀ := rfl

@[simp] theorem optionFiltrations_some (F₀ : NilpotentLieFiltration L₀ s)
    (F : ∀ i, NilpotentLieFiltration (L i) s) (i : ι) :
    optionFiltrations F₀ F (some i) = F i := rfl

end NilpotentLieFiltration

def optionMarkedComponents (φ : L₀ →ₗ⁅ℚ⁆ M₀) :
    ∀ i : Option ι, (∀ j : Option ι, optionLieSpace L₀ L j) →ₗ⁅ℚ⁆
      optionLieSpace M₀ L i
  | none => φ.comp (liePiEval none)
  | some i => liePiEval (some i)

def optionMarkedLieMap (φ : L₀ →ₗ⁅ℚ⁆ M₀) :
    (∀ i : Option ι, optionLieSpace L₀ L i) →ₗ⁅ℚ⁆
      (∀ i : Option ι, optionLieSpace M₀ L i) :=
  liePiMap (optionMarkedComponents (L := L) φ)

@[simp] theorem optionMarkedLieMap_none (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    (x : ∀ i : Option ι, optionLieSpace L₀ L i) :
    optionMarkedLieMap φ x none = φ (x none) := rfl

@[simp] theorem optionMarkedLieMap_some (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    (x : ∀ i : Option ι, optionLieSpace L₀ L i) (i : ι) :
    optionMarkedLieMap φ x (some i) = x (some i) := rfl

theorem realification_optionMarkedLieMap_none (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    (x : ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i)) :
    realificationLieHom (liePiEval none) (realificationLieHom (optionMarkedLieMap φ) x) =
      realificationLieHom φ (realificationLieHom (liePiEval none) x) := by
  rw [optionMarkedLieMap, realification_liePiEval_liePiMap]
  induction x using TensorProduct.induction_on with
  | zero =>
    first
      | (simp; done)
      | (simp only [map_zero]; done)
      | (simp only [map_zero]; exact (map_zero (realificationLieHom φ)).symm)
  | tmul r x => rfl
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    exact (map_add (realificationLieHom φ) _ _).symm

theorem realification_optionMarkedLieMap_some (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    (x : ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i)) (i : ι) :
    realificationLieHom (liePiEval (some i))
        (realificationLieHom (optionMarkedLieMap φ) x) =
      realificationLieHom (liePiEval (some i)) x := by
  rw [optionMarkedLieMap, realification_liePiEval_liePiMap]
  rfl

open NilpotentLieFiltration

theorem optionMarkedLieMap_mem_layer (F₀ : NilpotentLieFiltration L₀ s)
    (G₀ : NilpotentLieFiltration M₀ s) (F : ∀ i, NilpotentLieFiltration (L i) s)
    (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    (hφ : ∀ n x, x ∈ F₀.layer n → φ x ∈ G₀.layer n)
    (n : ℕ) (x : ∀ i : Option ι, optionLieSpace L₀ L i)
    (hx : x ∈ (pi (optionFiltrations F₀ F)).layer n) :
    optionMarkedLieMap φ x ∈ (pi (optionFiltrations G₀ F)).layer n := by
  apply (mem_pi_layer _ _ _).mpr
  intro i
  cases i with
  | none => exact hφ n _ ((mem_pi_layer _ _ _).mp hx none)
  | some i => exact (mem_pi_layer _ _ _).mp hx (some i)

variable [Fintype ι] [DecidableEq ι]

theorem realBCHPiEquiv_optionMarkedLieMap_none
    (F₀ : NilpotentLieFiltration L₀ s) (G₀ : NilpotentLieFiltration M₀ s)
    (F : ∀ i, NilpotentLieFiltration (L i) s) (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    (g : (pi (optionFiltrations F₀ F)).realification.Group) :
    realBCHPiEquiv (optionFiltrations G₀ F)
        (NilpotentLieBCHGroup.realificationMap
          (hnil := (pi (optionFiltrations F₀ F)).lowerCentralSeries_eq_bot)
          (hM := (pi (optionFiltrations G₀ F)).lowerCentralSeries_eq_bot)
          (optionMarkedLieMap φ) g) none =
      NilpotentLieBCHGroup.realificationMap
        (hnil := F₀.lowerCentralSeries_eq_bot) (hM := G₀.lowerCentralSeries_eq_bot)
        φ (realBCHPiEquiv (optionFiltrations F₀ F) g none) := by
  apply NilpotentLieBCHGroup.ext
  exact realification_optionMarkedLieMap_none φ g.coord

theorem realBCHPiEquiv_optionMarkedLieMap_some
    (F₀ : NilpotentLieFiltration L₀ s) (G₀ : NilpotentLieFiltration M₀ s)
    (F : ∀ i, NilpotentLieFiltration (L i) s) (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    (g : (pi (optionFiltrations F₀ F)).realification.Group) (i : ι) :
    realBCHPiEquiv (optionFiltrations G₀ F)
        (NilpotentLieBCHGroup.realificationMap
          (hnil := (pi (optionFiltrations F₀ F)).lowerCentralSeries_eq_bot)
          (hM := (pi (optionFiltrations G₀ F)).lowerCentralSeries_eq_bot)
          (optionMarkedLieMap φ) g) (some i) =
      realBCHPiEquiv (optionFiltrations F₀ F) g (some i) := by
  apply NilpotentLieBCHGroup.ext
  exact realification_optionMarkedLieMap_some φ g.coord i

end Erdos3

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {Pivot : Type v} [Fintype Pivot]
    {L M : Type u} {Partner : Pivot → Type u}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [∀ a, LieRing (Partner a)] [∀ a, LieAlgebra ℚ (Partner a)]
    {s dL dM : ℕ} {d : Pivot → ℕ}
    (D : RationalFilteredNilmanifold L s dL)
    (Q : RationalFilteredNilmanifold M s dM)
    (E : ∀ a, RationalFilteredNilmanifold (Partner a) s (d a))
    (φ : L →ₗ⁅ℚ⁆ M)

theorem optionMarkedLieMap_native_logHeight {p : ℝ} (hp : 0 ≤ p)
    (hφ : ∀ i j, rationalLogHeight (Q.basis.repr (φ (D.basis j)) i) ≤ p) :
    ∀ i j, rationalLogHeight ((optionProduct Q E).basis.repr
      (optionMarkedLieMap (L := Partner) φ ((optionProduct D E).basis j)) i) ≤ p := by
  classical
  intro i j
  dsimp only [optionProduct]
  rw [productFinBasis_repr]
  generalize hz :
    (Fintype.equivFin (Σ a : Option Pivot, Fin (optionDimension dM d a))).symm i = z
  rcases z with ⟨a, k⟩
  cases a with
  | none =>
    change rationalLogHeight (Q.basis.repr
      (φ (productFinBasis (optionFactors D E) j none)) k) ≤ p
    rw [productFinBasis, Basis.reindex_apply]
    generalize hy :
      (Fintype.equivFin (Σ a : Option Pivot, Fin (optionDimension dL d a))).symm j = y
    rcases y with ⟨b, l⟩
    rw [Pi.basis_apply]
    cases b with
    | none =>
      rw [Pi.single_eq_same]
      exact hφ k l
    | some b =>
      rw [Pi.single_eq_of_ne (by simp : (none : Option Pivot) ≠ some b)]
      change rationalLogHeight (Q.basis.repr (φ (0 : L)) k) ≤ p
      rw [map_zero, map_zero]
      change rationalLogHeight (0 : ℚ) ≤ p
      simpa [rationalLogHeight] using hp
  | some a =>
    change rationalLogHeight ((E a).basis.repr
      (liePiEval (R := ℚ) (some a) ((optionProduct D E).basis j)) k) ≤ p
    exact rationalLogHeight_le_of_height
      (productProjection_matrix_height (optionFactors D E) (some a) j k)
      (by simpa only [Nat.cast_one] using Real.one_le_exp_iff.mpr hp)

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

theorem optionMarkedLieMap_piRealOrbit_log
    {ι : Type v} [Fintype ι] {L₀ M₀ : Type u} {L : ι → Type u}
    [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing M₀] [LieAlgebra ℚ M₀]
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
    {s d₀ e₀ : ℕ} {d : ι → ℕ} {σ : Type*} {w : σ → ℕ}
    (D₀ : RationalFilteredNilmanifold L₀ s d₀)
    (Q₀ : RationalFilteredNilmanifold M₀ s e₀)
    (E : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (φ : L₀ →ₗ⁅ℚ⁆ M₀)
    (g : ∀ i, (optionFactors D₀ E i).filtration.realification.PolynomialOrbit w)
    (h : ∀ i, (optionFactors Q₀ E i).filtration.realification.PolynomialOrbit w)
    (hnone : VectorPolynomial.map
      ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) (g none).log =
        (h none).log)
    (hsome : ∀ i, (g (some i)).log = (h (some i)).log) :
    VectorPolynomial.map
      ((realificationLieHom (optionMarkedLieMap φ)).toLinearMap.restrictScalars ℚ)
      (piRealOrbit (fun i => (optionFactors D₀ E i).filtration) g).log =
        (piRealOrbit (fun i => (optionFactors Q₀ E i).filtration) h).log := by
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [coefficients_map]
  apply ((Pi.basis (fun i => (optionFactors Q₀ E i).basis)).baseChange ℝ).repr.injective
  ext ⟨i, k⟩
  rw [realification_pi_basis_repr, realification_pi_basis_repr]
  change ((optionFactors Q₀ E i).basis.baseChange ℝ).repr
    (realificationLieHom (liePiEval i)
      (realificationLieHom (optionMarkedLieMap φ)
        (coefficients (piRealOrbit (fun i => (optionFactors D₀ E i).filtration) g).log α))) k =
    ((optionFactors Q₀ E i).basis.baseChange ℝ).repr
      (realificationLieHom (liePiEval i)
        (coefficients (piRealOrbit (fun i => (optionFactors Q₀ E i).filtration) h).log α)) k
  rw [piRealOrbit_coefficient]
  cases i with
  | none =>
    rw [realification_optionMarkedLieMap_none, piRealOrbit_coefficient]
    have hα := congrArg (fun q => coefficients q α) hnone
    erw [coefficients_map] at hα
    exact congrArg (fun x => (Q₀.basis.baseChange ℝ).repr x k) hα
  | some i =>
    rw [realification_optionMarkedLieMap_some, piRealOrbit_coefficient]
    exact congrArg (fun q => ((E i).basis.baseChange ℝ).repr (coefficients q α) k)
      (hsome i)

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3

variable {J : Type v} {L Y : Type u} {M : J → Type u}
    [LieRing L] [LieAlgebra ℚ L] [LieRing Y] [LieAlgebra ℚ Y]
    [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonPivotQuotientTop
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

section Product

variable {L W : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing W] [LieAlgebra ℚ W] {s : ℕ}

def prod (F : NilpotentLieFiltration L s) (P : NilpotentLieFiltration W s) :
    NilpotentLieFiltration (L × W) s where
  layer j := (F.layer j).prod (P.layer j)
  antitone := by
    intro i j hij x hx
    exact ⟨F.antitone hij hx.1, P.antitone hij hx.2⟩
  one_eq_top := by rw [F.one_eq_top, P.one_eq_top, Submodule.prod_top]
  lie_mem := by
    intro i j x y hx hy
    exact ⟨F.lie_mem hx.1 hy.1, P.lie_mem hx.2 hy.2⟩
  terminal := by rw [F.terminal, P.terminal, Submodule.prod_bot]

@[simp] theorem prod_layer (F : NilpotentLieFiltration L s)
    (P : NilpotentLieFiltration W s) (j : ℕ) :
    (F.prod P).layer j = (F.layer j).prod (P.layer j) := rfl

@[simp] theorem mem_prod_layer (F : NilpotentLieFiltration L s)
    (P : NilpotentLieFiltration W s) (j : ℕ) (x : L × W) :
    x ∈ (F.prod P).layer j ↔ x.1 ∈ F.layer j ∧ x.2 ∈ P.layer j := Iff.rfl

end Product

variable {L Y W J : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing Y] [LieAlgebra ℚ Y] [LieRing W] [LieAlgebra ℚ W] {s : ℕ}
  (F : NilpotentLieFiltration L s) (π : L →ₗ⁅ℚ⁆ Y)
  (eta : J → L →ₗ[ℚ] ℚ) (js : List J)

noncomputable def pivotQuotientFiltration :
    NilpotentLieFiltration (L ⧸ F.pivotAnnihilatorIdeal π eta js) s :=
  F.quotientLie (F.pivotAnnihilatorIdeal π eta js) (by rw [F.terminal]; exact bot_le)

@[simp] theorem pivotQuotientFiltration_layer (j : ℕ) :
    (F.pivotQuotientFiltration π eta js).layer j =
      (F.layer j).map (lieQuotientMap (F.pivotAnnihilatorIdeal π eta js)).toLinearMap := rfl

noncomputable def pivotProductQuotientFiltration (P : NilpotentLieFiltration W s) :
    NilpotentLieFiltration ((L ⧸ F.pivotAnnihilatorIdeal π eta js) × W) s :=
  (F.pivotQuotientFiltration π eta js).prod P

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

theorem frequency_zero_on_refilteredLayer_of_real
    {V : Type*} [LieRing V] [LieAlgebra ℚ V] {s : ℕ}
    (H : NilpotentLieFiltration V s) (U : LieSubalgebra ℚ H.AssociatedGraded)
    (η : V →ₗ[ℚ] ℚ) (k : ℕ)
    (hzero : ∀ x ∈ H.realGradedRefiltrationLayer U k, realifyFunctional η x = 0)
    (x : V) (hx : x ∈ H.gradedRefiltrationLayer U k) : η x = 0 := by
  have hz := hzero ((1 : ℝ) ⊗ₜ[ℚ] x) (Submodule.tmul_mem_baseChange_of_mem 1 hx)
  simp only [realifyFunctional_tmul, one_mul] at hz
  exact_mod_cast hz

variable {L V Y J κ κQ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing V] [LieAlgebra ℚ V] [LieRing Y] [LieAlgebra ℚ Y] {s : ℕ}
  (F : NilpotentLieFiltration L s) (P : NilpotentLieFiltration V s)
  (π : L →ₗ⁅ℚ⁆ Y) (eta : J → L →ₗ[ℚ] ℚ) (js : List J)
  (partner : J → V →ₗ[ℚ] ℚ)
  (U : LieSubalgebra ℚ (F.prod P).AssociatedGraded)

variable
  (hzero : ∀ j ∈ js, ∀ x ∈ (F.prod P).realGradedRefiltrationLayer U s,
    realifyFunctional ((eta j).comp (LinearMap.fst ℚ L V) +
      (partner j).comp (LinearMap.snd ℚ L V)) x = 0)

variable (e : Basis κ ℚ (L × V)) (μ : κ → ℕ)
  (hH : ∀ k, (F.prod P).layer k = Submodule.span ℚ (e '' {i | k ≤ μ i}))
  (q : Basis κQ ℚ ((L ⧸ F.pivotAnnihilatorIdeal π eta js) × V)) (ν : κQ → ℕ)
  (hQ : ∀ k, (F.pivotProductQuotientFiltration π eta js P).layer k =
    Submodule.span ℚ (q '' {i | k ≤ ν i}))
  (hU : BasisGradedSubmodule ((F.prod P).associatedGradedBasis e μ hH) μ U.toSubmodule)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestVerticalBounds
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem exists_controlled_adapted_basis {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ) (N : ℕ),
      Monotone w ∧ IsCentralLieBasis b ∧
      (∀ i, D.filtration.layer i = Submodule.span ℚ (b '' {j | i ≤ w j})) ∧
      (∀ j i, rationalLogHeight (D.basis.repr (b j) i) ≤ p + 1) ∧
      (∀ i j, rationalLogHeight (b.repr (D.basis i) j) ≤ (p + 3) ^ 5) ∧
      (∀ i j k, rationalLogHeight (lieStructureConstants b i j k) ≤ (p + 3) ^ 11) ∧
      0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 3) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b D.lattice ∧
      bchSubgroupCoordinates b D.lattice ⊆ denominatorGrid N := by
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHp : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hp1 : 0 ≤ p + 1 := by linarith
  have hdp : (Fintype.card (Fin d) : ℝ) ≤ p + 1 := by
    simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 1 by linarith)
  have hlp : (D.grid : ℝ) ≤ Real.exp (p + 1) :=
    hD.2.1.trans (Real.exp_le_exp.mpr (by linarith))
  obtain ⟨b, w, N, hw, hc, hlayers, hb, hbinv, hbracket, hN, hNp, hin, hout⟩ :=
    D.filtration.exists_adapted_basis_and_grid D.basis (fun i => D.layerBasis i)
      (fun i => (D.layerBasis i).span_eq) D.lattice hH D.grid_pos
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.2 i j k))
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
      D.inner_grid D.outer_grid hp1 hdp hHp hlp
  have hdr : (finrank ℚ L : ℝ) ≤ p + 1 := by
    simpa only [finrank_eq_card_basis D.basis] using hdp
  have hshift : p + 1 + 2 = p + 3 := by ring
  have hinvBudget : (rationalSolveHeight (finrank ℚ L) H : ℝ) ≤ Real.exp ((p + 3) ^ 5) := by
    simpa only [hshift] using rationalSolveHeight_le_budget (finrank ℚ L) H hp1 hdr hHp
  refine ⟨b, w, N, hw, hc, hlayers, ?_, ?_, ?_, hN, ?_, hin, hout⟩
  · exact fun j i => rationalLogHeight_le_of_height (hb j i) hHp
  · exact fun i j => rationalLogHeight_le_of_height (hbinv i j) hinvBudget
  · intro i j k
    apply (rationalLogHeight_le_iff _ _).mpr
    simpa only [hshift] using hbracket i j k
  · simpa only [hshift] using hNp

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_controlled_central_actions {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    letI := D.metricSpace
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ) (N : ℕ),
      (∀ i, D.filtration.layer i = Submodule.span ℚ (b '' {j | i ≤ w j})) ∧
      (∀ j i, rationalLogHeight (D.basis.repr (b j) i) ≤ p + 1) ∧
      (∀ i j, rationalLogHeight (b.repr (D.basis i) j) ≤ (p + 3) ^ 5) ∧
      0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 3) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b D.lattice ∧
      bchSubgroupCoordinates b D.lattice ⊆ denominatorGrid N ∧
      ∃ A : {j // s ≤ w j} → CircleFourier.IsometricCircleAction D.Space,
        (∀ i j, (A i).Commutes (A j)) ∧
        (∀ j (t : CircleFourier.Circle) x,
          dist ((A j).act t x) x ≤ Real.exp ((p + 3) ^ 9 + 2 * p + 2) * ‖t‖) ∧
        ∀ j (r : ℝ) x, (A j).act (r : CircleFourier.Circle) x =
          realBCHLine (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
            ((N : ℝ) • (b.baseChange ℝ) j) r • x := by
  let := D.metricSpace
  obtain ⟨b, w, N, _, _, hlayers, hb, hbinv, _, hN, hNb, hin, hout⟩ :=
    D.exists_controlled_adapted_basis hp hD
  have hcentral (j : {j // s ≤ w j}) (z : L) : ⁅b j, z⁆ = 0 := by
    apply D.filtration.top_layer_central
    rw [hlayers s]
    exact Submodule.subset_span ⟨j, j.property, rfl⟩
  let A : {j // s ≤ w j} → CircleFourier.IsometricCircleAction D.Space := fun j =>
    realifiedCentralBasisAction D.basis b D.lattice D.grid D.grid_pos D.outer_grid N hin j (hcentral j)
  have hbabs (j : Fin (finrank ℚ L)) (i : Fin d) :
      |(D.basis.repr (b j) i : ℝ)| ≤ Real.exp (p + 2) := by
    have hh := (rationalHeightLE_ceil_exp (hb j i)).abs_real_le
    have hceil := ceil_exp_le_exp_add_one (show 0 ≤ p + 1 by linarith)
    exact hh.trans (by simpa only [show p + 1 + 1 = p + 2 by ring] using hceil)
  have hcost : ((d : ℝ) + 1) * ((N : ℝ) * Real.exp (p + 2)) ≤
      Real.exp ((p + 3) ^ 9 + 2 * p + 2) := by
    have hd : (d : ℝ) + 1 ≤ Real.exp p :=
      (by linarith [hD.1] : (d : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)
    calc
      _ ≤ Real.exp p * (Real.exp ((p + 3) ^ 9) * Real.exp (p + 2)) := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  refine ⟨b, w, N, hlayers, hb, hbinv, hN, hNb, hin, hout, A, ?_, ?_, ?_⟩
  · intro i j
    exact realifiedCentralBasisAction_commutes D.basis b D.lattice D.grid D.grid_pos D.outer_grid
      N hin i j (hcentral i) (hcentral j)
  · intro j t x
    have hh := realifiedCentralBasisAction_displacement D.basis b D.lattice D.grid D.grid_pos D.outer_grid
      N hin j (hcentral j) (Real.exp_nonneg (p + 2)) (hbabs j) t x
    simp only [Fintype.card_fin] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hcost (norm_nonneg t))
  · intro j r x
    exact realifiedCentralBasisAction_act_coe D.basis b D.lattice D.grid D.grid_pos D.outer_grid
      N hin j (hcentral j) r x

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct BigOperators NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_controlled_vertical_decomposition {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) :
    letI := D.metricSpace
    ∀ (f : D.Space → ℂ) (K B : ℝ≥0), LipschitzWith K f → (∀ x, ‖f x‖ ≤ B) →
      (K : ℝ) ≤ Real.exp p → ∀ δ : ℝ, 0 < δ → δ⁻¹ ≤ Real.exp p →
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (η : J → L →ₗ[ℚ] ℚ) (v : J → D.Space → ℂ),
      (Fintype.card J : ℝ) ≤ Real.exp (verticalDecompositionBudget p) ∧
      (∀ j i, rationalLogHeight (η j (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ j, LipschitzWith K (v j) ∧ (∀ x, ‖v j x‖ ≤ B)) ∧
      (∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
        v j (z • x) = character ((realifyFunctional (η j) z.coord : ℝ) : CircleFourier.Circle) * v j x) ∧
      (∀ (z : D.RealGroup) (c : ℂ), (∀ x, f (z • x) = c * f x) →
        ∀ j x, v j (z • x) = c * v j x) ∧
      ∀ x, ‖(∑ j, v j x) - f x‖ ≤ δ := by
  classical
  let := D.metricSpace
  intro f K B hf hb hK δ hδ hδp
  obtain ⟨b, w, N, hlayers, _, hbinv, hN, hNp, _, _, A, hcomm, horbit, hact⟩ :=
    D.exists_controlled_central_actions hp hD
  let S : Set (Fin (finrank ℚ L)) := {j | s ≤ w j}
  let q := centralActionBudget p
  have hq : 0 ≤ q := centralActionBudget_nonneg hp
  have hpq : p ≤ q := le_centralActionBudget hp
  have hd : (Fintype.card S : ℝ) ≤ p := by
    apply (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans
    simpa only [Fintype.card_fin, finrank_eq_card_basis D.basis] using hD.1
  let O : ℝ≥0 := ⟨Real.exp q, (Real.exp_pos q).le⟩
  obtain ⟨J, inst, ν, v, hcard, hν, hv, hchar, hpres, herr⟩ :=
    exists_controlled_commuting_circle_decomposition A hcomm f K B O hf hb horbit δ q hδ hq
      (hd.trans hpq) (hK.trans (Real.exp_le_exp.mpr hpq)) le_rfl
      (hδp.trans (Real.exp_le_exp.mpr hpq))
  let η : J → L →ₗ[ℚ] ℚ := fun j => basisFrequency b S N (ν j)
  let R : ℝ := (2 * q + 2) ^ 4 + q + (p + 3) ^ 5
  have hpow : 0 ≤ (p + 3) ^ 5 := by positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hqR : q ≤ R := by dsimp [R]; nlinarith [sq_nonneg ((2 * q + 2) ^ 2)]
  have hfreq : (2 * q + 2) ^ 4 ≤ R := by dsimp [R]; linarith
  have hbas : (p + 3) ^ 5 ≤ R := by dsimp [R]; nlinarith [sq_nonneg ((2 * q + 2) ^ 2)]
  have hNq : (p + 3) ^ 9 ≤ q := by dsimp [q, centralActionBudget]; linarith
  have hterm : 2 * q * (2 * q + 2) ^ 4 ≤ verticalDecompositionBudget p := by
    change _ ≤ _ + (R + 2) ^ 4
    exact le_add_of_nonneg_right (by positivity)
  have hheight : (R + 2) ^ 4 ≤ verticalDecompositionBudget p := by
    change _ ≤ 2 * q * (2 * q + 2) ^ 4 + _
    have h : 0 ≤ 2 * q * (2 * q + 2) ^ 4 := by positivity
    linarith
  have hcentral (i : S) (z : L) : ⁅b i, z⁆ = 0 := by
    apply D.filtration.top_layer_central
    rw [hlayers s]
    exact Submodule.subset_span ⟨i, i.property, rfl⟩
  have hucentral (i : S) (z : ℝ ⊗[ℚ] L) : ⁅(N : ℝ) • b.baseChange ℝ i, z⁆ = 0 :=
    scaled_real_basis_central b i (hcentral i) N z
  refine ⟨J, inst, η, v, hcard.trans (Real.exp_le_exp.mpr hterm), ?_, hv, ?_, ?_, herr⟩
  · intro j i
    exact (basisFrequency_logHeight_le D.basis b S N hN (ν j) hR (hd.trans (hpq.trans hqR))
      (hNp.trans (Real.exp_le_exp.mpr (hNq.trans hqR)))
      (fun a => (hν j a).trans (Real.exp_le_exp.mpr hfreq))
      (fun a c => (hbinv a c).trans hbas) i).trans hheight
  · intro j z hz x
    apply central_span_character (fun i : S => (N : ℝ) • b.baseChange ℝ i) hucentral
      (realifyFunctional (η j)) (v j) ?_ ?_ x
    · intro i r y
      have h := hchar j i (r : CircleFourier.Circle) y
      rw [hact] at h
      change _ = character ((r * realifyFunctional (basisFrequency b S N (ν j))
        ((N : ℝ) • b.baseChange ℝ i) : ℝ) : CircleFourier.Circle) * _
      rw [realify_basisFrequency_direction b S N hN (ν j) i]
      simpa only [← AddCircle.coe_zsmul, zsmul_eq_mul, mul_comm] using h
    · exact D.filtration.realLayer_le_span_scaled_basis b s S (hlayers s) N hN hz
  · intro z c hc
    apply hpres (fun x => z • x) c ?_ hc
    intro i t x
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
    rw [hact, hact, ← mul_smul, ← mul_smul]
    rw [(realBCHLine_commute _ (hucentral i) r z).eq]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieFiltration

noncomputable def squareGeometryBudget (p : ℝ) : ℝ :=
  ((p + 3) ^ 11 + 2 * p + 5) ^ 11

theorem squareGeometryBudget_nonneg {p : ℝ} (hp : 0 ≤ p) : 0 ≤ squareGeometryBudget p := by
  unfold squareGeometryBudget
  positivity

namespace RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem exists_controlled_square_geometry {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ)
      (hlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis b w (hlayers 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b w (hlayers 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p + 1) ∧
      (D.filtration.squareFiltration.ofAdaptedBasis
        (D.filtration.squareFinBasis b w (hlayers 2)) (squareFinWeight w)
        (D.filtration.squareFinBasis_layers b w hlayers)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE
          (squareGeometryBudget p) := by
  obtain ⟨b, w, l, _, _, hlayers, hb, _, hc, hl, hlp, hin, hout⟩ :=
    D.exists_controlled_adapted_basis hp hD
  let q : ℝ := (p + 3) ^ 11 + 2 * p + 3
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqbr : (p + 3) ^ 11 + 1 ≤ q := by dsimp [q]; linarith
  have hdim : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ p := by
    simpa only [Fintype.card_fin, finrank_eq_card_basis D.basis] using hD.1
  have h2dim : 2 * (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ q := by
    have hpow : 0 ≤ (p + 3) ^ 11 := by positivity
    dsimp [q]
    linarith
  have hH : (⌈Real.exp ((p + 3) ^ 11)⌉₊ : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one (by positivity)).trans (Real.exp_le_exp.mpr hqbr)
  have hgrid : (l : ℝ) ≤ Real.exp q := by
    apply hlp.trans (Real.exp_le_exp.mpr _)
    have hpow := pow_le_pow_right₀ (by linarith : 1 ≤ p + 3) (by decide : 9 ≤ 11)
    dsimp [q]
    linarith
  obtain ⟨N, hN, hinner, houter, hgeom⟩ := D.filtration.exists_square_rational_model
    b w hlayers D.lattice hl (one_le_ceil_exp _)
    (fun i j k => rationalHeightLE_ceil_exp (hc i j k)) hin hout hq h2dim hH hgrid
  refine ⟨b, w, hlayers, N, hN, hinner, houter, hb, ?_⟩
  have he : q + 2 = (p + 3) ^ 11 + 2 * p + 5 := by dsimp [q]; ring
  simpa only [he, squareGeometryBudget] using hgeom

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_controlled_vertical_decomposition (T : D.Niltest w)
    {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p)
    (δ : ℝ) (hδ : 0 < δ) (hδp : δ⁻¹ ≤ Real.exp p) :
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (η : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest w),
      (Fintype.card J : ℝ) ≤ Real.exp (verticalDecompositionBudget p) ∧
      (∀ j i, rationalLogHeight (η j (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ j, (U j).ComplexityLE p ∧ (U j).orbit = T.orbit) ∧
      (∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
        (U j).observable (z • x) =
          character ((realifyFunctional (η j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x) ∧
      (∀ j, (∃ x, (U j).observable x ≠ 0) → ∀ z : D.RealGroup,
        z ∈ D.filtration.realification.subgroup s → z ∈ D.realLattice →
          ∃ n : ℤ, realifyFunctional (η j) z.coord = n) ∧
      (∀ (z : D.RealGroup) (c : ℂ), (∀ x, T.observable (z • x) = c * T.observable x) →
        ∀ j x, (U j).observable (z • x) = c * (U j).observable x) ∧
      (∀ x, ‖(∑ j, (U j).observable x) - T.observable x‖ ≤ δ) ∧
      ∀ x : σ → ℤ, ‖(∑ j, (U j).eval x) - T.eval x‖ ≤ δ := by
  let := D.metricSpace
  have hK : (T.lipBound : ℝ) ≤ Real.exp p := by
    have h := observable_budget hT
    have hB := T.normBound.coe_nonneg
    linarith
  obtain ⟨J, inst, η, v, hcard, hheight, hv, hchar, hpres, herr⟩ :=
    D.exists_controlled_vertical_decomposition hp hT.1 T.observable T.lipBound T.normBound
      T.lipschitz T.norm_le hK δ hδ hδp
  let U : J → D.Niltest w := fun j =>
    { orbit := T.orbit
      observable := v j
      normBound := T.normBound
      lipBound := T.lipBound
      norm_le := (hv j).2
      lipschitz := (hv j).1 }
  refine ⟨J, inst, η, U, hcard, hheight, fun j => ⟨hT, rfl⟩, hchar, ?_, hpres, herr, ?_⟩
  · intro j hne z hz hΓ
    exact vertical_frequency_integral_on_lattice D.filtration D.realLattice (η j) (v j)
      (hchar j) hne z hz hΓ
  · intro x
    exact herr (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x T.orbit))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_vertical_decomposition_preserving_bounds (T : D.Niltest w)
    {p rho : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p) (hrho : 0 < rho)
    (hrhop : rho⁻¹ ≤ Real.exp p) :
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (eta : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest w),
      (Fintype.card J : ℝ) ≤ Real.exp (verticalDecompositionBudget p) ∧
      (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ j, (U j).ComplexityLE p ∧ (U j).orbit = T.orbit ∧
        (U j).normBound = T.normBound ∧ (U j).lipBound = T.lipBound) ∧
      (∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
        (U j).observable (z • x) =
          character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x) ∧
      (∀ j, (∃ x, (U j).observable x ≠ 0) → ∀ z : D.RealGroup,
        z ∈ D.filtration.realification.subgroup s → z ∈ D.realLattice →
          ∃ n : ℤ, realifyFunctional (eta j) z.coord = n) ∧
      (∀ x, ‖(∑ j, (U j).observable x) - T.observable x‖ ≤ rho) ∧
      ∀ x : σ → ℤ, ‖(∑ j, (U j).eval x) - T.eval x‖ ≤ rho := by
  let := D.metricSpace
  have hK : (T.lipBound : ℝ) ≤ Real.exp p := by
    have h := observable_budget hT
    have hB := T.normBound.coe_nonneg
    linarith
  obtain ⟨J, inst, eta, v, hcard, hheight, hv, hchar, _, herr⟩ :=
    D.exists_controlled_vertical_decomposition hp hT.1 T.observable T.lipBound T.normBound
      T.lipschitz T.norm_le hK rho hrho hrhop
  let U : J → D.Niltest w := fun j =>
    { orbit := T.orbit
      observable := v j
      normBound := T.normBound
      lipBound := T.lipBound
      norm_le := (hv j).2
      lipschitz := (hv j).1 }
  refine ⟨J, inst, eta, U, hcard, hheight, fun _ => ⟨hT, rfl, rfl, rfl⟩, hchar, ?_, herr, ?_⟩
  · intro j hne z hz hGamma
    exact vertical_frequency_integral_on_lattice D.filtration D.realLattice (eta j) (v j)
      (hchar j) hne z hz hGamma
  · intro x
    exact herr (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x T.orbit))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PivotAnnihilatorFrequencyCode
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open Module
open scoped Classical

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]

def frequencyCodeKernel (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ)
    {D : ℕ} (code : Fin D → Option J) : Submodule ℚ V :=
  finiteFrequencyKernel P (fun i => (code i).elim 0 eta) (List.finRange D)

theorem mem_frequencyCodeKernel (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ)
    {D : ℕ} (code : Fin D → Option J) (v : V) :
    v ∈ frequencyCodeKernel P eta code ↔ v ∈ P ∧
      ∀ i j, code i = some j → eta j v = 0 := by
  simp only [frequencyCodeKernel, mem_finiteFrequencyKernel, List.mem_finRange, forall_true_left]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro h i j hij
    simpa only [hij, Option.elim_some] using h i
  · intro h i
    cases hi : code i with
    | none => simp
    | some j => simpa only [Option.elim_some] using h i j hi

theorem exists_frequency_basis_code [FiniteDimensional ℚ V]
    (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ) (js : List J) :
    ∃ code : Fin (finrank ℚ P) → Option J,
      (∀ i j, code i = some j → j ∈ js) ∧
      finiteFrequencyKernel P eta js = frequencyCodeKernel P eta code := by
  obtain ⟨m, hm, index, hindex, hlin, hspan⟩ := exists_restricted_frequency_basis P eta js
  let code : Fin (finrank ℚ P) → Option J := fun i =>
    if hi : i.val < m then some (index ⟨i.val, hi⟩) else none
  have hkernel : finiteFrequencyKernel P eta js =
      finiteFrequencyKernel P (fun i => eta (index i)) (List.finRange m) := by
    apply finiteFrequencyKernel_eq_of_span_eq
    rw [restrictedFrequencySpan_finRange]
    exact hspan.symm
  refine ⟨code, ?_, ?_⟩
  · intro i j hij
    dsimp only [code] at hij
    split_ifs at hij with hi
    · cases hij
      exact hindex _
  · rw [hkernel]
    ext v
    rw [mem_finiteFrequencyKernel, mem_frequencyCodeKernel]
    simp only [List.mem_finRange, forall_true_left]
    refine and_congr_right (fun _ => ?_)
    constructor
    · intro h i j hij
      dsimp only [code] at hij
      split_ifs at hij with hi
      · cases hij
        exact h _
    · intro h i
      let k : Fin (finrank ℚ P) := ⟨i.val, lt_of_lt_of_le i.isLt hm⟩
      apply h k (index i)
      simp only [code, k, i.isLt, dite_true]

theorem exists_common_frequency_kernel [FiniteDimensional ℚ V]
    {Ω : Type*} [Fintype Ω] [Fintype J]
    (law : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ) (js : Ω → List J) :
    ∃ (code : Fin (finrank ℚ P) → Option J) (retained : Finset Ω),
      retained ⊆ productive ∧
      law.mass productive / (Fintype.card J + 1) ^ finrank ℚ P ≤ law.mass retained ∧
      ∀ a ∈ retained, (∀ i j, code i = some j → j ∈ js a) ∧
        finiteFrequencyKernel P eta (js a) = frequencyCodeKernel P eta code := by
  choose code hmem hkernel using fun a => exists_frequency_basis_code P eta (js a)
  obtain ⟨c, hc⟩ := law.exists_code_fiber_mass productive code
  refine ⟨c, productive.filter (fun a => code a = c), Finset.filter_subset _ _, ?_, ?_⟩
  · have hcard : (Fintype.card (Fin (finrank ℚ P) → Option J) : ℝ) =
        (Fintype.card J + 1 : ℝ) ^ finrank ℚ P := by simp
    rw [hcard] at hc
    convert hc using 1; try rfl
    congr 1
    ext a
    simp only [Finset.mem_filter]
  · intro a ha
    have he := (Finset.mem_filter.mp ha).2
    rw [← he]
    exact ⟨hmem a, hkernel a⟩

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open Module
open scoped Classical TensorProduct

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L Y J : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing Y] [LieAlgebra ℚ Y] {s n : ℕ}
  (F : NilpotentLieFiltration L s) (π : L →ₗ⁅ℚ⁆ Y)
  (eta : J → L →ₗ[ℚ] ℚ) (code : Fin n → Option J)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelProjectionPresentPivotIdeal
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct Classical

def KernelProjectionPresentPivot {J : Type*} {r : ℕ}
    (code : Fin r → Option J) := {i : Fin r // ∃ j, code i = some j}

noncomputable instance {J : Type*} {r : ℕ} (code : Fin r → Option J) :
    Fintype (KernelProjectionPresentPivot code) := inferInstanceAs (Fintype {i // ∃ j, code i = some j})

noncomputable def kernelProjectionSelectedPivot {J : Type*} {r : ℕ}
    (code : Fin r → Option J) (i : KernelProjectionPresentPivot code) : J :=
  Classical.choose i.property

theorem kernelProjectionSelectedPivot_spec {J : Type*} {r : ℕ}
    (code : Fin r → Option J) (i : KernelProjectionPresentPivot code) :
    code i.val = some (kernelProjectionSelectedPivot code i) := Classical.choose_spec i.property

theorem kernelProjectionPresentPivot_card_le {J : Type*} {r : ℕ}
    (code : Fin r → Option J) : Fintype.card (KernelProjectionPresentPivot code) ≤ r := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
    (fun i : KernelProjectionPresentPivot code => i.val) Subtype.val_injective

variable {L Y Ω T X J I σ Θ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : Y → ℕ}

end Erdos3

end

section

namespace Erdos3
open scoped TensorProduct Classical

open RationalFilteredNilmanifold

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped Classical

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]

theorem finiteFrequencyKernel_presentPivots
    (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ)
    {r : ℕ} (code : Fin r → Option J) :
    finiteFrequencyKernel P (fun k => eta (kernelProjectionSelectedPivot code k))
      (Finset.univ : Finset (KernelProjectionPresentPivot code)).toList =
      frequencyCodeKernel P eta code := by
  ext x
  rw [mem_finiteFrequencyKernel, mem_frequencyCodeKernel]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro h i j hij
    let k : KernelProjectionPresentPivot code := ⟨i, ⟨j, hij⟩⟩
    have hselected : kernelProjectionSelectedPivot code k = j := by
      exact Option.some.inj ((kernelProjectionSelectedPivot_spec code k).symm.trans hij)
    simpa only [hselected] using h k (Finset.mem_toList.mpr (Finset.mem_univ k))
  · intro h k _
    exact h k.val (kernelProjectionSelectedPivot code k)
      (kernelProjectionSelectedPivot_spec code k)

namespace NilpotentLieFiltration

variable {L Y : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing Y] [LieAlgebra ℚ Y] {s r : ℕ}
    (F : NilpotentLieFiltration L s) (φ : L →ₗ⁅ℚ⁆ Y)
    (eta : J → L →ₗ[ℚ] ℚ) (code : Fin r → Option J)

theorem pivotAnnihilatorIdeal_presentPivots_toSubmodule :
    (F.pivotAnnihilatorIdeal φ (fun k => eta (kernelProjectionSelectedPivot code k))
      (Finset.univ : Finset (KernelProjectionPresentPivot code)).toList).toSubmodule =
      frequencyCodeKernel (F.layer s ⊓ LinearMap.ker φ.toLinearMap) eta code := by
  exact finiteFrequencyKernel_presentPivots
    (F.layer s ⊓ LinearMap.ker φ.toLinearMap) eta code

theorem pivotAnnihilatorIdeal_presentPivots
    (hK : frequencyCodeKernel (F.layer s ⊓ LinearMap.ker φ.toLinearMap) eta code ≤
      F.layer s) :
    F.pivotAnnihilatorIdeal φ (fun k => eta (kernelProjectionSelectedPivot code k))
      (Finset.univ : Finset (KernelProjectionPresentPivot code)).toList =
      F.topSubspaceIdeal
        (frequencyCodeKernel (F.layer s ⊓ LinearMap.ker φ.toLinearMap) eta code) hK := by
  ext x
  change x ∈ (F.pivotAnnihilatorIdeal φ
    (fun k => eta (kernelProjectionSelectedPivot code k))
    (Finset.univ : Finset (KernelProjectionPresentPivot code)).toList).toSubmodule ↔
    x ∈ frequencyCodeKernel (F.layer s ⊓ LinearMap.ker φ.toLinearMap) eta code
  rw [F.pivotAnnihilatorIdeal_presentPivots_toSubmodule φ eta code]

end NilpotentLieFiltration

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EuclideanGraphNorm
namespace OAI

section

namespace Erdos3

theorem euclidean_graph_gram {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ]
    (A : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    Matrix.gram ℝ (fun i => productEuclideanEquiv (Pi.basisFun ℝ σ i, A (Pi.basisFun ℝ σ i))) =
      1 + (LinearMap.toMatrix' A).transpose * LinearMap.toMatrix' A := by
  ext i j
  simp only [Matrix.gram_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fintype.sum_sum_type, Pi.star_apply, star_trivial, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply, LinearMap.toMatrix'_apply]
  change (∑ k : σ, (Pi.basisFun ℝ σ j) k * (Pi.basisFun ℝ σ i) k) +
      (∑ k : κ, A (Pi.basisFun ℝ σ j) k * A (Pi.basisFun ℝ σ i) k) = _
  congr 1
  · simp [Pi.basisFun_apply, Pi.single_apply, Matrix.one_apply, eq_comm]
  · apply Finset.sum_congr rfl
    intro k _
    simpa only [Pi.basisFun_apply] using
      mul_comm (A (Pi.single j 1) k) (A (Pi.single i 1) k)

theorem euclidean_section_gram {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ]
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (G : (σ → ℝ) →ₗ[ℝ] Z) (hG : ∀ y i, (G y).val (Sum.inl i) = y i) :
    let A := ((LinearMap.snd ℝ (σ → ℝ) (κ → ℝ)).comp
      productEuclideanEquiv.symm.toLinearMap).comp (Z.subtype.comp G)
    Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i)) =
      1 + (LinearMap.toMatrix' A).transpose * LinearMap.toMatrix' A := by
  let A := ((LinearMap.snd ℝ (σ → ℝ) (κ → ℝ)).comp
    productEuclideanEquiv.symm.toLinearMap).comp (Z.subtype.comp G)
  have he (y : σ → ℝ) : (G y).val = productEuclideanEquiv (y, A y) := by
    apply PiLp.ext
    intro i
    cases i with
    | inl i => exact hG y i
    | inr j => rfl
  change Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i)) = _
  calc
    _ = Matrix.gram ℝ (fun i => productEuclideanEquiv
        (Pi.basisFun ℝ σ i, A (Pi.basisFun ℝ σ i))) := by
      ext i j
      change inner ℝ (G (Pi.basisFun ℝ σ i)).val (G (Pi.basisFun ℝ σ j)).val = _
      rw [he, he]
      rfl
    _ = _ := euclidean_graph_gram A

end Erdos3

end

section

namespace Erdos3

open Matrix

theorem gram_linearMap_quadratic
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : (ι → ℝ) →ₗ[ℝ] E) (x : ι → ℝ) :
    star x ⬝ᵥ (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ ι i))) *ᵥ x = ‖G x‖ ^ 2 := by
  have hsum : (∑ i, x i • G (Pi.basisFun ℝ ι i)) = G x := by
    simp_rw [← map_smul]
    rw [← map_sum]
    apply congrArg G
    simpa only [Pi.basisFun_repr] using (Pi.basisFun ℝ ι).sum_repr x
  rw [Matrix.star_dotProduct_gram_mulVec, hsum, real_inner_self_eq_norm_sq]

theorem norm_le_sqrt_gram_det_mul
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : (ι → ℝ) →ₗ[ℝ] E)
    (hG : (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ ι i)) - 1).PosSemidef)
    (x : ι → ℝ) :
    ‖G x‖ ≤ Real.sqrt (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ ι i))).det *
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ := by
  let M := Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ ι i))
  have hM : M.IsHermitian := Matrix.isHermitian_gram ℝ _
  have hdet : 0 ≤ M.det := zero_le_one.trans (one_le_det_of_sub_one_posSemidef hM hG)
  have hp := (det_smul_one_sub_posSemidef hM hG).dotProduct_mulVec_nonneg x
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at hp
  have hx : star x ⬝ᵥ x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ ^ 2 := by
    rw [dotProduct_comm]
    exact real_inner_self_eq_norm_sq (WithLp.toLp 2 x : EuclideanSpace ℝ ι)
  rw [hx, gram_linearMap_quadratic G x] at hp
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hdet]
  linarith

end Erdos3

end

section

namespace Erdos3

theorem euclidean_section_gram_sub_one_posSemidef
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ]
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (G : (σ → ℝ) →ₗ[ℝ] Z) (hG : ∀ y i, (G y).val (Sum.inl i) = y i) :
    (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i)) - 1).PosSemidef := by
  let A := ((LinearMap.snd ℝ (σ → ℝ) (κ → ℝ)).comp
    productEuclideanEquiv.symm.toLinearMap).comp (Z.subtype.comp G)
  have he : Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i)) =
      1 + (LinearMap.toMatrix' A).transpose * LinearMap.toMatrix' A :=
    euclidean_section_gram Z G hG
  rw [he, add_sub_cancel_left]
  have hp := Matrix.posSemidef_conjTranspose_mul_self (LinearMap.toMatrix' A)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hp
  exact hp

theorem one_le_euclidean_section_gram_sqrt
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ]
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (G : (σ → ℝ) →ₗ[ℝ] Z) (hG : ∀ y i, (G y).val (Sum.inl i) = y i) :
    1 ≤ Real.sqrt (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i))).det := by
  have hd := one_le_det_of_sub_one_posSemidef (Matrix.isHermitian_gram ℝ _)
    (euclidean_section_gram_sub_one_posSemidef Z G hG)
  simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hd

theorem euclidean_section_norm_le_gram_sqrt
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ]
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (G : (σ → ℝ) →ₗ[ℝ] Z) (hG : ∀ y i, (G y).val (Sum.inl i) = y i)
    (x : σ → ℝ) :
    ‖G x‖ ≤ Real.sqrt (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i))).det *
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ σ)‖ :=
  norm_le_sqrt_gram_det_mul G (euclidean_section_gram_sub_one_posSemidef Z G hG) x

theorem euclidean_section_basis_norm_le_gram_sqrt
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ]
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (G : (σ → ℝ) →ₗ[ℝ] Z) (hG : ∀ y i, (G y).val (Sum.inl i) = y i)
    (i : σ) :
    ‖G (Pi.basisFun ℝ σ i)‖ ≤
      Real.sqrt (Matrix.gram ℝ (fun j => G (Pi.basisFun ℝ σ j))).det := by
  simpa only [Pi.basisFun_apply, PiLp.toLp_single, PiLp.norm_single, norm_one, mul_one] using
    euclidean_section_norm_le_gram_sqrt Z G hG (Pi.basisFun ℝ σ i)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ScalarFunctionalCoefficientGrid
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]

theorem scalarFunctionalDenominator_pos (b : Basis ι ℚ V) (θ : V →ₗ[ℚ] ℚ) :
    0 < matrixDenominator (fun (_ : Unit) i => θ (b i)) :=
  matrixDenominator_pos _

theorem scalarFunctionalDenominator_le (b : Basis ι ℚ V) (θ : V →ₗ[ℚ] ℚ)
    {H : ℕ} (hθ : ∀ i, RationalHeightLE (θ (b i)) H) :
    matrixDenominator (fun (_ : Unit) i => θ (b i)) ≤ H ^ Fintype.card ι := by
  simpa using matrixDenominator_le (fun (_ : Unit) i => θ (b i)) (fun _ i => hθ i)

theorem realifyFunctional_denominator_grid (b : Basis ι ℚ V) (θ : V →ₗ[ℚ] ℚ)
    (m : ℕ) (x : ℝ ⊗[ℚ] V)
    (hx : (b.baseChange ℝ).equivFun x ∈ realDenominatorGrid m) :
    ∃ z : ℤ,
      ((matrixDenominator (fun (_ : Unit) i => θ (b i)) * m : ℕ) : ℝ) *
        realifyFunctional θ x = (z : ℝ) := by
  let ℓ : V →ₗ[ℚ] (Unit → ℚ) := LinearMap.pi (fun _ => θ)
  obtain ⟨z, hz⟩ := realifyCoordinateMap_grid b ℓ m x hx
  refine ⟨z (), ?_⟩
  exact (congrFun hz ()).symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AveragedModeledPatchTransfer
namespace OAI

section

namespace Erdos3.PatchKernel

open scoped NNReal

variable {d : ℕ}

noncomputable def weightBounded (Φ : PatchKernel d) (f : (Fin d → ℝ) → ℝ)
    (L C : ℝ≥0) (hC : 1 ≤ C) (hf : LipschitzWith L f)
    (hbound : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) : PatchKernel d :=
  Φ.weight (fun x => f x / C) (L / C)
    (by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.dist_eq, ← sub_div, abs_div, abs_of_nonneg C.coe_nonneg]
      have h := div_le_div_of_nonneg_right (hf.dist_le_mul x y) C.coe_nonneg
      simpa only [Real.dist_eq, NNReal.coe_div, mul_div_right_comm] using h)
    (fun x => ⟨div_nonneg (hbound x).1 C.coe_nonneg,
      (div_le_one (show (0 : ℝ) < C by exact lt_of_lt_of_le zero_lt_one hC)).mpr (hbound x).2⟩)

@[simp] theorem weightBounded_lip (Φ : PatchKernel d) (f : (Fin d → ℝ) → ℝ)
    (L C : ℝ≥0) (hC : 1 ≤ C) (hf : LipschitzWith L f)
    (hbound : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) :
    (Φ.weightBounded f L C hC hf hbound).lip = Φ.lip + L / C := rfl

end Erdos3.PatchKernel

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.PolynomialPatch

open scoped NNReal

variable {σ : Type*} {s d E m : ℕ} {p : Fin m → ℕ}

noncomputable abbrev withRecoveredWeight (A : PolynomialPatch σ s d) (Ψ : PatchKernel m)
    (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) : PolynomialPatch σ s d :=
  { A with kernel := recoveredCellKernel A.kernel Ψ M a c K hM }

noncomputable def recoveredPatch (A : PolynomialPatch σ s d)
    (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (Ψ : PatchKernel m) (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K)
    (hweight : ∀ i j, M i j ≠ 0 → A.weight j ≤ p i) : PolynomialPatch σ s (d + E) :=
  (A.withRecoveredWeight Ψ M a c K hM).insertAffineLifts B
    (fun i => (c i : ℝ)) (fun i j => (M i j : ℝ))
    (fun i j h => hweight i j (by exact_mod_cast h))

@[simp] theorem recoveredPatch_lip (A : PolynomialPatch σ s d)
    (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (Ψ : PatchKernel m) (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K)
    (hweight : ∀ i j, M i j ≠ 0 → A.weight j ≤ p i) :
    (A.recoveredPatch B Ψ M a c K hM hweight).kernel.lip = A.kernel.lip + Ψ.lip * K + B.kernel.lip := rfl

end Erdos3.PolynomialPatch

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal BigOperators

namespace PolynomialPatch

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal BigOperators

namespace PolynomialPatch

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3.PolynomialPatch

open scoped NNReal BigOperators

variable {σ : Type*} {s d₀ d D j detector E m : ℕ} {p : Fin m → ℕ}

noncomputable def recursiveRecoveredPatch (A : PolynomialPatch σ s detector)
    (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (Ψ : PatchKernel m) (M : Fin m → Fin detector → ℤ)
    (a : Fin detector → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ k, |(M i k : ℝ)|) ≤ K)
    (hweight : ∀ i k, M i k ≠ 0 → A.weight k ≤ p i)
    (hs : 1 ≤ s) (hD : D ≤ d) (hE : E ≤ d₀ + s * (d-D))
    (hdetector : detector ≤ j * D) (hj : j ≤ s) :
    PolynomialPatch σ s (d₀ + s * d) :=
  (A.recoveredPatch B Ψ M a c K hM hweight).padRank hs
    (recursive_patch_step_rank_bound hD hE hdetector hj)

@[simp] theorem recursiveRecoveredPatch_value (A : PolynomialPatch σ s detector)
    (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (Ψ : PatchKernel m) (M : Fin m → Fin detector → ℤ)
    (a : Fin detector → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ k, |(M i k : ℝ)|) ≤ K)
    (hweight : ∀ i k, M i k ≠ 0 → A.weight k ≤ p i)
    (hs : 1 ≤ s) (hD : D ≤ d) (hE : E ≤ d₀ + s * (d-D))
    (hdetector : detector ≤ j * D) (hj : j ≤ s) (t : σ → ℝ) :
    (A.recursiveRecoveredPatch B Ψ M a c K hM hweight hs hD hE hdetector hj).value t =
      (A.recoveredPatch B Ψ M a c K hM hweight).value t :=
  padRank_value _ _ _ _

@[simp] theorem recursiveRecoveredPatch_lip (A : PolynomialPatch σ s detector)
    (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (Ψ : PatchKernel m) (M : Fin m → Fin detector → ℤ)
    (a : Fin detector → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ k, |(M i k : ℝ)|) ≤ K)
    (hweight : ∀ i k, M i k ≠ 0 → A.weight k ≤ p i)
    (hs : 1 ≤ s) (hD : D ≤ d) (hE : E ≤ d₀ + s * (d-D))
    (hdetector : detector ≤ j * D) (hj : j ≤ s) :
    (A.recursiveRecoveredPatch B Ψ M a c K hM hweight hs hD hE hdetector hj).kernel.lip =
      A.kernel.lip + Ψ.lip * K + B.kernel.lip + 4 := by
  rw [recursiveRecoveredPatch, padRank_lip, recoveredPatch_lip]

end Erdos3.PolynomialPatch

namespace Erdos3
open _root_.MvPolynomial
open scoped NNReal BigOperators

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

open _root_.MvPolynomial
open scoped NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeNiltestPartition
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_native_niltest_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ) {p ρ : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → 0 < ρ →
      1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∀ g : D.filtration.realification.PolynomialOrbit w,
        ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ A : Fin n → D.Niltest w,
            (∀ i, (A i).orbit = g) ∧
            (∀ i, (A i).UnitIntervalValued) ∧
            (∀ i, (A i).ComplexityLE ((p + C) ^ C)) ∧
            (∀ z, ∑ i, ((A i).observable z).re = 1) ∧
            (letI := D.metricSpace
             ∀ i x y, 0 < ((A i).observable x).re → 0 < ((A i).observable y).re → dist x y ≤ ρ) := by
  obtain ⟨B, _, hpartition⟩ := exists_native_positive_partition s a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Polynomial.X + (Polynomial.X + Polynomial.C B) ^ B + 2)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ d D w p ρ hp hD hρ hρinv g
  obtain ⟨n, hn, hnb, K, hK, ψ, hψ, hsum, hLip, hdiam⟩ := hpartition D hp hD hρ hρinv
  have hcost : p + (p + B) ^ B + 2 ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  have hB0 : 0 ≤ (p + B) ^ B := pow_nonneg (by positivity) _
  have hBC : (p + B) ^ B ≤ (p + C) ^ C := by linarith
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hlog : Real.log (3 + (K : ℝ)) ≤ (p + C) ^ C := by
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    have h1 : 1 ≤ Real.exp ((p + B) ^ B) := Real.one_le_exp hB0
    have h2 : (4 : ℝ) ≤ Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    have hle : 3 + (K : ℝ) ≤ Real.exp ((p + B) ^ B + 2) := by
      rw [Real.exp_add]
      nlinarith [mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg ((p + B) ^ B))]
    exact hle.trans (Real.exp_le_exp.mpr (by linarith))
  let A : Fin n → D.Niltest w := fun i =>
    D.sectionNiltest g (fun z (_ : Unit) => ψ i z) (fun z _ => hψ i z) K (fun _ => hLip i) (some ())
  refine ⟨n, hn, hnb.trans (Real.exp_le_exp.mpr hBC), A, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro i
    exact D.sectionNiltest_unit_interval g _ _ K _ (some ())
  · intro i
    exact D.sectionNiltest_complexityLE g _ _ K _ (some ()) (hD.mono D hpC) hlog
  · intro z
    change ∑ i, ψ i z = 1
    exact hsum z
  · let := D.metricSpace
    intro i x y hx hy
    exact hdiam i x y hx hy

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonPositivePartitionRefinement
namespace OAI

section

universe u

namespace Erdos3

open scoped TensorProduct

structure PositiveCyclicModel (degree N : ℕ) [NeZero N] (p : ℝ) (f : ZMod N → ℝ) where
  L : Type u
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : model.Niltest (fun _ : Unit => 1)
  positive : test.UnitIntervalValued
  complexity : test.ComplexityLE p
  eval : ∀ x, f x = (test.evalCyclic N (fun _ => x)).re

theorem PositiveCyclicNiltest.model_nonempty {degree N : ℕ} [NeZero N] {p : ℝ}
    {f : ZMod N → ℝ} (hf : PositiveCyclicNiltest.{u} degree N p f) (hp : 0 ≤ p) :
    Nonempty (PositiveCyclicModel.{u} degree N (raisedNiltestBudget p) f) := by
  rcases hf with @⟨L, lie, algebra, s, dim, topology, topologicalAdd, continuousSMul,
    hausdorff, D, hdegree, T, hpositive, hcomplexity, heval⟩
  refine ⟨{
    L := L
    lie := lie
    algebra := algebra
    dim := dim
    topology := topology
    topologicalAdd := topologicalAdd
    continuousSMul := continuousSMul
    hausdorff := hausdorff
    model := D.raiseStep hdegree
    test := T.raiseStep hdegree
    positive := T.raiseStep_unit_interval hdegree hpositive
    complexity := T.raiseStep_complexity hdegree hp hcomplexity
    eval := ?_ }⟩
  intro x
  rw [RationalFilteredNilmanifold.Niltest.raiseStep_evalCyclic]
  exact heval x

end Erdos3

end

section

universe u

namespace Erdos3.PositiveCyclicNiltest

open scoped TensorProduct

end Erdos3.PositiveCyclicNiltest

end

section

universe u

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearCoefficientSplitting
namespace OAI

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct

theorem exists_biased_linear_coefficient_splitting
    {σ ι V : Type*} [Fintype σ] [DecidableEq σ] [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (η : V →ₗ[ℚ] ℚ) (hη : η ≠ 0)
    {H : ℕ} (hH : 1 ≤ H) (hheight : ∀ i, RationalHeightLE (η (b i)) H)
    (T : σ → ℕ) (hT : ∀ i, 0 < T i) (a : σ → ℝ ⊗[ℚ] V)
    {δ : ℝ} (hδ : 0 < δ)
    (hbias : δ ≤ ‖linearPhaseMean T (fun i => (realifyFunctional η (a i) : CircleFourier.Circle))‖) :
    ∃ (m : ℕ) (e p r : σ → ℝ ⊗[ℚ] V),
      0 < m ∧ m ≤ H ∧
      (∀ i, e i + p i + r i = a i) ∧
      (∀ i, realifyFunctional η (p i) = 0) ∧
      (∀ i j, |(b.baseChange ℝ).repr (e i) j| ≤ (H : ℝ) / (2 * T i * δ)) ∧
      (fun z : σ × ι => (b.baseChange ℝ).repr (r z.1) z.2) ∈ realDenominatorGrid m := by
  classical
  obtain ⟨v, m, hm, hmH, hv, hvheight, z, hz⟩ := exists_bounded_frequency_direction b η hη hH hheight
  let vR : ℝ ⊗[ℚ] V := (1 : ℝ) ⊗ₜ[ℚ] v
  let c : σ → ℝ := fun i => realifyFunctional η (a i)
  let n : σ → ℤ := fun i => round (c i)
  let e := fun i => (c i - (n i : ℝ)) • vR
  let p := fun i => a i - c i • vR
  let r := fun i => (n i : ℝ) • vR
  have hvR : realifyFunctional η vR = 1 := by simp only [vR, realifyFunctional_tmul, hv, Rat.cast_one, one_mul]
  have hcoord (j : ι) : (b.baseChange ℝ).repr vR j = (b.repr v j : ℝ) := by
    simp only [vR, Basis.baseChange_repr_tmul, Rat.smul_def, mul_one]
  have hnear : ∀ i, |c i - (n i : ℝ)| ≤ 1 / (2 * T i * δ) :=
    linear_phase_near_integers T hT c hδ hbias
  refine ⟨m, e, p, r, hm, hmH, ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp [e, p, r]
    rw [sub_smul]
    abel
  · intro i
    simp only [p, map_sub, map_smul, hvR, smul_eq_mul, mul_one, c, sub_self]
  · intro i j
    change |(b.baseChange ℝ).repr ((c i - (n i : ℝ)) • vR) j| ≤ _
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, abs_mul, hcoord]
    calc
      _ ≤ |c i - (n i : ℝ)| * H :=
        mul_le_mul_of_nonneg_left (hvheight j).abs_real_le (abs_nonneg _)
      _ ≤ (1 / (2 * T i * δ)) * H := mul_le_mul_of_nonneg_right (hnear i) (Nat.cast_nonneg H)
      _ = _ := by ring
  · refine ⟨fun ij => n ij.1 * z ij.2, ?_⟩
    funext ij
    change ((n ij.1 * z ij.2 : ℤ) : ℝ) = (m : ℝ) * (b.baseChange ℝ).repr ((n ij.1 : ℝ) • vR) ij.2
    rw [Int.cast_mul, map_smul, Finsupp.smul_apply, smul_eq_mul, hcoord]
    have hz' : (m : ℝ) * (b.repr v ij.2 : ℝ) = (z ij.2 : ℝ) := by exact_mod_cast hz ij.2
    calc
      (n ij.1 : ℝ) * (z ij.2 : ℝ) = (n ij.1 : ℝ) * ((m : ℝ) * (b.repr v ij.2 : ℝ)) := by rw [hz']
      _ = _ := by ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OptionComplementCover
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {L : Option ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : Option ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

noncomputable def optionProductSpaceEquiv :
    (pi D).Space ≃ (D none).Space × (pi (fun i => D (some i))).Space :=
  ((productSpaceEquiv D).trans Equiv.piOptionEquivProd).trans
    (Equiv.prodCongr (Equiv.refl _) (productSpaceEquiv (fun i => D (some i))).symm)

theorem optionProductSpaceEquiv_apply (x : (pi D).Space) :
    optionProductSpaceEquiv D x =
      (productSpaceEquiv D x none,
        (productSpaceEquiv (fun i => D (some i))).symm (fun i => productSpaceEquiv D x (some i))) := rfl

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L (some i)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L (some i)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L (some i)))]
  [T2Space (ℝ ⊗[ℚ] (∀ i, L (some i)))]

theorem optionProductSpaceEquiv_symm_lipschitz :
    letI := (pi D).metricSpace
    letI := (D none).metricSpace
    letI := (pi (fun i => D (some i))).metricSpace
    LipschitzWith ((1 + productMetricBound (fun i => d (some i))) * productMetricBound d)
      (optionProductSpaceEquiv D).symm := by
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  let := (pi (fun i => D (some i))).metricSpace
  have hpair : LipschitzWith (1 + productMetricBound (fun i => d (some i)))
      (fun x : (D none).Space × (pi (fun i => D (some i))).Space =>
        (x.1, productSpaceEquiv (fun i => D (some i)) x.2)) := by
    have h := (LipschitzWith.prod_fst (α := (D none).Space)
      (β := (pi (fun i => D (some i))).Space)).prodMk
      ((productSpaceEquiv_lipschitz (fun i => D (some i))).comp
        (LipschitzWith.prod_snd (α := (D none).Space)))
    apply h.weaken
    simp only [mul_one]
    exact max_le (le_add_of_nonneg_right zero_le) (le_add_of_nonneg_left zero_le)
  have h := (productSpaceEquiv_symm_lipschitz D).comp
    ((optionPiIsometryEquiv (X := fun i => (D i).Space)).symm.isometry.lipschitz.comp hpair)
  have heq : ((optionProductSpaceEquiv D).symm : _ → (pi D).Space) =
      (fun x => (productSpaceEquiv D).symm
        ((optionPiIsometryEquiv (X := fun i => (D i).Space)).symm
          (x.1, productSpaceEquiv (fun i => D (some i)) x.2))) := rfl
  rw [heq]
  simpa only [one_mul, mul_comm, Function.comp_def] using h

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [LieRing H] [LieAlgebra ℚ H]
  {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {r t : ℕ} {d : ι → ℕ} (F : NilpotentLieFiltration H r)
  (D : ∀ i, RationalFilteredNilmanifold (L i) t (d i))

omit [DecidableEq ι] in
theorem productProjectionHom_realificationMap (φ : ∀ i, H →ₗ⁅ℚ⁆ L i)
    (x : F.realification.Group) (i : ι) :
    productProjectionHom D i
      (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := (pi D).filtration.lowerCentralSeries_eq_bot) (liePiMap φ) x) =
      realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := (D i).filtration.lowerCentralSeries_eq_bot) (φ i) x := by
  apply NilpotentLieBCHGroup.ext
  exact realification_liePiEval_liePiMap φ x.coord i

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [LieRing H] [LieAlgebra ℚ H]
  {L : Option ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {r t : ℕ} {d : Option ι → ℕ} (F : NilpotentLieFiltration H r)
  (D : ∀ i, RationalFilteredNilmanifold (L i) t (d i))

theorem optionProductSpaceEquiv_realificationMap (φ : ∀ i, H →ₗ⁅ℚ⁆ L i)
    (x : F.realification.Group) :
    optionProductSpaceEquiv D
      (QuotientGroup.mk (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := (pi D).filtration.lowerCentralSeries_eq_bot) (liePiMap φ) x)) =
      (QuotientGroup.mk (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
          (hM := (D none).filtration.lowerCentralSeries_eq_bot) (φ none) x),
        QuotientGroup.mk (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
          (hM := (pi (fun i => D (some i))).filtration.lowerCentralSeries_eq_bot)
          (liePiMap (fun i => φ (some i))) x)) := by
  rw [optionProductSpaceEquiv_apply]
  apply Prod.ext
  · simp only [productSpaceEquiv_mk, productProjectionHom_realificationMap]
  · apply (productSpaceEquiv (fun i => D (some i))).injective
    rw [Equiv.apply_symm_apply]
    funext i
    simp only [productSpaceEquiv_mk, productProjectionHom_realificationMap]

omit [DecidableEq ι] in
theorem lowered_productProjectionHom_realificationMap {s n : ℕ}
    (Q : RationalFilteredNilmanifold (L none) s n) (φ : ∀ i, H →ₗ⁅ℚ⁆ L i)
    (x : F.realification.Group) :
    changeStep (D none).filtration.realification.lowerCentralSeries_eq_bot
      Q.filtration.realification.lowerCentralSeries_eq_bot
      (productProjectionHom D none (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := (pi D).filtration.lowerCentralSeries_eq_bot) (liePiMap φ) x)) =
      realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (φ none) x := by
  rw [productProjectionHom_realificationMap]
  rfl

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (E : RationalFilteredNilmanifold L s d)

noncomputable def singletonProductSpace (y : E.Space) :
    (pi (fun _ : Unit => E)).Space :=
  (productSpaceEquiv (fun _ : Unit => E)).symm (fun _ => y)

@[simp] theorem productSpaceEquiv_singletonProductSpace (y : E.Space) (i : Unit) :
    productSpaceEquiv (fun _ : Unit => E) (E.singletonProductSpace y) i = y := by
  simp only [singletonProductSpace, Equiv.apply_symm_apply]

theorem productMetricBound_singleton (d : ℕ) :
    productMetricBound (fun _ : Unit => d) = coordinateLipschitzBound d d 1 := by
  simp [productMetricBound, Fintype.card_sigma]

theorem productMetricBound_singleton_le_exp {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) :
    (productMetricBound (fun _ : Unit => d) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
  rw [productMetricBound_singleton]
  exact coordinateLipschitzBound_le_exp d d 1 hp hd hd
    (by simpa only [NNReal.coe_one] using Real.one_le_exp hp)

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] (Unit → L))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Unit → L))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Unit → L))] [T2Space (ℝ ⊗[ℚ] (Unit → L))]

theorem singletonProductSpace_lipschitz :
    letI := E.metricSpace
    letI := (pi (fun _ : Unit => E)).metricSpace
    LipschitzWith (productMetricBound (fun _ : Unit => d)) E.singletonProductSpace := by
  let := E.metricSpace
  let : ∀ _ : Unit, MetricSpace E.Space := fun _ => E.metricSpace
  let := (pi (fun _ : Unit => E)).metricSpace
  have hconstant : LipschitzWith 1 (fun y : E.Space => fun _ : Unit => y) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    apply (dist_pi_le_iff (by positivity)).mpr
    intro i
    simp only [NNReal.coe_one, one_mul, le_refl]
  have h := (productSpaceEquiv_symm_lipschitz (fun _ : Unit => E)).comp hconstant
  rw [mul_one] at h
  exact h

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] (Unit → L))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Unit → L))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Unit → L))] [T2Space (ℝ ⊗[ℚ] (Unit → L))] in

theorem singletonProductSpace_realificationMap
    {H : Type*} [LieRing H] [LieAlgebra ℚ H] {r : ℕ}
    (F : NilpotentLieFiltration H r) (φ : H →ₗ⁅ℚ⁆ L)
    (x : F.realification.Group) :
    E.singletonProductSpace
        (QuotientGroup.mk (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
          (hM := E.filtration.lowerCentralSeries_eq_bot) φ x)) =
      QuotientGroup.mk (realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := (pi (fun _ : Unit => E)).filtration.lowerCentralSeries_eq_bot)
        (liePiMap (fun _ : Unit => φ)) x) := by
  apply (productSpaceEquiv (fun _ : Unit => E)).injective
  rw [singletonProductSpace, Equiv.apply_symm_apply]
  funext i
  rw [productSpaceEquiv_mk, productProjectionHom_realificationMap]

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι : Type v} {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [LieAlgebra ℚ L₀] [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

def optionComplementMaps : ∀ j : {j : Option ι // j ≠ none},
    (∀ i, L i) →ₗ⁅ℚ⁆ optionLieSpace L₀ L j.val
  | ⟨none, h⟩ => False.elim (h rfl)
  | ⟨some i, _⟩ => liePiEval i

def optionComplementMap : (∀ i, L i) →ₗ⁅ℚ⁆
    (∀ j : {j : Option ι // j ≠ none}, optionLieSpace L₀ L j.val) :=
  liePiMap (optionComplementMaps (L₀ := L₀) (L := L))

namespace RationalFilteredNilmanifold

variable [Fintype ι] [DecidableEq ι] {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

noncomputable def optionComplementFactors : ∀ j : {j : Option ι // j ≠ none},
    RationalFilteredNilmanifold (optionLieSpace L₀ L j.val) s (optionDimension d₀ d j.val) :=
  fun j => optionFactors D₀ D j.val

noncomputable def optionComplementOrbits {σ : Type*} {w : σ → ℕ}
    (g : ∀ i, (D i).filtration.realification.PolynomialOrbit w) :
    ∀ j, ((optionComplementFactors D₀ D) j).filtration.realification.PolynomialOrbit w
  | ⟨none, h⟩ => False.elim (h rfl)
  | ⟨some i, _⟩ => g i

end RationalFilteredNilmanifold
end Erdos3

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup NilpotentLieFiltration
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BoundedFrequencyKernel
namespace OAI

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct

theorem realifyFunctional_zero {V : Type*} [AddCommGroup V] [Module ℚ V]
    (x : ℝ ⊗[ℚ] V) : realifyFunctional (0 : V →ₗ[ℚ] ℚ) x = 0 := by
  apply (mem_realified_frequency_kernel_iff (0 : V →ₗ[ℚ] ℚ) x).mp
  rw [LinearMap.ker_zero, Submodule.baseChange_top]
  trivial

theorem exists_linear_frequency_splitting
    {σ ι V : Type*} [Fintype σ] [DecidableEq σ] [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (η : V →ₗ[ℚ] ℚ)
    {H : ℕ} (hH : 1 ≤ H) (hheight : ∀ i, RationalHeightLE (η (b i)) H)
    (T : σ → ℕ) (hT : ∀ i, 0 < T i) (a : σ → ℝ ⊗[ℚ] V)
    {δ : ℝ} (hδ : 0 < δ)
    (hbias : δ ≤ ‖linearPhaseMean T (fun i => (realifyFunctional η (a i) : CircleFourier.Circle))‖) :
    ∃ (m : ℕ) (e p r : σ → ℝ ⊗[ℚ] V),
      0 < m ∧ m ≤ H ∧ (∀ i, e i + p i + r i = a i) ∧
      (∀ i, realifyFunctional η (p i) = 0) ∧
      (∀ i j, |(b.baseChange ℝ).repr (e i) j| ≤ (H : ℝ) / (2 * T i * δ)) ∧
      (fun z : σ × ι => (b.baseChange ℝ).repr (r z.1) z.2) ∈ realDenominatorGrid m := by
  by_cases hη : η = 0
  · subst η
    refine ⟨1, 0, a, 0, Nat.zero_lt_one, hH, ?_, ?_, ?_, ?_⟩
    · intro i
      simp
    · intro i
      exact realifyFunctional_zero (a i)
    · intro i j
      simp only [Pi.zero_apply, map_zero, Finsupp.zero_apply, abs_zero]
      positivity
    · refine ⟨0, ?_⟩
      ext z
      simp
  · exact exists_biased_linear_coefficient_splitting b η hη hH hheight T hT a hδ hbias

theorem exists_bounded_frequency_kernel_spanning {ι V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (η : V →ₗ[ℚ] ℚ)
    {H : ℕ} (hH : 1 ≤ H) (hheight : ∀ i, RationalHeightLE (η (b i)) H) :
    ∃ v : ι → V, Submodule.span ℚ (Set.range v) = LinearMap.ker η ∧
      ∀ i j, RationalHeightLE (b.repr (v i) j) (2 * H ^ 2) := by
  classical
  by_cases hη : η = 0
  · subst η
    refine ⟨b, ?_, ?_⟩
    · rw [LinearMap.ker_zero]
      exact b.span_eq
    · intro i j
      have hh : 1 ≤ 2 * H ^ 2 := (one_le_pow₀ hH).trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 2))
      rw [Basis.repr_self, Finsupp.single_apply]
      split_ifs
      · exact rationalHeightLE_one hh
      · exact rationalHeightLE_zero hh
  · obtain ⟨u, _, _, _, hu, huheight, _⟩ := exists_bounded_frequency_direction b η hη hH hheight
    exact ⟨fun i => b i - η (b i) • u, frequencyKernel_spanning b η u hu,
      frequencyKernel_spanning_height b η u hheight huheight⟩

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Classical

theorem exists_frequency_kernel_basis_logHeight
    {V : Type*} [AddCommGroup V] [Module ℚ V] {d D : ℕ}
    (b : Basis (Fin d) ℚ V) (P : Submodule ℚ V)
    (vP : Fin d → V) (hP : Submodule.span ℚ (Set.range vP) = P)
    (eta : Fin D → V →ₗ[ℚ] ℚ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hD : (D : ℝ) ≤ p)
    (hvP : ∀ i j, rationalLogHeight (b.repr (vP i) j) ≤ p)
    (heta : ∀ i j, rationalLogHeight (eta i (b j)) ≤ p) :
    ∃ n : ℕ, n ≤ d ∧
      ∃ bk : Basis (Fin n) ℚ (finiteFrequencyKernel P eta (List.finRange D)),
        ∀ i j, rationalLogHeight (b.repr (bk i : V) j) ≤
          ((2 * p + 6) ^ 2 + 2) ^ 63 := by
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHp : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  choose v hv hh using fun i => exists_bounded_frequency_kernel_spanning b (eta i) hH
    (fun j => rationalHeightLE_ceil_exp (heta i j))
  let U : Option (Fin D) → Submodule ℚ V := fun z => z.elim P (fun i => LinearMap.ker (eta i))
  let gen : Option (Fin D) → Fin d → V := fun z => z.elim vP v
  have hgen (z) : Submodule.span ℚ (Set.range (gen z)) = U z := by
    cases z with
    | none => exact hP
    | some i => exact hv i
  have hHmono : H ≤ 2 * H ^ 2 := by nlinarith
  have hHe : ((2 * H ^ 2 : ℕ) : ℝ) ≤ Real.exp (2 * p + 4) := by
    have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    calc
      _ = 2 * (H : ℝ) ^ 2 := by push_cast; rfl
      _ ≤ Real.exp 2 * (Real.exp (p + 1)) ^ 2 := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  have hheight (z) (i j) : rationalLogHeight (b.repr (gen z i) j) ≤ 2 * p + 4 := by
    apply rationalLogHeight_le_of_height (H := 2 * H ^ 2) _ hHe
    cases z with
    | none => exact (rationalHeightLE_ceil_exp (hvP i j)).mono hHmono
    | some k => exact hh k i j
  have hcount : (Fintype.card (Option (Fin D)) : ℝ) ≤ 2 * p + 4 := by
    simp only [Fintype.card_option, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    linarith
  obtain ⟨n, hn, bk, hbk⟩ := exists_submodule_intersection_basis_logHeight b U gen hgen
    (by linarith : 0 ≤ 2 * p + 4)
    (by simpa only [Fintype.card_fin] using (show (d : ℝ) ≤ 2 * p + 4 by linarith))
    (by simpa only [Fintype.card_fin] using (show (d : ℝ) ≤ 2 * p + 4 by linarith))
    hcount hheight
  have hK : (⨅ z, U z) = finiteFrequencyKernel P eta (List.finRange D) := by
    ext x
    simp only [Submodule.mem_iInf, mem_finiteFrequencyKernel, List.mem_finRange, forall_true_left]
    constructor
    · intro h
      exact ⟨h none, fun i => h (some i)⟩
    · intro h z
      cases z with
      | none => exact h.1
      | some i => exact h.2 i
  refine ⟨n, by simpa only [Fintype.card_fin] using hn,
    bk.map (LinearEquiv.ofEq _ _ hK), ?_⟩
  intro i j
  simpa only [Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    show 2 * p + 4 + 2 = 2 * p + 6 by ring] using hbk i j

theorem exists_frequency_code_kernel_basis_logHeight
    {V J : Type*} [AddCommGroup V] [Module ℚ V] {d D : ℕ}
    (b : Basis (Fin d) ℚ V) (P : Submodule ℚ V)
    (vP : Fin d → V) (hP : Submodule.span ℚ (Set.range vP) = P)
    (eta : J → V →ₗ[ℚ] ℚ) (code : Fin D → Option J) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hD : (D : ℝ) ≤ p)
    (hvP : ∀ i j, rationalLogHeight (b.repr (vP i) j) ≤ p)
    (heta : ∀ i j, rationalLogHeight (eta i (b j)) ≤ p) :
    ∃ n : ℕ, n ≤ d ∧ ∃ bk : Basis (Fin n) ℚ (frequencyCodeKernel P eta code),
      ∀ i j, rationalLogHeight (b.repr (bk i : V) j) ≤ ((2 * p + 6) ^ 2 + 2) ^ 63 := by
  apply exists_frequency_kernel_basis_logHeight b P vP hP
    (fun i => (code i).elim 0 eta) hp hd hD hvP
  intro i j
  cases code i with
  | none => simpa [rationalLogHeight] using hp
  | some k => exact heta k j

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteUnitCoordinate
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_large_unit_coordinate {I : Type*} [Fintype I] (v : I → ℂ)
    (hv : ∑ i, ‖v i‖ ^ 2 = 1) :
    ∃ i, 1 / (Fintype.card I + 1 : ℝ) ≤ ‖v i‖ := by
  classical
  have hpos : (0 : ℝ) < Fintype.card I + 1 := by positivity
  by_contra h
  push Not at h
  have hn : ‖v‖ < 1 / (Fintype.card I + 1 : ℝ) :=
    (pi_norm_lt_iff (by positivity)).mpr h
  let V : EuclideanSpace ℂ I := WithLp.toLp 2 v
  have hV : ‖V‖ = 1 := by
    have hs : ‖V‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      exact hv
    nlinarith [norm_nonneg V]
  have hbound := euclidean_norm_le_card_add_one_mul V (norm_nonneg v)
    (fun i => norm_le_pi_norm v i)
  rw [hV] at hbound
  have hsmall := (lt_div_iff₀ hpos).mp hn
  nlinarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.OptionMarkedPolynomialProjection
namespace OAI

section

universe u v

namespace Erdos3

open VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

theorem optionMarkedPolynomialProjection_none
    {ι : Type v} [Fintype ι] {L₀ M₀ : Type u} {L : ι → Type u}
    [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing M₀] [LieAlgebra ℚ M₀]
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
    {σ : Type*} {s : ℕ} {w : σ → ℕ}
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace L₀ L i)))
    (φ : L₀ →ₗ⁅ℚ⁆ M₀) (F₀ : NilpotentLieFiltration M₀ s)
    (F : ∀ i, NilpotentLieFiltration (L i) s)
    (g : ∀ i, (optionFiltrations F₀ F i).realification.PolynomialOrbit w)
    (h : VectorPolynomial.map
      ((realificationLieHom (optionMarkedLieMap φ)).toLinearMap.restrictScalars ℚ) p =
        (piRealOrbit (optionFiltrations F₀ F) g).log) :
    VectorPolynomial.map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ)
      (VectorPolynomial.map
        ((realificationLieHom (liePiEval none)).toLinearMap.restrictScalars ℚ) p) =
          (g none).log := by
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  erw [coefficients_map, coefficients_map]
  have hα := congrArg
    (fun q : VectorPolynomial σ ℚ
        (ℝ ⊗[ℚ] (∀ i : Option ι, optionLieSpace M₀ L i)) =>
      realificationLieHom (liePiEval none) (coefficients q α)) h
  simp only [coefficients_map] at hα
  change realificationLieHom (liePiEval none)
    (realificationLieHom (optionMarkedLieMap φ) (coefficients p α)) = _ at hα
  rw [realification_optionMarkedLieMap_none, piRealOrbit_coefficient] at hα
  exact hα

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RaisedDegreeRank
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

noncomputable def realLayer (d i : ℕ) : LieIdeal ℝ (ℝ ⊗[ℚ] L) :=
  (F.layerIdeal d i).baseChange ℝ

theorem realLayer_lex_antitone {d e i j : ℕ} (h : d < e ∨ d = e ∧ i ≤ j) :
    F.realLayer e j ≤ F.realLayer d i := Submodule.baseChange_mono ℝ (F.lex_antitone h)

theorem realLayer_congr {d e i j : ℕ} (h : F.layer d i = F.layer e j) :
    F.realLayer d i = F.realLayer e j :=
  le_antisymm (Submodule.baseChange_mono ℝ h.le) (Submodule.baseChange_mono ℝ h.ge)

theorem realLayer_one : F.realLayer 1 0 = ⊤ := by
  have h : F.layerIdeal 1 0 = ⊤ := by
    ext x
    change x ∈ F.layer 1 0 ↔ x ∈ (⊤ : Submodule ℚ L)
    rw [F.one_eq_top]
  simp only [realLayer, h, LieSubmodule.baseChange_top]

theorem realLayer_rank_zero_eq_one (d : ℕ) : F.realLayer d 0 = F.realLayer d 1 :=
  F.realLayer_congr (F.rank_zero_eq_one d)

theorem realLayer_overshoot (d i : ℕ) (h : d < i) : F.realLayer d i = F.realLayer (d + 1) 0 :=
  F.realLayer_congr (F.overshoot d i h)

theorem realLayer_terminal : F.realLayer s (r + 1) = ⊥ := by
  have h : F.layerIdeal s (r + 1) = ⊥ := by
    ext x
    change x ∈ F.layer s (r + 1) ↔ x ∈ (⊥ : Submodule ℚ L)
    rw [F.terminal]
  simp only [realLayer, h, LieSubmodule.baseChange_bot]

theorem lie_realLayer_le (d e i j : ℕ) :
    ⁅F.realLayer d i, F.realLayer e j⁆ ≤ F.realLayer (d + e) (i + j) := by
  have h : ⁅F.layerIdeal d i, F.layerIdeal e j⁆ ≤ F.layerIdeal (d + e) (i + j) := by
    rw [LieSubmodule.lie_le_iff]
    exact fun x hx y hy => F.lie_mem hx hy
  rw [realLayer, realLayer, ← LieSubmodule.lie_baseChange]
  exact Submodule.baseChange_mono ℝ h

theorem realLayer_lie_mem {d e i j : ℕ} {x y : ℝ ⊗[ℚ] L}
    (hx : x ∈ F.realLayer d i) (hy : y ∈ F.realLayer e j) :
    ⁅x, y⁆ ∈ F.realLayer (d + e) (i + j) :=
  F.lie_realLayer_le d e i j (LieSubmodule.lie_mem_lie hx hy)

noncomputable def realification : DegreeRankLieFiltration (ℝ ⊗[ℚ] L) s r where
  rank_le_degree := F.rank_le_degree
  layer d i := (F.realLayer d i).toSubmodule.restrictScalars ℚ
  lex_antitone := F.realLayer_lex_antitone
  one_eq_top := by rw [F.realLayer_one]; rfl
  rank_zero_eq_one d := by rw [F.realLayer_rank_zero_eq_one]
  overshoot d i h := by rw [F.realLayer_overshoot d i h]
  lie_mem := F.realLayer_lie_mem
  terminal := by rw [F.realLayer_terminal]; rfl

theorem realification_associatedDegree :
    F.realification.associatedDegree = F.associatedDegree.realification := rfl

theorem rational_inclusion_mem_realLayer {d i : ℕ} {x : L} (hx : x ∈ F.layer d i) :
    rationalLieInclusion x ∈ F.realLayer d i := LieSubmodule.tmul_mem_baseChange_of_mem 1 hx

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}

structure DegreeRankStructure (D : RationalFilteredNilmanifold L s d) (r : ℕ) where
  filtration : DegreeRankLieFiltration L s r
  associated : filtration.associatedDegree = D.filtration
  basis : ∀ i j : Fin (s + 1),
    Basis (Fin (finrank ℚ (filtration.layer i.val j.val))) ℚ (filtration.layer i.val j.val)

namespace DegreeRankStructure

variable {D : RationalFilteredNilmanifold L s d} (R : D.DegreeRankStructure r)

def ComplexityLE (p : ℝ) : Prop :=
  D.GeometryComplexityLE p ∧ ∀ i j a k, rationalLogHeight (D.basis.repr (R.basis i j a : L) k) ≤ p

theorem ComplexityLE.mono {p q : ℝ} (hR : R.ComplexityLE p) (hpq : p ≤ q) : R.ComplexityLE q :=
  ⟨GeometryComplexityLE.mono D hR.1 hpq, fun i j a k => (hR.2 i j a k).trans hpq⟩

theorem real_associated : R.filtration.realification.associatedDegree = D.filtration.realification := by
  rw [R.filtration.realification_associatedDegree, R.associated]

noncomputable def realSubgroup (i j : ℕ) : Subgroup D.RealGroup := R.filtration.realification.subgroup i j

theorem realSubgroup_le_degree (i j : ℕ) : R.realSubgroup i j ≤ D.filtration.realification.subgroup i := by
  intro x hx
  have h := R.filtration.realification.subgroup_le_associatedDegree i j hx
  change x.coord ∈ R.filtration.realification.associatedDegree.layer i at h
  change x.coord ∈ D.filtration.realification.layer i
  rwa [R.real_associated] at h

noncomputable def orbitEquiv {σ : Type*} (w : σ → ℕ) :
    D.filtration.realification.PolynomialOrbit w ≃*
      R.filtration.realification.associatedDegree.PolynomialOrbit w :=
  D.filtration.realification.orbitEquivOfEq R.real_associated.symm w

theorem orbitEquiv_eval {σ : Type*} (w : σ → ℕ)
    (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    R.filtration.realification.associatedDegree.polynomialOrbitEval w x (R.orbitEquiv w g) =
      D.filtration.realification.polynomialOrbitEval w x g :=
  D.filtration.realification.orbitEquivOfEq_eval R.real_associated.symm w g x

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

end DegreeRankStructure

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

namespace DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r t : ℕ}

def withRank (F : DegreeRankLieFiltration L s r) (ht : t ≤ s)
    (hterminal : F.layer s (t + 1) = ⊥) : DegreeRankLieFiltration L s t where
  rank_le_degree := ht
  layer := F.layer
  lex_antitone := F.lex_antitone
  one_eq_top := F.one_eq_top
  rank_zero_eq_one := F.rank_zero_eq_one
  overshoot := F.overshoot
  lie_mem := F.lie_mem
  terminal := hterminal

end DegreeRankLieFiltration

namespace RationalFilteredNilmanifold.DegreeRankStructure

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r t d : ℕ}
  {D : RationalFilteredNilmanifold L s d}

noncomputable def withRank (R : D.DegreeRankStructure r) (ht : t ≤ s)
    (hterminal : R.filtration.layer s (t + 1) = ⊥) : D.DegreeRankStructure t where
  filtration := R.filtration.withRank ht hterminal
  associated := R.associated
  basis := R.basis

theorem withRank_complexity (R : D.DegreeRankStructure r) (ht : t ≤ s)
    (hterminal : R.filtration.layer s (t + 1) = ⊥) {p : ℝ} (hR : R.ComplexityLE p) :
    (R.withRank ht hterminal).ComplexityLE p := hR

end RationalFilteredNilmanifold.DegreeRankStructure

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_native_degree_rank_structure (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p →
      ∃ R : D.DegreeRankStructure s, R.filtration = D.filtration.canonicalDegreeRank ∧
        R.ComplexityLE ((p + C) ^ C) := by
  obtain ⟨a, _, hbasis⟩ := exists_canonical_rank_basis_budget s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + (X + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro L _ _ d D p hp hD
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hcost : p + (p + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hex : ∀ i j : Fin (s + 1),
      ∃ b : Basis (Fin (finrank ℚ (D.filtration.rankLayer i.val j.val))) ℚ
          (D.filtration.rankLayer i.val j.val),
        ∀ k l, rationalLogHeight (D.basis.repr (b k : L) l) ≤ (p + a) ^ a := by
    intro i j
    obtain ⟨b, _, hb⟩ := hbasis D hp hD i.val j.val (Nat.le_of_lt_succ i.isLt)
    exact ⟨b, hb⟩
  choose b hb using hex
  let R : D.DegreeRankStructure s := {
    filtration := D.filtration.canonicalDegreeRank
    associated := D.filtration.canonicalDegreeRank_associatedDegree_eq
    basis := b }
  refine ⟨R, rfl, hD.mono D (by linarith), ?_⟩
  intro i j k l
  exact (hb i j k l).trans (by linarith)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t r d : ℕ}

theorem raiseStep_rankSubgroup_eq_bot (D : RationalFilteredNilmanifold L t d)
    (hts : t < s) (R : (D.raiseStep hts.le).DegreeRankStructure r) (j : ℕ) :
    R.realSubgroup s j = ⊥ := by
  apply bot_unique
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply NilpotentLieBCHGroup.ext
  change x.coord = 0
  have hm := R.realSubgroup_le_degree s j hx
  change x.coord ∈ D.filtration.realification.layer s at hm
  simpa only [D.filtration.realification.layer_eq_bot_above_step hts, Submodule.mem_bot] using hm

theorem exists_raised_degree_rank_structure (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {t r d : ℕ}
      (D : RationalFilteredNilmanifold L t d) (hts : t < s), r ≤ s →
      ∀ {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      ∃ R : (D.raiseStep hts.le).DegreeRankStructure r,
        R.ComplexityLE ((p + C) ^ C) ∧ R.realSubgroup s r = ⊥ := by
  obtain ⟨C, hC, hcanonical⟩ := exists_native_degree_rank_structure s
  refine ⟨C, hC, ?_⟩
  intro L _ _ t r d D hts hrs p hp hD
  obtain ⟨A, _, hA⟩ := hcanonical (D.raiseStep hts.le) hp (D.raiseStep_geometry hts.le hD)
  have hzero (j : ℕ) : A.filtration.layer s j = ⊥ := by
    apply bot_unique
    have h := A.filtration.layer_le_associatedDegree s j
    rw [A.associated] at h
    exact h.trans (D.filtration.layer_eq_bot_above_step hts).le
  let R := A.withRank hrs (hzero (r + 1))
  exact ⟨R, A.withRank_complexity hrs (hzero (r + 1)) hA,
    D.raiseStep_rankSubgroup_eq_bot hts R r⟩

namespace Niltest

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {σ : Type*} {w : σ → ℕ} {D : RationalFilteredNilmanifold L t d}

theorem raiseStep_rank_vertical (T : D.Niltest w) (hts : t < s)
    (R : (D.raiseStep hts.le).DegreeRankStructure r)
    (z : (D.raiseStep hts.le).RealGroup) (hz : z ∈ R.realSubgroup s r)
    (x : (D.raiseStep hts.le).Space) :
    (T.raiseStep hts.le).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (0 : L →ₗ[ℚ] ℚ) z.coord : ℝ) : CircleFourier.Circle) *
          (T.raiseStep hts.le).observable x := by
  rw [D.raiseStep_rankSubgroup_eq_bot hts R r] at hz
  have hz' : z = 1 := Subgroup.mem_bot.mp hz
  subst z
  simp

end Niltest

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end


