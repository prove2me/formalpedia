-- Prove2me | Definitions.Def_OAIErdos3B130
-- name    : OAIErdos3B130
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T08:36:51.97601+00:00
-- url     : https://prove2.me/theorems/ca734791-956e-4c4d-81cd-6fb634588c14
-- title:
--   OpenAI Erdős-3 split, definitions bundle 131 of 132
-- statement:
--   Definitions bundle 131 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B129`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 131 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieFiltration.FirstCoefficientSlowBound.mono`, `OAI.Erdos3.NilpotentLieFiltration.exists_reindexed_fast_coefficient_section`, `OAI.Erdos3.NilpotentLieFiltration.layerOne_equiv_grid`, `OAI.Erdos3.NilpotentLieFiltration.layerOne_equiv_norm`, `OAI.Erdos3.NilpotentLieFiltration.layerOne_equiv_rational_matrix`, `OAI.Erdos3.NilpotentLieFiltration.layerOne_equiv_representative`, `OAI.Erdos3.NilpotentLieFiltration.layerOne_equiv_symm_coordinates`, `OAI.Erdos3.NilpotentLieFiltration.layerOne_equiv_symm_norm`, `OAI.Erdos3.NilpotentLieFiltration.layerOne_rational_kernel_basis`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientHorizontal_section_grid`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientHorizontal_section_norm_bound`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientRepresentative`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientRepresentative_bound`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientRepresentative_grid`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientRepresentative_horizontal`, `OAI.Erdos3.NilpotentLieFiltration.realFastCoefficientRepresentative_mk`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientHorizontal_bound`, `OAI.Erdos3.NilpotentLieFiltration.realFirstCoefficientHorizontal_grid`, `OAI.Erdos3.NilpotentLieFiltration.realHorizontalSection_constant_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.realHorizontalSection_nonconstant_coordinate`, `OAI.Erdos3.NilpotentLieFiltration.realHorizontalSection_slow_bound`, `OAI.Erdos3.PreparedRelativeInitializerScalarInputs.recOn`, `OAI.Erdos3.PreparedRelativePatchPowerPassage`, `OAI.Erdos3.RankPreparationFamily.DeterminingIndex`, `OAI.Erdos3.RankPreparationFamily.PreparedCoordinate`, `OAI.Erdos3.RankPreparationFamily.PreparedHeights.basisAxisScale_le_exp`, `OAI.Erdos3.RankPreparationFamily.PreparedHeights.exists_bounded_integral_bases`, `OAI.Erdos3.RankPreparationFamily.PreparedHeights.exists_bounded_integral_bases_of_sized`, `OAI.Erdos3.RankPreparationFamily.PreparedHeights.exists_canonical_sampler_geometry`, `OAI.Erdos3.RankPreparationFamily.PreparedHeights.exists_early_late_sampler_geometry`, `OAI.Erdos3.RankPreparationFamily.PreparedHeights.mono_parameter`, `OAI.Erdos3.RankPreparationFamily.centeredDeterminingPolynomial`, `OAI.Erdos3.RankPreparationFamily.centeredDeterminingPolynomial_support`, `OAI.Erdos3.RankPreparationFamily.determiningCenterCoordinate`, `OAI.Erdos3.RankPreparationFamily.determiningMatrix`, `OAI.Erdos3.RankPreparationFamily.determiningPolynomial`, `OAI.Erdos3.RankPreparationFamily.determiningPolynomial_degree`, `OAI.Erdos3.RankPreparationFamily.determiningWeight`, `OAI.Erdos3.RankPreparationFamily.dilatedCenteredDeterminingPatch`, `OAI.Erdos3.RankPreparationFamily.dilatedCenteredDeterminingPatch_kernel`, `OAI.Erdos3.RankPreparationFamily.dilatedCenteredDeterminingPatch_weight`, `OAI.Erdos3.RankPreparationFamily.dilatedCenteredDeterminingPolynomial`, `OAI.Erdos3.RankPreparationFamily.dilatedCenteredDeterminingPolynomial_eval`, `OAI.Erdos3.RankPreparationFamily.dilatedCenteredDeterminingPolynomial_support`, `OAI.Erdos3.RankPreparationFamily.dilatedSortedDeterminingMatrix`, `OAI.Erdos3.RankPreparationFamily.integral_determining_card`, `OAI.Erdos3.RankPreparationFamily.padDeterminingRecovered`, `OAI.Erdos3.RankPreparationFamily.padDeterminingRecovered_lip`, `OAI.Erdos3.RankPreparationFamily.padDeterminingRecovered_value`, `OAI.Erdos3.RankPreparationFamily.sortedDeterminingCenter`, `OAI.Erdos3.RankPreparationFamily.sortedDeterminingMatrix`, `OAI.Erdos3.RankPreparationFamily.sortedDeterminingPolynomial`, `OAI.Erdos3.RankPreparationFamily.sortedDeterminingPolynomial_support`, `OAI.Erdos3.RankPreparationFamily.sortedDeterminingRecovered_rank`, `OAI.Erdos3.RankPreparationLayer.exists_bounded_integral_basis`, `OAI.Erdos3.RankPreparationLayer.rank_le_coord_card`, `OAI.Erdos3.RankPreparationLayer.shortIntegralBasisNormBound_le_exp`, `OAI.Erdos3.RelativePatchFinPositivePowerRule`, `OAI.Erdos3.RelativePatchFinPowerInductionRule`, `OAI.Erdos3.VectorPolynomial.EnlargedPreparedCommonKernel`, `OAI.Erdos3.VectorPolynomial.EnlargedPreparedCommonKernelWithCutoff`, `OAI.Erdos3.VectorPolynomial.EnlargedPreparedCommonSamplerBlock`, `OAI.Erdos3.VectorPolynomial.PreparedSamplerContinuous`, `OAI.Erdos3.VectorPolynomial.enlargedPreparedCommonCanonicalSelection`, `OAI.Erdos3.VectorPolynomial.enlargedPreparedCommonCanonicalSelectionWithCutoff`, `OAI.Erdos3.VectorPolynomial.enlargedPreparedCommonCanonicalSelectionWithCutoff_val`, `OAI.Erdos3.VectorPolynomial.enlargedPreparedCommonCanonicalSelection_val`, `OAI.Erdos3.VectorPolynomial.enlargedPreparedCommonKernelWithCutoff_analytic_capacity`, `OAI.Erdos3.VectorPolynomial.enlargedPreparedCommonKernel_analytic_capacity`, `OAI.Erdos3.VectorPolynomial.enlargedPreparedCommonSamplerBlock_positive`, `OAI.Erdos3.VectorPolynomial.enlargedPreparedCommonSamplerBlock_spectrum`, `OAI.Erdos3.VectorPolynomial.enlargedPreparedCommonSamplerBlock_uniform`, `OAI.Erdos3.VectorPolynomial.enlargedPreparedCommonSamplerDimension`, `OAI.Erdos3.VectorPolynomial.enlargedPreparedCommonSamplerDimension_ge`, `OAI.Erdos3.VectorPolynomial.enlargedPreparedCommonSamplerDimension_polynomial`, `OAI.Erdos3.VectorPolynomial.enlargedPreparedCommonSampler_dimensions`, `OAI.Erdos3.VectorPolynomial.enlargedPreparedCommonSampler_variables_card`, `OAI.Erdos3.VectorPolynomial.enlargedPreparedRankKernelEmbedding`, `OAI.Erdos3.VectorPolynomial.enlargedPreparedRankPrincipalEmbedding`, `OAI.Erdos3.VectorPolynomial.enlargedPreparedRankSpatialEmbedding`, `OAI.Erdos3.VectorPolynomial.exists_preparedCenteredForecastSpatialLog_budget`, `OAI.Erdos3.VectorPolynomial.preparedCenteredForecastSpatialLog`, `OAI.Erdos3.VectorPolynomial.preparedCenteredForecastThresholdExponent`, `OAI.Erdos3.VectorPolynomial.preparedCenteredForecast_badRadius_bound`, `OAI.Erdos3.VectorPolynomial.preparedCenteredForecast_threshold_inverse`, `OAI.Erdos3.VectorPolynomial.preparedCommonBlockCount`, `OAI.Erdos3.VectorPolynomial.preparedCommonBlockCount_ge`, `OAI.Erdos3.VectorPolynomial.preparedCommonBlockCount_positive`, `OAI.Erdos3.VectorPolynomial.preparedCommonBlockCount_spectrum`, `OAI.Erdos3.VectorPolynomial.preparedCommonSamplerDimension`, `OAI.Erdos3.VectorPolynomial.preparedFinalScalarBudget`, `OAI.Erdos3.VectorPolynomial.preparedInitialRankKernelEmbedding`, `OAI.Erdos3.VectorPolynomial.preparedInitialRankPrincipalEmbedding`, `OAI.Erdos3.VectorPolynomial.preparedInitialRankSpatialEmbedding`, `OAI.Erdos3.VectorPolynomial.preparedSamplerBlockCount`, `OAI.Erdos3.VectorPolynomial.preparedSamplerBlockCount_positive`, `OAI.Erdos3.VectorPolynomial.preparedSamplerBlockCount_spectrum`, `OAI.Erdos3.VectorPolynomial.preparedSamplerTransverse`, `OAI.Erdos3.VectorPolynomial.preparedSampler_axis_card`, `OAI.Erdos3.VectorPolynomial.preparedSlicedForecastChildSize`, `OAI.Erdos3.VectorPolynomial.preparedSlicedForecastCommonFloor`, `OAI.Erdos3.VectorPolynomial.preparedSlicedForecastCommonFloorExponent`, `OAI.Erdos3.VectorPolynomial.preparedSlicedForecastDensity`, `OAI.Erdos3.VectorPolynomial.preparedSlicedForecastKernelLog`, `OAI.Erdos3.VectorPolynomial.preparedSlicedForecastPrimitiveCap`, `OAI.Erdos3.VectorPolynomial.preparedSlicedForecastPrimitiveCap_one_le`, `OAI.Erdos3.VectorPolynomial.preparedSlicedForecastSourceLog`, `OAI.Erdos3.VectorPolynomial.preparedSlicedForecastTailCap`, `OAI.Erdos3.VectorPolynomial.preparedSlicedForecastTailLog`, `OAI.Erdos3.VectorPolynomial.preparedSlicedForecastTailLog_nonneg`, `OAI.Erdos3.VectorPolynomial.preparedSpatialKernelBlocks`, `OAI.Erdos3.coarseSpatialLogs_nonneg`, `OAI.Erdos3.coarseSpatialPartitionLog`, `OAI.Erdos3.coarseSpatialReciprocalLog`, `OAI.Erdos3.modularCoefficientPrimeThreshold`, `OAI.Erdos3.modularInitialBlockCount`, `OAI.Erdos3.modularInitialBlockCount_linear_bound`, `OAI.Erdos3.modularInitialBlockCount_two_dimensions`, `OAI.Erdos3.modularInitialRankStrength`, `OAI.Erdos3.modularRankSmallBallExponent`, `OAI.Erdos3.normalizedTuple_log_envelopes`, `OAI.Erdos3.normalizedTuple_log_envelopes_of_le`, `OAI.Erdos3.normalizedTuple_log_mono`, `OAI.Erdos3.preparationCoordinateCap`, `OAI.Erdos3.preparationCoordinateCap_bounds`, `OAI.Erdos3.preparationModulusCap`, `OAI.Erdos3.preparationOscillationCap`, `OAI.Erdos3.preparationShrink`, `OAI.Erdos3.preparedIntegralBasisExponent`, `OAI.Erdos3.preparedRelativeInitializerVariableCount`, `OAI.Erdos3.rational_horizontal_basis_transport`, `OAI.Erdos3.reindexCoordinateSection`, `OAI.Erdos3.reindexCoordinateSection_right_inverse`, `OAI.Erdos3.spatialTupleCoarseMesh_inv_bound`, `OAI.Erdos3.spatialTupleCoarseMesh_partition_budget`, `OAI.Erdos3.tupleEarlyLogEnvelope`, `OAI.Erdos3.tupleLateLogEnvelope`, `OAI.Erdos3.tupleSideLogEnvelope`, `OAI.Erdos3.tupleSideLogEnvelope_mono`, `OAI.Erdos3.tupleWidthLogEnvelope`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B131

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReindexedFastCoefficientSection
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype ι]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realFirstCoefficientHorizontal_grid (l : ℕ) (x : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientGrid e ω hF w l x) :
    ((F.layerOneBasis e ω hF).baseChange ℝ).equivFun
      (F.realFirstCoefficientHorizontal w x) ∈ realDenominatorGrid l := by
  obtain ⟨v, hv⟩ := hx
  refine ⟨fun i => v (F.horizontalCoefficientIndex e ω hF w i), ?_⟩
  funext i
  change (v (F.horizontalCoefficientIndex e ω hF w i) : ℝ) =
    (l : ℝ) * ((F.layerOneBasis e ω hF).baseChange ℝ).repr
      (F.realFirstCoefficientHorizontal w x) i
  rw [F.realFirstCoefficientHorizontal_coordinates]
  exact congrFun hv _

theorem realFirstCoefficientHorizontal_bound (T : σ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (x : F.RealFirstCoefficientModule w) (hx : F.FirstCoefficientSlowBound e ω hF w T M x) :
    ‖((F.layerOneBasis e ω hF).baseChange ℝ).equivFun
      (F.realFirstCoefficientHorizontal w x)‖ ≤ M := by
  apply (pi_norm_le_iff_of_nonneg hM).mpr
  intro i
  rw [Real.norm_eq_abs, Basis.equivFun_apply, F.realFirstCoefficientHorizontal_coordinates]
  simpa only [horizontalCoefficientIndex, monomialScale_zero, div_one] using
    hx (F.horizontalCoefficientIndex e ω hF w i)

omit [Fintype ι] in
theorem realHorizontalSection_constant_coordinate
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) (z : FirstCoefficientIndex w ω) (hz : z.val.1 = 0) :
    (F.realFirstCoefficientBasis e ω hF w).repr (F.realFirstCoefficientHorizontalSection w x) z =
      ((F.layerOneBasis e ω hF).baseChange ℝ).repr x (layerOneIndexOfConstant ω w z hz) := by
  have h := F.realFirstCoefficientHorizontal_coordinates e ω hF w
    (F.realFirstCoefficientHorizontalSection w x) (layerOneIndexOfConstant ω w z hz)
  rw [F.realFirstCoefficientHorizontal_section, F.horizontalCoefficientIndex_of_constant] at h
  exact h.symm

omit [Fintype ι] in
theorem realHorizontalSection_nonconstant_coordinate
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) (z : FirstCoefficientIndex w ω) (hz : z.val.1 ≠ 0) :
    (F.realFirstCoefficientBasis e ω hF w).repr (F.realFirstCoefficientHorizontalSection w x) z = 0 := by
  classical
  have h := F.realFirstCoefficientHorizontal_projector_repr e ω hF w
    (F.realFirstCoefficientHorizontalSection w x) z
  simpa only [F.realFirstCoefficientHorizontal_section, hz, ite_false] using h

theorem realHorizontalSection_slow_bound (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) {M : ℝ} (hM : 0 ≤ M)
    (hx : ‖((F.layerOneBasis e ω hF).baseChange ℝ).equivFun x‖ ≤ M) :
    F.FirstCoefficientSlowBound e ω hF w T M (F.realFirstCoefficientHorizontalSection w x) := by
  classical
  intro z
  by_cases hz : z.val.1 = 0
  · rw [F.realHorizontalSection_constant_coordinate e ω hF w x z hz,
      hz, monomialScale_zero, div_one]
    exact (norm_le_pi_norm (((F.layerOneBasis e ω hF).baseChange ℝ).equivFun x)
      (layerOneIndexOfConstant ω w z hz)).trans hx
  · rw [F.realHorizontalSection_nonconstant_coordinate e ω hF w x z hz, abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT _).le

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

section Bounds

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem FirstCoefficientSlowBound.mono (w : σ → ℕ) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M N : ℝ} (hMN : M ≤ N) (x : F.RealFirstCoefficientModule w)
    (hx : F.FirstCoefficientSlowBound e ω hF w T M x) :
    F.FirstCoefficientSlowBound e ω hF w T N x := by
  intro z
  exact (hx z).trans (div_le_div_of_nonneg_right hMN (monomialScale_pos T hT z.val.1).le)

end Bounds

variable {σ ι ν L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ν] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

local notation "E" => F.RealFirstCoefficientModule w
local notation "J" => F.realFirstCoefficientFastSubmodule w hw U

noncomputable def realFastCoefficientRepresentative (b : Basis ν ℝ (E ⧸ J))
    (sectionMap : (ν → ℝ) →ₗ[ℝ] E) : (E ⧸ J) →ₗ[ℝ] E :=
  sectionMap.comp b.equivFun.toLinearMap

theorem realFastCoefficientRepresentative_mk (b : Basis ν ℝ (E ⧸ J))
    (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y) (x : E ⧸ J) :
    (J).mkQ (F.realFastCoefficientRepresentative w hw U b sectionMap x) = x := by
  change (J).mkQ (sectionMap (b.equivFun x)) = x
  rw [hsection, LinearEquiv.symm_apply_apply]

theorem realFastCoefficientRepresentative_horizontal (b : Basis ν ℝ (E ⧸ J))
    (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y) (x : E ⧸ J) :
    F.realFirstCoefficientHorizontal w (F.realFastCoefficientRepresentative w hw U b sectionMap x) =
      F.realFastCoefficientHorizontal w hw U x := by
  have h := congrArg (F.realFastCoefficientHorizontal w hw U)
    (F.realFastCoefficientRepresentative_mk w hw U b sectionMap hsection x)
  exact h

theorem realFastCoefficientRepresentative_bound
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (b : Basis ν ℝ (E ⧸ J)) (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (rows : ν → FirstCoefficientIndex w ω) (T : σ → ℝ) {C M : ℝ}
    (hbound : ∀ y, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
      F.FirstCoefficientSlowBound e ω hF w T (C * M) (sectionMap y))
    (x : E ⧸ J) (hx : ∀ i, |b.equivFun x i| ≤ M / monomialScale T (rows i).val.1) :
    F.FirstCoefficientSlowBound e ω hF w T (C * M)
      (F.realFastCoefficientRepresentative w hw U b sectionMap x) := hbound (b.equivFun x) hx

theorem realFastCoefficientRepresentative_grid
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (b : Basis ν ℝ (E ⧸ J)) (sectionMap : (ν → ℝ) →ₗ[ℝ] E) (l m : ℕ)
    (hgrid : ∀ y, y ∈ realDenominatorGrid l → F.FirstCoefficientGrid e ω hF w m (sectionMap y))
    (x : E ⧸ J) (hx : b.equivFun x ∈ realDenominatorGrid l) :
    F.FirstCoefficientGrid e ω hF w m
      (F.realFastCoefficientRepresentative w hw U b sectionMap x) := hgrid (b.equivFun x) hx

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι ν L : Type*} [Fintype ι] [Fintype ν] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

local notation "E" => F.RealFirstCoefficientModule w
local notation "J" => F.realFirstCoefficientFastSubmodule w hw U
local notation "Hq" => F.realFastCoefficientHorizontal w hw U
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))

theorem realFastCoefficientHorizontal_section_norm_bound
    (b : Basis ν ℝ (E ⧸ J)) (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y)
    (rows : ν → FirstCoefficientIndex w ω) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ M, 0 ≤ M → ∀ y : ν → ℝ,
      (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF w T (C * M) (sectionMap y))
    (x : E ⧸ J) :
    ‖cH (Hq x)‖ ≤ C * ‖basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1) x‖ := by
  let N := basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1)
  let x' := F.realFastCoefficientRepresentative w hw U b sectionMap x
  have hcoords : ∀ i, |b.equivFun x i| ≤ ‖N x‖ / monomialScale T (rows i).val.1 :=
    (basisWeightedCoordinates_norm_le_iff b _ (fun i => monomialScale_pos T hT _)
      (norm_nonneg _) x).mp le_rfl
  have hx' : F.FirstCoefficientSlowBound e ω hF w T (C * ‖N x‖) x' :=
    F.realFastCoefficientRepresentative_bound w hw U e ω hF b sectionMap rows T
      (hbound ‖N x‖ (norm_nonneg _)) x hcoords
  have hhorizontal := F.realFastCoefficientRepresentative_horizontal w hw U b sectionMap hsection x
  calc
    ‖cH (Hq x)‖ = ‖cH (F.realFirstCoefficientHorizontal w x')‖ :=
      (congrArg (fun y => ‖cH y‖) hhorizontal).symm
    _ ≤ C * ‖N x‖ := F.realFirstCoefficientHorizontal_bound e ω hF w T
      (mul_nonneg hC (norm_nonneg _)) x' hx'

theorem realFastCoefficientHorizontal_section_grid
    (b : Basis ν ℝ (E ⧸ J)) (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y)
    (l m : ℕ)
    (hgrid : ∀ y : ν → ℝ, y ∈ realDenominatorGrid l →
      F.FirstCoefficientGrid e ω hF w m (sectionMap y))
    (x : E ⧸ J) (hx : b.equivFun x ∈ realDenominatorGrid l) :
    cH (Hq x) ∈ realDenominatorGrid m := by
  have hx' := F.realFastCoefficientRepresentative_grid w hw U e ω hF b sectionMap l m hgrid x hx
  have hhorizontal := F.realFastCoefficientRepresentative_horizontal w hw U b sectionMap hsection x
  have hg := F.realFirstCoefficientHorizontal_grid e ω hF w m _ hx'
  exact (congrArg (fun y => cH y ∈ realDenominatorGrid m) hhorizontal).mp hg

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module

noncomputable def reindexCoordinateSection {ν E : Type*} [AddCommGroup E] [Module ℝ E]
    (R : (ν → ℝ) →ₗ[ℝ] E) (e : Equiv.Perm ν) : (ν → ℝ) →ₗ[ℝ] E where
  toFun y := R (fun i => y (e.symm i))
  map_add' _ _ := R.map_add _ _
  map_smul' r _ := R.map_smul r _

theorem reindexCoordinateSection_right_inverse {ν E Q : Type*} [Fintype ν]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup Q] [Module ℝ Q]
    (P : E →ₗ[ℝ] Q) (b : Basis ν ℝ Q) (R : (ν → ℝ) →ₗ[ℝ] E)
    (hR : ∀ y, P (R y) = b.equivFun.symm y) (e : Equiv.Perm ν) (y : ν → ℝ) :
    P (reindexCoordinateSection R e y) = (b.reindex e.symm).equivFun.symm y := by
  apply (b.reindex e.symm).equivFun.injective
  rw [LinearEquiv.apply_symm_apply, basis_reindex_equivFun]
  change (fun i => b.equivFun (P (R (fun j => y (e.symm j)))) (e i)) = y
  rw [hR, LinearEquiv.apply_symm_apply]
  funext i
  exact congrArg y (e.symm_apply_apply i)

namespace NilpotentLieFiltration

theorem exists_reindexed_fast_coefficient_section
    {σ ι ν L : Type*} [Fintype ν] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (b : Basis ν ℝ (F.RealFirstCoefficientModule w ⧸ F.realFirstCoefficientFastSubmodule w hw U))
    (rows : ν → FirstCoefficientIndex w ω) (R : (ν → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w)
    (hR : ∀ y, (F.realFirstCoefficientFastSubmodule w hw U).mkQ (R y) = b.equivFun.symm y)
    (δ : ℕ) (C : ℝ)
    (hproj : ∀ l x, F.FirstCoefficientGrid e ω hF w l x →
      b.equivFun ((F.realFirstCoefficientFastSubmodule w hw U).mkQ x) ∈ realDenominatorGrid (δ * l))
    (hgrid : ∀ l y, y ∈ realDenominatorGrid l → F.FirstCoefficientGrid e ω hF w (δ * l) (R y))
    (hweighted : ∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
      (∀ x, F.FirstCoefficientSlowBound e ω hF w T M x → ∀ i,
        |b.equivFun ((F.realFirstCoefficientFastSubmodule w hw U).mkQ x) i| ≤
          C * M / monomialScale T (rows i).val.1) ∧
      (∀ y, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF w T (C * M) (R y)))
    (perm : Equiv.Perm ν) :
    ∃ R' : (ν → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w,
      (∀ y, (F.realFirstCoefficientFastSubmodule w hw U).mkQ (R' y) =
        (b.reindex perm.symm).equivFun.symm y) ∧
      (∀ l x, F.FirstCoefficientGrid e ω hF w l x →
        (b.reindex perm.symm).equivFun ((F.realFirstCoefficientFastSubmodule w hw U).mkQ x) ∈
          realDenominatorGrid (δ * l)) ∧
      (∀ l y, y ∈ realDenominatorGrid l → F.FirstCoefficientGrid e ω hF w (δ * l) (R' y)) ∧
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
        (∀ x, F.FirstCoefficientSlowBound e ω hF w T M x → ∀ i,
          |(b.reindex perm.symm).equivFun ((F.realFirstCoefficientFastSubmodule w hw U).mkQ x) i| ≤
            C * M / monomialScale T (rows (perm i)).val.1) ∧
        (∀ y, (∀ i, |y i| ≤ M / monomialScale T (rows (perm i)).val.1) →
          F.FirstCoefficientSlowBound e ω hF w T (C * M) (R' y)) := by
  refine ⟨reindexCoordinateSection R perm,
    reindexCoordinateSection_right_inverse _ b R hR perm, ?_, ?_, ?_⟩
  · intro l x hx
    exact basis_reindex_grid b perm (δ * l) _ (hproj l x hx)
  · intro l y hy
    exact hgrid l _ (realDenominatorGrid_comp l y hy perm.symm)
  · intro T hT M hM
    obtain ⟨hproj', hlift'⟩ := hweighted T hT M hM
    constructor
    · intro x hx i
      simpa only [basis_reindex_equivFun] using hproj' x hx (perm i)
    · intro y hy
      apply hlift' (fun i => y (perm.symm i))
      intro i
      simpa only [Equiv.apply_symm_apply] using hy (perm.symm i)

end NilpotentLieFiltration
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ControlledLayerOneCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype ι]
  [LieRing L] [LieAlgebra ℚ L] {s a d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
  (b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
    F.realFirstCoefficientFastSubmodule w hw U))
  (ha : a ≤ d) (η : (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)))
  (hη : ∀ x, η (fun i => b.equivFun x (Fin.castLE ha i)) = F.realFastCoefficientHorizontal w hw U x)

include hη

omit [Fintype ι] in
theorem layerOne_equiv_symm_coordinates (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    η.symm x = fun i => b.equivFun ((F.realFirstCoefficientFastSubmodule w hw U).mkQ
      (F.realFirstCoefficientHorizontalSection w x)) (Fin.castLE ha i) := by
  apply η.injective
  rw [LinearEquiv.apply_symm_apply, hη]
  exact (F.realFirstCoefficientHorizontal_section w x).symm

omit [Fintype ι] in
theorem layerOne_equiv_representative
    (R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w)
    (hR : ∀ y, (F.realFirstCoefficientFastSubmodule w hw U).mkQ (R y) = b.equivFun.symm y)
    (x : Fin a → ℝ) :
    η x = F.realFirstCoefficientHorizontal w (R (extendInitialCoordinates x)) := by
  have h := hη (b.equivFun.symm (extendInitialCoordinates x))
  simp only [LinearEquiv.apply_symm_apply, extendInitialCoordinates_castLE] at h
  rw [← hR] at h
  exact h

theorem layerOne_equiv_grid (l m : ℕ)
    (R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w)
    (hR : ∀ y, (F.realFirstCoefficientFastSubmodule w hw U).mkQ (R y) = b.equivFun.symm y)
    (hgrid : ∀ y, y ∈ realDenominatorGrid l → F.FirstCoefficientGrid e ω hF w m (R y))
    (x : Fin a → ℝ) (hx : x ∈ realDenominatorGrid l) :
    ((F.layerOneBasis e ω hF).baseChange ℝ).equivFun (η x) ∈ realDenominatorGrid m := by
  rw [F.layerOne_equiv_representative w hw U b ha η hη R hR x]
  exact F.realFirstCoefficientHorizontal_grid e ω hF w m _
    (hgrid _ (extendInitialCoordinates_grid l x hx))

theorem layerOne_equiv_norm (C : ℝ) (hC : 0 ≤ C)
    (R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w)
    (hR : ∀ y, (F.realFirstCoefficientFastSubmodule w hw U).mkQ (R y) = b.equivFun.symm y)
    (hbound : ∀ (y : Fin d → ℝ) (M : ℝ), 0 ≤ M → (∀ j, |y j| ≤ M) →
      F.FirstCoefficientSlowBound e ω hF w (fun _ => 1) (C * M) (R y))
    (x : Fin a → ℝ) :
    ‖((F.layerOneBasis e ω hF).baseChange ℝ).equivFun (η x)‖ ≤ C * ‖x‖ := by
  rw [F.layerOne_equiv_representative w hw U b ha η hη R hR x]
  apply F.realFirstCoefficientHorizontal_bound e ω hF w (fun _ => 1)
    (mul_nonneg hC (norm_nonneg _))
  apply hbound _ ‖x‖ (norm_nonneg x)
  intro j
  exact (norm_le_pi_norm (extendInitialCoordinates x : Fin d → ℝ) j).trans
    (norm_extendInitialCoordinates_le x)

theorem layerOne_equiv_symm_norm (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (x : F.RealFirstCoefficientModule w) (M : ℝ), 0 ≤ M →
      F.FirstCoefficientSlowBound e ω hF w (fun _ => 1) M x → ∀ j,
        |b.equivFun ((F.realFirstCoefficientFastSubmodule w hw U).mkQ x) j| ≤ C * M)
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    ‖η.symm x‖ ≤ C * ‖((F.layerOneBasis e ω hF).baseChange ℝ).equivFun x‖ := by
  rw [F.layerOne_equiv_symm_coordinates w hw U b ha η hη x]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg _))).mpr
  intro i
  exact hbound _ _ (norm_nonneg _) (F.realHorizontalSection_slow_bound e ω hF w
    (fun _ => 1) (by intro i; norm_num) x (norm_nonneg _) le_rfl) (Fin.castLE ha i)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.LayerOneProjectionMatrixBounds
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct Matrix

theorem rational_horizontal_basis_transport
    {V ι κ ν : Type*} [AddCommGroup V] [Module ℚ V]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (b : Basis ι ℚ V) (η : (κ → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] V))
    (A : Matrix ι κ ℚ)
    (hA : ∀ x, (b.baseChange ℝ).equivFun (η x) = A.map (Rat.castHom ℝ) *ᵥ x)
    (K : Submodule ℝ (κ → ℝ)) (Q : Matrix κ ν ℚ)
    (hK : K = Submodule.span ℝ (Set.range (Q.map (Rat.castHom ℝ)).col))
    (hQ : LinearIndependent ℝ (Q.map (Rat.castHom ℝ)).col)
    {H J : ℕ} (hAH : ∀ i j, RationalHeightLE (A i j) H)
    (hQJ : ∀ i j, RationalHeightLE (Q i j) J) :
    ∃ v : ν → V,
      (∀ j, (1 : ℝ) ⊗ₜ[ℚ] v j = η ((Q.map (Rat.castHom ℝ)).col j)) ∧
      K.map η.toLinearMap = (Submodule.span ℚ (Set.range v)).baseChange ℝ ∧
      LinearIndependent ℚ v ∧
      ∀ i j, RationalHeightLE (b.repr (v j) i) ((Fintype.card κ + 1) * (H * J) ^ Fintype.card κ) := by
  let v : ν → V := fun j => b.equivFun.symm ((A * Q).col j)
  have hvc (i : ι) (j : ν) : b.repr (v j) i = (A * Q) i j :=
    congrFun (b.equivFun.apply_symm_apply ((A * Q).col j)) i
  have hv (j : ν) : (1 : ℝ) ⊗ₜ[ℚ] v j = η ((Q.map (Rat.castHom ℝ)).col j) := by
    apply (b.baseChange ℝ).equivFun.injective
    rw [hA]
    funext i
    rw [Basis.equivFun_apply, Basis.baseChange_repr_tmul, hvc]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Algebra.smul_def]
  refine ⟨v, hv, ?_, ?_, ?_⟩
  · rw [hK, Submodule.map_span, Submodule.baseChange_span]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨v j, ⟨j, rfl⟩, hv j⟩
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨_, ⟨j, rfl⟩, (hv j).symm⟩
  · have hreal : LinearIndependent ℝ (fun j => (1 : ℝ) ⊗ₜ[ℚ] v j) := by
      simpa only [hv, Function.comp_def, LinearEquiv.coe_coe] using
        hQ.map' η.toLinearMap (LinearMap.ker_eq_bot.mpr η.injective)
    apply LinearIndependent.of_comp (TensorProduct.mk ℚ ℝ V 1)
    exact LinearIndependent.restrict_scalars' ℚ hreal
  · intro i j
    rw [hvc]
    exact rationalHeightLE_matrix_mul A Q hAH hQJ i j

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct Matrix

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s a d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
  (b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
    F.realFirstCoefficientFastSubmodule w hw U))
  (ha : a ≤ d) (η : (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)))
  (hη : ∀ x, η (fun i => b.equivFun x (Fin.castLE ha i)) = F.realFastCoefficientHorizontal w hw U x)
  (R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w)
  (hR : ∀ y, (F.realFirstCoefficientFastSubmodule w hw U).mkQ (R y) = b.equivFun.symm y)
  (l m : ℕ) (hm : 0 < m) (C : ℝ) (hC : 0 ≤ C)
  (hgrid : ∀ y, y ∈ realDenominatorGrid l → F.FirstCoefficientGrid e ω hF w m (R y))
  (hbound : ∀ (y : Fin d → ℝ) (M : ℝ), 0 ≤ M → (∀ j, |y j| ≤ M) →
    F.FirstCoefficientSlowBound e ω hF w (fun _ => 1) (C * M) (R y))

include hη hR hm hC hgrid hbound

theorem layerOne_equiv_rational_matrix :
    ∃ A : Matrix (LayerOneBasisIndex ω) (Fin a) ℚ,
      (∀ i j, RationalHeightLE (A i j) (max m (Nat.ceil ((m : ℝ) * C)))) ∧
      ∀ x, ((F.layerOneBasis e ω hF).baseChange ℝ).equivFun (η x) =
        A.map (Rat.castHom ℝ) *ᵥ x := by
  exact exists_bounded_rational_map_matrix
    (((F.layerOneBasis e ω hF).baseChange ℝ).equivFun.toLinearMap.comp η.toLinearMap)
    m hm (fun j => F.layerOne_equiv_grid e ω hF w hw U b ha η hη l m R hR hgrid
      (Pi.single j 1) (realDenominatorGrid_single l j)) C
    (F.layerOne_equiv_norm e ω hF w hw U b ha η hη C hC R hR hbound)

theorem layerOne_rational_kernel_basis {ν : Type*}
    (K : Submodule ℝ (Fin a → ℝ)) (Q : Matrix (Fin a) ν ℚ)
    (hK : K = Submodule.span ℝ (Set.range (Q.map (Rat.castHom ℝ)).col))
    (hQ : LinearIndependent ℝ (Q.map (Rat.castHom ℝ)).col)
    {J : ℕ} (hQJ : ∀ i j, RationalHeightLE (Q i j) J) :
    ∃ v : ν → L ⧸ F.layer 2,
      (∀ j, (1 : ℝ) ⊗ₜ[ℚ] v j = η ((Q.map (Rat.castHom ℝ)).col j)) ∧
      K.map η.toLinearMap = (Submodule.span ℚ (Set.range v)).baseChange ℝ ∧
      LinearIndependent ℚ v ∧
      ∀ i j, RationalHeightLE ((F.layerOneBasis e ω hF).repr (v j) i)
        ((a + 1) * (max m (Nat.ceil ((m : ℝ) * C)) * J) ^ a) := by
  obtain ⟨A, hA, heq⟩ := F.layerOne_equiv_rational_matrix e ω hF w hw U b ha η hη
    R hR l m hm C hC hgrid hbound
  simpa only [Fintype.card_fin] using rational_horizontal_basis_transport
    (F.layerOneBasis e ω hF) η A heq K Q hK hQ hA hQJ

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct NNReal Matrix

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s a d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
  (b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
    F.realFirstCoefficientFastSubmodule w hw U))
  (ha : a ≤ d) (η : (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)))
  (hη : ∀ x, η (fun i => b.equivFun x (Fin.castLE ha i)) = F.realFastCoefficientHorizontal w hw U x)
  (A : Matrix (LayerOneBasisIndex ω) (Fin a) ℚ)
  (hA : ∀ x, ((F.layerOneBasis e ω hF).baseChange ℝ).equivFun (η x) =
    A.map (Rat.castHom ℝ) *ᵥ x)

include hη hA

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedTupleSideThreshold
namespace OAI

section

namespace Erdos3

noncomputable def tupleEarlyLogEnvelope {A : Type*} [Semiring A] (p E : A) : A :=
  p + (p ^ 3 + anisotropicSpatialCapLog p) + (coefficientErrorVolumeLog p + 4) +
    spatialDisplacementEnvelope p + E + 3

noncomputable def tupleWidthLogEnvelope {A : Type*} [Semiring A] (p E : A) : A :=
  2 * (tupleEarlyLogEnvelope p E + spatialTupleToleranceLog (tupleEarlyLogEnvelope p E)) + 4

noncomputable def tupleLateLogEnvelope {A : Type*} [Semiring A] (p E l : A) : A :=
  spatialDiscretizationEnvelope p l + spatialMeshEnvelope p l + spatialLipschitzCostEnvelope p l +
    spatialTupleToleranceLog (tupleEarlyLogEnvelope p E) + E + 3 + 2 * l +
    (1 + 2 * p) + (1 + 2 * p) * p + p + 40

noncomputable def tupleSideLogEnvelope {A : Type*} [Semiring A] (p E l : A) : A :=
  3 * tupleLateLogEnvelope p E l + tupleWidthLogEnvelope p E + 3 * l + 17

theorem normalizedTuple_log_envelopes (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) {p E l : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l)
    (hq : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hN : (Fintype.card N : ℝ) ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) :
    normalizedTupleWidthLog N s p E ≤ tupleWidthLogEnvelope p E ∧
      normalizedTupleSideLog X N s p E l ≤ tupleSideLogEnvelope p E l := by
  obtain ⟨he, hd, hcoords⟩ := spatialAuxiliaryDimensions (N := N) s hG hN
  have hdis := spatialDisplacementLog_le_envelope _ _ _ _ hp hq hd he hN
  have hearly : anisotropicTupleEarlyBudget N s p (E + 3) ≤ tupleEarlyLogEnvelope p E := by
    unfold anisotropicTupleEarlyBudget tupleEarlyLogEnvelope
    linarith
  have hearly0 := (anisotropicTupleEarlyBudget_bounds N s hp (by linarith : 0 ≤ E + 3)).1
  have ht : spatialTupleToleranceLog (anisotropicTupleEarlyBudget N s p (E + 3)) ≤
      spatialTupleToleranceLog (tupleEarlyLogEnvelope p E) := by
    unfold spatialTupleToleranceLog
    gcongr
  have hw : normalizedTupleWidthLog N s p E ≤ tupleWidthLogEnvelope p E := by
    unfold normalizedTupleWidthLog tupleWidthLogEnvelope
    linarith
  have hA := spatialDiscretizationLog_le_envelope _ _ hp hl hq hd
  have hT := anisotropicSpatialMeshLog_le_envelope _ _ hp hl hq hd
  have hprof := spatialProfileLog_le_fixedEnvelope _ _ hp hq (he.trans (by linarith))
  have hK : p ^ 3 + anisotropicSpatialCapLog p +
      2 * spatialProfileLog (Fintype.card (Unit ⊕ Fin q)) (Fintype.card (UnselectedColumn s)) p + l + 1 ≤
        spatialLipschitzCostEnvelope p l := by
    unfold spatialLipschitzCostEnvelope spatialLipschitzEnvelope
    linarith
  have hprod : (Fintype.card (Option (G ⊕ N) × X) : ℝ) ≤ (1 + 2 * p) * p := by
    simp only [Fintype.card_prod, Nat.cast_mul]
    exact mul_le_mul hcoords hX (Nat.cast_nonneg _) (by positivity)
  have hlate : normalizedTupleLateBudget X N s p E l ≤ tupleLateLogEnvelope p E l := by
    unfold normalizedTupleLateBudget tupleLateLogEnvelope
    linarith
  refine ⟨hw, ?_⟩
  unfold normalizedTupleSideLog tupleSideLogEnvelope
  linarith

theorem tupleSideLogEnvelope_mono {p E l P F L : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l) (hP : p ≤ P) (hF : E ≤ F) (hL : l ≤ L) :
    tupleSideLogEnvelope p E l ≤ tupleSideLogEnvelope P F L := by
  have hP0 : 0 ≤ P := hp.trans hP
  dsimp only [tupleEarlyLogEnvelope, tupleWidthLogEnvelope, tupleLateLogEnvelope, tupleSideLogEnvelope,
    spatialTupleToleranceLog, spatialDiscretizationEnvelope, spatialMeshEnvelope,
    spatialLipschitzCostEnvelope, spatialLipschitzEnvelope, spatialDisplacementEnvelope,
    spatialFixedProfileEnvelope, anisotropicSpatialCapLog, coefficientErrorVolumeLog]
  gcongr

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NormalizedTupleLargerBudget
namespace OAI

section

namespace Erdos3

theorem normalizedTuple_log_mono (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G)
    {p E l P F L : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l)
    (hpP : p ≤ P) (hEF : E ≤ F) (hlL : l ≤ L) :
    normalizedTupleWidthLog N s p E ≤ normalizedTupleWidthLog N s P F ∧
      normalizedTupleSideLog X N s p E l ≤ normalizedTupleSideLog X N s P F L := by
  have hP := hp.trans hpP
  have hF := hE.trans hEF
  have hL := hl.trans hlL
  constructor
  · dsimp only [normalizedTupleWidthLog, anisotropicTupleEarlyBudget, spatialTupleToleranceLog,
      spatialDisplacementLog, spatialProfileLog, anisotropicSpatialCapLog, coefficientErrorVolumeLog]
    gcongr
  · dsimp only [normalizedTupleSideLog, normalizedTupleLateBudget, normalizedTupleWidthLog,
      anisotropicTupleEarlyBudget, spatialTupleToleranceLog, spatialDiscretizationLog,
      anisotropicSpatialMeshLog, spatialDisplacementLog, spatialProfileLog,
      anisotropicSpatialCapLog, coefficientErrorVolumeLog]
    gcongr

theorem normalizedTuple_log_envelopes_of_le (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G)
    {p E l P : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l) (hpP : p ≤ P)
    (hq : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ P)
    (hG : (Fintype.card G : ℝ) ≤ P) (hN : (Fintype.card N : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P) :
    normalizedTupleWidthLog N s p E ≤ tupleWidthLogEnvelope P E ∧
      normalizedTupleSideLog X N s p E l ≤ tupleSideLogEnvelope P E l := by
  obtain ⟨hwidth, hside⟩ := normalizedTuple_log_mono X N s hp hE hl hpP le_rfl le_rfl
  obtain ⟨hwidth', hside'⟩ := normalizedTuple_log_envelopes X N s (hp.trans hpP) hE hl hq hG hN hX
  exact ⟨hwidth.trans hwidth', hside.trans hside'⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoarseSpatialPartitionBudget
namespace OAI

section

namespace Erdos3

def coarseSpatialReciprocalLog {A : Type*} [Semiring A] (P : A) : A :=
  2 * (P + spatialTupleToleranceLog P) + 8

def coarseSpatialPartitionLog {A : Type*} [Semiring A] (P : A) : A :=
  let R := P + coarseSpatialReciprocalLog P + 4
  R * ((3 * R + 4) * R + 2 * R)

theorem coarseSpatialLogs_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ coarseSpatialReciprocalLog P ∧ 0 ≤ coarseSpatialPartitionLog P := by
  have ht := spatialTupleToleranceLog_nonneg hP
  have hL : 0 ≤ coarseSpatialReciprocalLog P := by unfold coarseSpatialReciprocalLog; positivity
  exact ⟨hL, by unfold coarseSpatialPartitionLog; positivity⟩

theorem spatialTupleCoarseMesh_inv_bound (d : ℕ) {G V K ε P : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hK : 0 ≤ K) (hε : 0 < ε) (hP : 0 ≤ P)
    (hd : (d : ℝ) ≤ P) (hGP : G ≤ Real.exp P) (hVP : V ≤ Real.exp P)
    (hKP : K ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    (spatialTupleCoarseMesh d G V K ε)⁻¹ ≤ Real.exp (coarseSpatialReciprocalLog P) := by
  have hwidth := spatialTupleEarlyWidth_inv_bound d hG hV hK hε hP hd hGP hVP hKP hεP
  have ht := (spatialTupleTolerance_spec d hG hV hε).1
  have hw := (twoTermErrorWidth_spec hK ht).1
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  unfold spatialTupleCoarseMesh
  rw [inv_div, div_eq_mul_inv]
  calc
    _ ≤ Real.exp 4 * Real.exp (2 * (P + spatialTupleToleranceLog P) + 4) :=
      mul_le_mul hfour hwidth (inv_nonneg.mpr hw.le) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; unfold coarseSpatialReciprocalLog; ring

theorem spatialTupleCoarseMesh_partition_budget (d n : ℕ) {G V K ε μ C P : ℝ}
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hK : 0 ≤ K) (hμ : 0 ≤ μ) (hC : 0 ≤ C)
    (hε : 0 < ε) (hP : 0 ≤ P) (hd : (d : ℝ) ≤ P) (hn : (n : ℝ) ≤ P)
    (hGP : G ≤ Real.exp P) (hVP : V ≤ Real.exp P) (hKP : K ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) (hμP : μ ≤ Real.exp P)
    (hΓP : μ ^ n ≤ Real.exp P) (hCP : C ≤ Real.exp P) :
    let r := spatialTupleCoarseMesh d G V K ε
    r⁻¹ ≤ Real.exp (coarseSpatialReciprocalLog P) ∧
      (μ ^ n * (intervalSiteCount 4 r : ℝ) ^ n * (μ ^ n * C)) ^ d ≤
        Real.exp (coarseSpatialPartitionLog P) := by
  intro r
  have hri := spatialTupleCoarseMesh_inv_bound d hG hV hK hε hP hd hGP hVP hKP hεP
  refine ⟨hri, ?_⟩
  have hr : 0 < r := (spatialTupleCoarseMesh_spec d hG hV hK hε).1
  have hL := (coarseSpatialLogs_nonneg hP).1
  let R := P + coarseSpatialReciprocalLog P + 4
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hPR : P ≤ R := by dsimp [R]; linarith
  have hLR : coarseSpatialReciprocalLog P ≤ R := by dsimp [R]; linarith
  have hfour : (4 : ℝ) ≤ Real.exp R := by
    have hR4 : 4 ≤ R := by dsimp [R]; linarith
    linarith [Real.add_one_le_exp R]
  have hcount := intervalSiteCount_le_exp (by norm_num : (0 : ℝ) ≤ 4) hr hR hfour
    (by simpa only [one_div] using hri.trans (Real.exp_le_exp.mpr hLR))
  have he := Real.exp_le_exp.mpr hPR
  have hbase := siteCoefficientAllowance_le_exp n hμ (Nat.cast_nonneg _) (pow_nonneg hμ _) hC
    (hμP.trans he) hcount (hΓP.trans he) (hCP.trans he)
  have hpower := vectorSiteAllowance_le_exp d (by positivity) hbase
  apply hpower.trans
  apply Real.exp_le_exp.mpr
  change (d : ℝ) * ((3 * R + 4) * n + 2 * R) ≤ R * ((3 * R + 4) * R + 2 * R)
  gcongr
  · exact hd.trans hPR
  · exact hn.trans hPR

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastPreparedScaleBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

noncomputable def preparedSamplerBlockCount (m dim : ℕ) (j : Fin m) : ℕ :=
  let rows := boundedBooleanJetRows (Fin dim) (j.val + 1)
  1 + Fintype.card (BoundedBooleanJet (Fin dim) (j.val + 1)) +
    max (positiveModerateSpectrumBlockCount j.val rows.card ((layerTailDegree m + 2) * rows.card))
      (uniformSpectrumBlockCount j.val rows.card ((j.val + 1) * rows.card))

theorem preparedSamplerBlockCount_positive (m dim : ℕ) (j : Fin m) :
    0 < preparedSamplerBlockCount m dim j := by dsimp only [preparedSamplerBlockCount]; omega

theorem preparedSamplerBlockCount_spectrum (m dim : ℕ) (j : Fin m) :
    let rows := boundedBooleanJetRows (Fin dim) (j.val + 1)
    max (positiveModerateSpectrumBlockCount j.val rows.card ((layerTailDegree m + 2) * rows.card))
      (uniformSpectrumBlockCount j.val rows.card ((j.val + 1) * rows.card)) ≤
        preparedSamplerBlockCount m dim j := by dsimp only [preparedSamplerBlockCount]; omega

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

abbrev PreparedSamplerContinuous (j : Fin m) := Fin (L j).rank

noncomputable def preparedSamplerTransverse (j : Fin m) : ℕ :=
  finrank ℝ (euclideanSubspace (L j).space)ᗮ

theorem preparedSampler_axis_card (j : Fin m) :
    Fintype.card (PreparedSamplerContinuous L j) + preparedSamplerTransverse L j =
      Fintype.card (L j).Coord := by
  simpa only [PreparedSamplerContinuous, Fintype.card_fin, preparedSamplerTransverse] using
    (L j).rank_add_orthogonal_finrank

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

noncomputable def preparedCommonBlockCount (m : ℕ) (j : Fin m) : ℕ :=
  ∑ s : Fin (m + 1), preparedSamplerBlockCount m (s.val + 1) j

theorem preparedCommonBlockCount_ge (m : ℕ) (j : Fin m) (s : Fin (m + 1)) :
    preparedSamplerBlockCount m (s.val + 1) j ≤ preparedCommonBlockCount m j := by
  exact Finset.single_le_sum
    (f := fun r : Fin (m + 1) => preparedSamplerBlockCount m (r.val + 1) j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)

theorem preparedCommonBlockCount_positive (m : ℕ) (j : Fin m) :
    0 < preparedCommonBlockCount m j :=
  (preparedSamplerBlockCount_positive m 1 j).trans_le (preparedCommonBlockCount_ge m j 0)

theorem preparedCommonBlockCount_spectrum (m : ℕ) (j : Fin m) (s : Fin (m + 1)) :
    let rows := boundedBooleanJetRows (Fin (s.val + 1)) (j.val + 1)
    max (positiveModerateSpectrumBlockCount j.val rows.card ((layerTailDegree m + 2) * rows.card))
      (uniformSpectrumBlockCount j.val rows.card ((j.val + 1) * rows.card)) ≤
        preparedCommonBlockCount m j :=
  (preparedSamplerBlockCount_spectrum m (s.val + 1) j).trans (preparedCommonBlockCount_ge m j s)

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

noncomputable def preparedCommonSamplerDimension (m M : ℕ) : ℕ :=
  (m + 1) * (m + 3) + M * m * (∑ j, preparedCommonBlockCount m j) + M + m + 2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

abbrev EnlargedPreparedCommonKernelWithCutoff (m d Jalloc : ℕ) :=
  Fin ((d + 1) * (d + 3) + (m + 1) * Jalloc)

theorem enlargedPreparedCommonKernelWithCutoff_analytic_capacity (m d Jalloc s : ℕ) (hs : s ≤ d) :
    (s + 1) * (s + 3) ≤ Fintype.card (EnlargedPreparedCommonKernelWithCutoff m d Jalloc) := by
  simp only [EnlargedPreparedCommonKernelWithCutoff, Fintype.card_fin]
  exact (Nat.mul_le_mul (by omega) (by omega)).trans (Nat.le_add_right _ _)

def enlargedPreparedCommonCanonicalSelectionWithCutoff (m d Jalloc s : ℕ) (hs : s ≤ d) :
    Fin (s + 1) ↪ EnlargedPreparedCommonKernelWithCutoff m d Jalloc where
  toFun i := ⟨i.val, lt_of_lt_of_le i.isLt (by
    have hcap := enlargedPreparedCommonKernelWithCutoff_analytic_capacity m d Jalloc s hs
    have hsmall : s + 1 ≤ (s + 1) * (s + 3) := by nlinarith
    simpa only [EnlargedPreparedCommonKernelWithCutoff, Fintype.card_fin] using hsmall.trans hcap)⟩
  inj' := by
    intro i j h
    exact Fin.ext (congrArg (fun z : EnlargedPreparedCommonKernelWithCutoff m d Jalloc => z.val) h)

@[simp] theorem enlargedPreparedCommonCanonicalSelectionWithCutoff_val (m d Jalloc s : ℕ)
    (hs : s ≤ d) (i : Fin (s + 1)) :
    (enlargedPreparedCommonCanonicalSelectionWithCutoff m d Jalloc s hs i).val = i.val := rfl

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

abbrev EnlargedPreparedCommonKernel (m Jalloc : ℕ) :=
  Fin ((m + 1) * (m + 3) + (m + 1) * Jalloc)

theorem enlargedPreparedCommonKernel_analytic_capacity (m Jalloc s : ℕ) (hs : s ≤ m) :
    (s + 1) * (s + 3) ≤ Fintype.card (EnlargedPreparedCommonKernel m Jalloc) := by
  simp only [EnlargedPreparedCommonKernel, Fintype.card_fin]
  exact (Nat.mul_le_mul (by omega) (by omega)).trans (Nat.le_add_right _ _)

def enlargedPreparedCommonCanonicalSelection (m Jalloc s : ℕ) (hs : s ≤ m) :
    Fin (s + 1) ↪ EnlargedPreparedCommonKernel m Jalloc where
  toFun i := ⟨i.val, lt_of_lt_of_le i.isLt (by
    have hcap := enlargedPreparedCommonKernel_analytic_capacity m Jalloc s hs
    have hsmall : s + 1 ≤ (s + 1) * (s + 3) := by nlinarith
    simpa only [EnlargedPreparedCommonKernel, Fintype.card_fin] using hsmall.trans hcap)⟩
  inj' := by
    intro i j h
    exact Fin.ext (congrArg (fun z : EnlargedPreparedCommonKernel m Jalloc => z.val) h)

@[simp] theorem enlargedPreparedCommonCanonicalSelection_val (m Jalloc s : ℕ)
    (hs : s ≤ m) (i : Fin (s + 1)) :
    (enlargedPreparedCommonCanonicalSelection m Jalloc s hs i).val = i.val := rfl

noncomputable def enlargedPreparedCommonSamplerDimension (m M Jalloc : ℕ) : ℕ :=
  (m + 1) * (m + 3) + (m + 1) * Jalloc +
    M * m * (∑ j : Fin m, (preparedCommonBlockCount m j + Jalloc)) + M + m + Jalloc + 2

theorem enlargedPreparedCommonSamplerDimension_polynomial (m M Jalloc : ℕ) :
    enlargedPreparedCommonSamplerDimension m M Jalloc =
      preparedCommonSamplerDimension m M + (m + 2 + M * m * m) * Jalloc := by
  simp only [enlargedPreparedCommonSamplerDimension, preparedCommonSamplerDimension,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_id]
  ring

theorem enlargedPreparedCommonSamplerDimension_ge (m M Jalloc : ℕ) :
    M ≤ enlargedPreparedCommonSamplerDimension m M Jalloc := by
  unfold enlargedPreparedCommonSamplerDimension
  omega

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

abbrev EnlargedPreparedCommonSamplerBlock (Jalloc : ℕ)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :=
  Fin (preparedCommonBlockCount m a.1 + Jalloc)

theorem enlargedPreparedCommonSamplerBlock_positive (Jalloc : ℕ)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    0 < Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a) := by
  simpa only [EnlargedPreparedCommonSamplerBlock, Fintype.card_fin] using
    (preparedCommonBlockCount_positive m a.1).trans_le (Nat.le_add_right _ Jalloc)

theorem enlargedPreparedCommonSamplerBlock_spectrum (Jalloc s : ℕ) (hs : s ≤ m)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    let rows := boundedBooleanJetRows (Fin (s + 1)) (a.1.val + 1)
    max (positiveModerateSpectrumBlockCount a.1.val rows.card ((layerTailDegree m + 2) * rows.card))
      (uniformSpectrumBlockCount a.1.val rows.card ((a.1.val + 1) * rows.card)) ≤
        Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a) := by
  simpa only [EnlargedPreparedCommonSamplerBlock, Fintype.card_fin] using
    (preparedCommonBlockCount_spectrum m a.1 ⟨s, Nat.lt_succ_of_le hs⟩).trans
      (Nat.le_add_right _ Jalloc)

theorem enlargedPreparedCommonSamplerBlock_uniform (Jalloc s : ℕ) (hs : s ≤ m)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    let rows := boundedBooleanJetRows (Fin (s + 1)) (a.1.val + 1)
    uniformSpectrumBlockCount a.1.val rows.card ((a.1.val + 1) * rows.card) ≤
      Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a) :=
  (le_max_right _ _).trans (enlargedPreparedCommonSamplerBlock_spectrum L Jalloc s hs a)

theorem enlargedPreparedCommonSampler_variables_card (Jalloc : ℕ) :
    Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc)
      (PreparedSamplerContinuous L) (preparedSamplerTransverse L)
      (EnlargedPreparedCommonSamplerBlock L Jalloc)) =
      (m + 1) * (m + 3) + (m + 1) * Jalloc + ∑ j : Fin m,
        Fintype.card (L j).Coord * ((preparedCommonBlockCount m j + Jalloc) * (j.val + 1)) := by
  rw [samplerTupleIndex_card]
  simp only [EnlargedPreparedCommonKernel, Fintype.card_fin, LayerSamplerAxis, Fintype.sum_sigma,
    EnlargedPreparedCommonSamplerBlock, layerSamplerDegree, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simpa only [PreparedSamplerContinuous, Fintype.card_fin, Nat.cast_id] using
    congrArg (fun d : ℕ => d * ((preparedCommonBlockCount m j + Jalloc) * (j.val + 1)))
      (preparedSampler_axis_card L j)

theorem enlargedPreparedCommonSampler_dimensions (Jalloc : ℕ) {M : ℕ}
    (hM : ∀ j, Fintype.card (L j).Coord ≤ M) :
    Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc)
      (PreparedSamplerContinuous L) (preparedSamplerTransverse L)
      (EnlargedPreparedCommonSamplerBlock L Jalloc)) ≤ enlargedPreparedCommonSamplerDimension m M Jalloc ∧
      (∀ j, Fintype.card (PreparedSamplerContinuous L j) ≤ enlargedPreparedCommonSamplerDimension m M Jalloc) ∧
      (∀ j, preparedSamplerTransverse L j ≤ enlargedPreparedCommonSamplerDimension m M Jalloc) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [enlargedPreparedCommonSampler_variables_card]
    have hsum : (∑ j : Fin m, Fintype.card (L j).Coord *
        ((preparedCommonBlockCount m j + Jalloc) * (j.val + 1))) ≤
        M * m * (∑ j : Fin m, (preparedCommonBlockCount m j + Jalloc)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ M * ((preparedCommonBlockCount m j + Jalloc) * m) :=
          Nat.mul_le_mul (hM j) (Nat.mul_le_mul_left _ (Nat.succ_le_of_lt j.isLt))
        _ = _ := by ring
    unfold enlargedPreparedCommonSamplerDimension
    omega
  · intro j
    have h := preparedSampler_axis_card L j
    have hb := hM j
    have hp := enlargedPreparedCommonSamplerDimension_ge m M Jalloc
    omega
  · intro j
    have h := preparedSampler_axis_card L j
    have hb := hM j
    have hp := enlargedPreparedCommonSamplerDimension_ge m M Jalloc
    omega

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedSpatialKernelBlocks
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def modularRankSmallBallExponent (s : ℕ) : ℝ := (2 : ℝ) ^ (1 - (s : ℝ))

end Erdos3

end

section

namespace Erdos3

def modularInitialRankStrength (s d : ℕ) : ℕ :=
  2 ^ (2 * s) * s.factorial * (d + 2)

def modularInitialBlockCount (s d : ℕ) : ℕ :=
  2 ^ s * (modularInitialRankStrength s d + d + 10) + 1

theorem modularInitialBlockCount_linear_bound (s d : ℕ) :
    modularInitialBlockCount s d ≤
      (2 ^ s * (2 ^ (2 * s) * s.factorial + 1) + 1) * (d + 11) := by
  dsimp only [modularInitialBlockCount, modularInitialRankStrength]
  nlinarith [Nat.zero_le (2 ^ s), Nat.zero_le (2 ^ (2 * s) * s.factorial)]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem modularInitialBlockCount_two_dimensions (m d : ℕ) :
    2 * d ≤ modularInitialBlockCount m d := by
  have ha : 1 ≤ 2 ^ (2 * m) * m.factorial := Nat.succ_le_of_lt (by positivity)
  have hb : 1 ≤ 2 ^ m := Nat.succ_le_of_lt (by positivity)
  have hr : d + 2 ≤ modularInitialRankStrength m d := by
    unfold modularInitialRankStrength
    nlinarith
  unfold modularInitialBlockCount
  nlinarith

namespace VectorPolynomial

def preparedSpatialKernelBlocks (m M nX : ℕ) :
    Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)) where
  toFun z := ⟨(m + 1) * (m + 3) + (finProdFinEquiv z).val, by
    have hz := (finProdFinEquiv z).isLt
    have hdim := modularInitialBlockCount_two_dimensions m (nX + m * M)
    have hmul : modularInitialBlockCount m (nX + m * M) ≤
        (m + 1) * modularInitialBlockCount m (nX + m * M) := by
      exact Nat.le_mul_of_pos_left _ (Nat.succ_pos m)
    omega⟩
  inj' := by
    intro z w h
    apply finProdFinEquiv.injective
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp only at hv
    omega

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedEarlyStructuralPowerBudget
namespace OAI

section

namespace Erdos3

open VectorPolynomial

def preparationCoordinateCap (s D T : ℕ) : ℕ := D * (T + 1) ^ s + D + T + 1

noncomputable def preparationModulusCap (s M R : ℕ) (p : ℝ) : ℕ :=
  R * preparationHeight p s ^ M

noncomputable def preparationOscillationCap (s n R : ℕ) (p : ℝ) : ℕ :=
  (s + 1) * (n + 1) ^ s * R * n * s * preparationHeight p s

noncomputable def preparationShrink (s n M R : ℕ) (p δ : ℝ) : ℝ :=
  4 * preparationModulusCap s M R p /
    min 1 (δ / (preparationOscillationCap s n R p + 1))

theorem preparationCoordinateCap_bounds {I J : Type} {s D t T : ℕ}
    {L : RankPreparationFamily I J s} (h : L.Sized D t) (ht : t ≤ T) (i : Fin s) :
    Fintype.card (L i).Coord ≤ preparationCoordinateCap s D T ∧
      Fintype.card (L i).Column ≤ preparationCoordinateCap s D T ∧
      Fintype.card (L i).Row + 1 ≤ preparationCoordinateCap s D T := by
  obtain ⟨hc, hb, hr⟩ := h.uniform ht i
  dsimp only [preparationCoordinateCap]
  omega

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ModularCoefficientBadPrimeProduct
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def modularCoefficientPrimeThreshold (s : ℕ) : ℕ :=
  max 2 ⌈(s : ℝ) ^ (4 / modularRankSmallBallExponent s)⌉₊

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {T D : Type*} {B : T → Type*}

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {T D I : Type*} [Fintype T] [DecidableEq T]
  [Fintype D] [DecidableEq D] [Fintype I] [DecidableEq I]
  {B : T → Type*} [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {T D I : Type*} [Fintype T] [DecidableEq T]
  [Fintype D] [DecidableEq D] [Fintype I] [DecidableEq I]
  {B : T → Type*} [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedDeterminingCoordinates
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ}

abbrev DeterminingIndex (_L : RankPreparationFamily X J m) (E : Fin m → Type) :=
  Sigma E

abbrev PreparedCoordinate (L : RankPreparationFamily X J m) :=
  (u : Fin m) × (L u).Coord

variable (L : RankPreparationFamily X J m) (E : Fin m → Type)

def determiningWeight (a : L.DeterminingIndex E) : ℕ := a.1.val + 1

variable {E} [∀ u, Fintype (E u)]
variable [∀ u, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L u).Coord) (euclideanSubspace (L u).space))]
variable (bW : ∀ u, Basis (E u) ℤ
  (latticeSection (standardEuclideanLattice (L u).Coord) (euclideanSubspace (L u).space)))
variable (hmem : ∀ u α, coefficients (L u).poly α ∈ (L u).space)

noncomputable def determiningPolynomial (a : L.DeterminingIndex E) : MvPolynomial X ℝ :=
  integralBasisPolynomialCoordinates (L a.1).space
    ((L a.1).integralCoordinateBasis (bW a.1)) (L a.1).poly (hmem a.1) a.2

noncomputable def determiningMatrix
    (r : L.PreparedCoordinate) (a : L.DeterminingIndex E) : ℤ :=
  if h : a.1 = r.1 then (L r.1).integralCoordinateMatrix (bW r.1) r.2 (h ▸ a.2)
  else 0

omit [∀ u, Fintype (E u)] in
theorem determiningPolynomial_degree
    (hdegree : ∀ u, DegreeLE (fun _ => 1) (u.val + 1) (L u).poly)
    (a : L.DeterminingIndex E) :
    (L.determiningPolynomial bW hmem a).totalDegree ≤ L.determiningWeight E a :=
  integralBasisPolynomialCoordinates_totalDegree _ _ _ _ (hdegree a.1) a.2

end Erdos3.RankPreparationFamily

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCenteredDeterminingSlots
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space))]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)))
variable (hmem : ∀ j α, coefficients (L j).poly α ∈ (L j).space)

noncomputable def sortedDeterminingPolynomial
    (i : Fin (Fintype.card (Σ j, E j))) : MvPolynomial X ℝ :=
  L.determiningPolynomial bW hmem (sortedLayerCoordinateEquiv E i)

noncomputable def sortedDeterminingMatrix {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (i : Fin n)
    (a : Fin (Fintype.card (Σ j, E j))) : ℤ :=
  L.determiningMatrix bW (e i) (sortedLayerCoordinateEquiv E a)

theorem sortedDeterminingPolynomial_support
    (hdegree : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (L j).poly)
    (i : Fin (Fintype.card (Σ j, E j))) :
    L.sortedDeterminingPolynomial bW hmem i ∈
      weightedSupportLE (fun _ : X => 1) (sortedLayerCoordinateWeight E i) := by
  apply (mem_weightedSupportLE_iff _ _ _).mpr
  change (L.sortedDeterminingPolynomial bW hmem i).weightedTotalDegree (1 : X → ℕ) ≤ _
  rw [MvPolynomial.weightedTotalDegree_one]
  exact L.determiningPolynomial_degree bW hmem hdegree (sortedLayerCoordinateEquiv E i)

include bW

theorem integral_determining_card : Fintype.card (Σ j, E j) = ∑ j, (L j).rank := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  exact (L j).integralCoordinateBasis_card (bW j)

theorem sortedDeterminingRecovered_rank {s d₀ d D returned : ℕ}
    (hprepared : (∑ j, (L j).rank) ≤ m * D)
    (hD : D ≤ d) (hreturned : returned ≤ d₀ + s * (d - D)) (hm : m ≤ s) :
    Fintype.card (Σ j, E j) + returned ≤ d₀ + s * d := by
  apply recursive_patch_step_rank_bound hD hreturned (j := m) _ hm
  rw [L.integral_determining_card bW]
  exact hprepared

noncomputable def padDeterminingRecovered {s d₀ d D returned : ℕ}
    (hprepared : (∑ j, (L j).rank) ≤ m * D)
    (hs : 1 ≤ s) (hD : D ≤ d) (hreturned : returned ≤ d₀ + s * (d - D)) (hm : m ≤ s)
    (Q : PolynomialPatch X s (Fintype.card (Σ j, E j) + returned)) :
    PolynomialPatch X s (d₀ + s * d) :=
  Q.padRank hs (L.sortedDeterminingRecovered_rank bW hprepared hD hreturned hm)

@[simp] theorem padDeterminingRecovered_value {s d₀ d D returned : ℕ}
    (hprepared : (∑ j, (L j).rank) ≤ m * D)
    (hs : 1 ≤ s) (hD : D ≤ d) (hreturned : returned ≤ d₀ + s * (d - D)) (hm : m ≤ s)
    (Q : PolynomialPatch X s (Fintype.card (Σ j, E j) + returned)) (x : X → ℝ) :
    (L.padDeterminingRecovered bW hprepared hs hD hreturned hm Q).value x = Q.value x :=
  PolynomialPatch.padRank_value _ _ _ _

@[simp] theorem padDeterminingRecovered_lip {s d₀ d D returned : ℕ}
    (hprepared : (∑ j, (L j).rank) ≤ m * D)
    (hs : 1 ≤ s) (hD : D ≤ d) (hreturned : returned ≤ d₀ + s * (d - D)) (hm : m ≤ s)
    (Q : PolynomialPatch X s (Fintype.card (Σ j, E j) + returned)) :
    (L.padDeterminingRecovered bW hprepared hs hD hreturned hm Q).kernel.lip =
      Q.kernel.lip + 4 := PolynomialPatch.padRank_lip _ _ _

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space))]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)))
variable (c : ∀ j, (L j).space)

noncomputable def determiningCenterCoordinate (a : L.DeterminingIndex E) : ℝ :=
  ((L a.1).integralCoordinateBasis (bW a.1)).repr (c a.1) a.2

noncomputable def sortedDeterminingCenter
    (a : Fin (Fintype.card (Σ j, E j))) : ℝ :=
  L.determiningCenterCoordinate bW c (sortedLayerCoordinateEquiv E a)

variable (hmem : ∀ j α, coefficients (L j).poly α ∈ (L j).space)

noncomputable def centeredDeterminingPolynomial
    (a : Fin (Fintype.card (Σ j, E j))) : MvPolynomial X ℝ :=
  L.sortedDeterminingPolynomial bW hmem a - MvPolynomial.C (L.sortedDeterminingCenter bW c a)

theorem centeredDeterminingPolynomial_support
    (hdegree : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (L j).poly)
    (a : Fin (Fintype.card (Σ j, E j))) :
    L.centeredDeterminingPolynomial bW c hmem a ∈
      weightedSupportLE (fun _ : X => 1) (sortedLayerCoordinateWeight E a) :=
  (weightedSupportLE _ _).sub_mem
    (L.sortedDeterminingPolynomial_support bW hmem hdegree a)
    (weightedSupportLE_C _ _ _)

end Erdos3.RankPreparationFamily

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedDeterminingMatrixBudget
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space))]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)))

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3

open Module Submodule VectorPolynomial BohrLattice.MinkowskiSecondBox
open scoped BigOperators

namespace RankPreparationLayer

variable {X J : Type} (L : RankPreparationLayer X J)

theorem rank_le_coord_card : L.rank ≤ Fintype.card L.Coord := by
  have h := L.rank_add_orthogonal_finrank
  omega

attribute [local irreducible] rank

theorem shortIntegralBasisNormBound_le_exp {H R : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hcoord : (Fintype.card L.Coord : ℝ) ≤ p)
    (hcols : (Fintype.card L.Column : ℝ) ≤ p)
    (hrows : (Fintype.card L.Row : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hR : (R : ℝ) ≤ Real.exp p) :
    L.shortIntegralBasisNormBound H R ≤ Real.exp ((p + 2) ^ 124) := by
  have hrank : (L.rank : ℝ) ≤ p :=
    (Nat.cast_le.mpr L.rank_le_coord_card).trans hcoord
  have hgen := jointSpaceGeneratorHeight_le_exp
    (Fintype.card L.Coord) (Fintype.card L.Column) (Fintype.card L.Row) H R
    hp hcoord hcols hrows hH hR
  have hfront : (L.rank : ℝ) * L.rank.factorial * minkowskiSecondConstant L.rank ≤
      Real.exp (4 * (p + 1) ^ 2) := by
    calc
      _ ≤ projectedAxisNormBudget L.rank := by
        unfold projectedAxisNormBudget
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (show (L.rank : ℝ) ≤ L.rank + 1 by linarith) (Nat.cast_nonneg _))
          (minkowskiSecondConstant_nonneg L.rank)
      _ ≤ Real.exp (4 * ((L.rank : ℝ) + 1) ^ 2) := projectedAxisNormBudget_le_exp L.rank
      _ ≤ _ := Real.exp_le_exp.mpr (by gcongr)
  have hcoordexp : (Fintype.card L.Coord : ℝ) ≤ Real.exp p :=
    hcoord.trans (by linarith only [Real.add_one_le_exp p])
  have hpow :
      (jointSpaceGeneratorHeight (Fintype.card L.Coord) (Fintype.card L.Column)
        (Fintype.card L.Row) H R : ℝ) ^ (Fintype.card L.Coord * Fintype.card L.Coord) ≤
      Real.exp (p ^ 2 * (p + 2) ^ 120) := by
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hgen _).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    simp only [Nat.cast_mul]
    calc
      (Fintype.card L.Coord : ℝ) * Fintype.card L.Coord * (p + 2) ^ 120 ≤
          (p * p) * (p + 2) ^ 120 := by gcongr
      _ = _ := by rw [pow_two]
  have hnorm : L.shortIntegralBasisNormBound H R ≤
      Real.exp (4 * (p + 1) ^ 2 + p + p ^ 2 * (p + 2) ^ 120) := by
    unfold shortIntegralBasisNormBound
    calc
      _ ≤ Real.exp (4 * (p + 1) ^ 2) *
          (Real.exp p * Real.exp (p ^ 2 * (p + 2) ^ 120)) := by
        apply mul_le_mul hfront (mul_le_mul hcoordexp hpow (by positivity)
          (Real.exp_nonneg _)) (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [Real.exp_add, Real.exp_add, mul_assoc]
  apply hnorm.trans (Real.exp_le_exp.mpr ?_)
  have hbase : 1 ≤ p + 2 := by linarith
  have hsmall : 4 * (p + 1) ^ 2 + p ≤ 5 * (p + 2) ^ 2 := by nlinarith
  have hcube : (5 : ℝ) ≤ (p + 2) ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
      (by linarith : (2 : ℝ) ≤ p + 2) 3
    norm_num at h
    linarith
  have hsmall' : 4 * (p + 1) ^ 2 + p ≤ (p + 2) ^ 5 := by
    apply hsmall.trans
    calc
      5 * (p + 2) ^ 2 ≤ (p + 2) ^ 3 * (p + 2) ^ 2 := by gcongr
      _ = _ := by rw [← pow_add]
  have hmain : p ^ 2 * (p + 2) ^ 120 ≤ (p + 2) ^ 122 := by
    calc
      _ ≤ (p + 2) ^ 2 * (p + 2) ^ 120 := by gcongr; linarith
      _ = _ := by rw [← pow_add]
  have hsmall122 := hsmall'.trans (pow_le_pow_right₀ hbase (by decide : 5 ≤ 122))
  calc
    _ ≤ (p + 2) ^ 122 + (p + 2) ^ 122 := add_le_add hsmall122 hmain
    _ = 2 * (p + 2) ^ 122 := (two_mul _).symm
    _ ≤ (p + 2) * (p + 2) ^ 122 := by gcongr; linarith
    _ = (p + 2) ^ 123 := (pow_succ' (p + 2) 122).symm
    _ ≤ (p + 2) ^ 124 := pow_le_pow_right₀ hbase (by decide)

theorem exists_bounded_integral_basis {d H R : ℕ} {p : ℝ}
    (hL : L.Valid d H R) (hH : 1 ≤ H) (hR : 1 ≤ R)
    (hp : 0 ≤ p) (hcoord : (Fintype.card L.Coord : ℝ) ≤ p)
    (hcols : (Fintype.card L.Column : ℝ) ≤ p)
    (hrows : (Fintype.card L.Row : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hRp : (R : ℝ) ≤ Real.exp p) :
    ∃ bW : Basis (Fin L.rank) ℤ
      (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space)),
      ∀ a, ‖(bW a).val‖ ≤ Real.exp ((p + 2) ^ 124) := by
  obtain ⟨bW, hbW⟩ := L.exists_short_integral_basis hL hH hR
  exact ⟨bW, fun a => (hbW a).trans
    (L.shortIntegralBasisNormBound_le_exp hp hcoord hcols hrows hHp hRp)⟩

end RankPreparationLayer

def preparedIntegralBasisExponent (m : ℕ) : ℕ :=
  (budgetDepthExponent 38 m + 2) * 124

namespace RankPreparationFamily

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem PreparedHeights.exists_bounded_integral_bases
    {p : ℝ} {R : ℕ} (hL : L.PreparedHeights p R)
    (hp : 0 ≤ p) (hR : 1 ≤ R) (hRp : (R : ℝ) ≤ Real.exp p)
    (hcoord : ∀ j, (Fintype.card (L j).Coord : ℝ) ≤ p)
    (hcols : ∀ j, (Fintype.card (L j).Column : ℝ) ≤ p)
    (hrows : ∀ j, (Fintype.card (L j).Row : ℝ) ≤ p) :
    ∃ bW : ∀ j, Basis (PreparedSamplerContinuous L j) ℤ
      (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)),
      ∀ j a, ‖(bW j a).val‖ ≤ Real.exp ((p + 2) ^ preparedIntegralBasisExponent m) := by
  let q := (p + 2) ^ budgetDepthExponent 38 m
  have hpq : p ≤ q := le_power_budget hp (preparationExponent_pos m)
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hheight (j : Fin m) :
      (preparationHeight p (m - 1 - j.val) : ℝ) ≤ Real.exp q :=
    (Nat.cast_le.mpr (preparationHeight_mono hp (by omega : m - 1 - j.val ≤ m))).trans
      (preparationHeight_le_exp p m)
  have hRpq : (R : ℝ) ≤ Real.exp q := hRp.trans (Real.exp_le_exp.mpr hpq)
  have heach (j : Fin m) := (L j).exists_bounded_integral_basis
    (hL j) (preparationHeight_pos hp _) hR hq
    ((hcoord j).trans hpq) ((hcols j).trans hpq) ((hrows j).trans hpq)
    (hheight j) hRpq
  choose bW hbW using heach
  refine ⟨bW, fun j a => (hbW j a).trans (Real.exp_le_exp.mpr ?_)⟩
  exact shifted_power_budget_le hp (budgetDepthExponent 38 m) 124

theorem PreparedHeights.exists_bounded_integral_bases_of_sized
    {p : ℝ} {R D t T : ℕ} (hL : L.PreparedHeights p R)
    (hp : 0 ≤ p) (hR : 1 ≤ R) (hRp : (R : ℝ) ≤ Real.exp p)
    (hsize : L.Sized D t) (ht : t ≤ T)
    (hcap : (preparationCoordinateCap m D T : ℝ) ≤ p) :
    ∃ bW : ∀ j, Basis (PreparedSamplerContinuous L j) ℤ
      (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)),
      ∀ j a, ‖(bW j a).val‖ ≤ Real.exp ((p + 2) ^ preparedIntegralBasisExponent m) := by
  apply hL.exists_bounded_integral_bases L hp hR hRp
  · intro j
    exact (Nat.cast_le.mpr (preparationCoordinateCap_bounds hsize ht j).1).trans hcap
  · intro j
    exact (Nat.cast_le.mpr (preparationCoordinateCap_bounds hsize ht j).2.1).trans hcap
  · intro j
    have h := (preparationCoordinateCap_bounds hsize ht j).2.2
    exact (Nat.cast_le.mpr (Nat.le_trans (Nat.le_succ _) h)).trans hcap

end RankPreparationFamily
end Erdos3

end

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space))]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)))

end Erdos3.RankPreparationFamily

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedCenteredForecastPathLogEnvelope
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem preparedCenteredForecast_badRadius_bound
    {X : Type*} [Fintype X] (m : ℕ) (stride : X → ℕ)
    {gainLog Qstride : ℝ} (hgainLog : 0 ≤ gainLog)
    (hstride : ∀ x, (stride x : ℝ) ≤ Real.exp Qstride) :
    (((∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) *
      quantitativeBadPrimeRadius (gainLog + 8)) : ℕ) : ℝ) ≤
      Real.exp (2 * Fintype.card X * Qstride +
        (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11) := by
  let correction := smallPrimePowerCorrection (modularCoefficientPrimeThreshold m)
  have hprod : ((∏ x, stride x : ℕ) : ℝ) ≤ Real.exp (Fintype.card X * Qstride) := by
    calc
      _ = ∏ x, (stride x : ℝ) := by simp only [Nat.cast_prod]
      _ ≤ ∏ _x : X, Real.exp Qstride :=
        Finset.prod_le_prod (fun x _ => Nat.cast_nonneg (stride x)) (fun x _ => hstride x)
      _ = Real.exp (Fintype.card X * Qstride) := by
        rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
  have hcorrection : (correction : ℝ) ≤ Real.exp correction := by
    linarith [Real.add_one_le_exp (correction : ℝ)]
  have hradius : (quantitativeBadPrimeRadius (gainLog + 8) : ℝ) ≤ Real.exp (gainLog + 11) := by
    simpa only [show gainLog + 8 + 3 = gainLog + 11 by ring] using
      (quantitativeBadPrimeRadius_bounds (show 0 ≤ gainLog + 8 by linarith)).2.1
  have hproduct := mul_le_mul
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hprod 2)
    (mul_le_mul hcorrection hradius (Nat.cast_nonneg _) (Real.exp_nonneg _))
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (sq_nonneg (Real.exp (Fintype.card X * Qstride)))
  calc
    _ = ((∏ x, stride x : ℕ) : ℝ) ^ 2 *
        ((correction : ℝ) * (quantitativeBadPrimeRadius (gainLog + 8) : ℝ)) := by
      simp only [Nat.cast_mul, Nat.cast_pow, correction]
    _ ≤ (Real.exp (Fintype.card X * Qstride)) ^ 2 *
        (Real.exp correction * Real.exp (gainLog + 11)) := hproduct
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp only [correction]
      ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedCenteredForecastThresholdExponent : ℕ :=
  Classical.choose exists_jointSpatialError_polynomial_budget

theorem preparedCenteredForecast_threshold_inverse {P g : ℝ} {n : ℕ}
    (hP : 0 ≤ P) (hn : 0 < n) (hnP : (n : ℝ) ≤ P) (hg : 0 ≤ g) (hgP : g ≤ P) :
    (spatialMatrixBlockThreshold n (jointSpatialError g))⁻¹ ≤
      Real.exp ((P + preparedCenteredForecastThresholdExponent) ^
        preparedCenteredForecastThresholdExponent) :=
  ((Classical.choose_spec exists_jointSpatialError_polynomial_budget).2 hP hn hnP hg hgP).1

noncomputable def preparedCenteredForecastSpatialLog (P : ℝ) : ℝ :=
  P * (P + 1) + ((P + preparedCenteredForecastThresholdExponent) ^
    preparedCenteredForecastThresholdExponent + 2) + P ^ 2 + P

theorem exists_preparedCenteredForecastSpatialLog_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {P : ℝ}, 0 ≤ P →
      preparedCenteredForecastSpatialLog P ≤ (P + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let A := preparedCenteredForecastThresholdExponent
  let Q : Polynomial ℕ := X * (X + 1) + ((X + Polynomial.C A) ^ A + 2) + X ^ 2 + X
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro P hP
  simpa [Q, X, A, preparedCenteredForecastSpatialLog, Polynomial.eval₂_pow] using hbound P hP

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFinalScalarPowerBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

def preparedFinalScalarBudget (m degree : ℕ) (t : ℝ) : ℝ :=
  2048 * t ^ 3 + (t + 2) ^ (preparedIntegralBasisExponent m + 1) +
    2 * t + 1 + degree * t

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedDilatedDeterminingSlots
namespace OAI

section

namespace Erdos3.RankPreparationFamily
open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space))]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)))
variable (c : ∀ j, (L j).space)
variable (hmem : ∀ j α, coefficients (L j).poly α ∈ (L j).space)

noncomputable def dilatedCenteredDeterminingPolynomial (q : ℕ)
    (a : Fin (Fintype.card (Σ j, E j))) : MvPolynomial X ℝ :=
  (q : ℝ)⁻¹ • L.centeredDeterminingPolynomial bW c hmem a

noncomputable def dilatedSortedDeterminingMatrix (q : ℕ) {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) :
    Fin n → Fin (Fintype.card (Σ j, E j)) → ℤ :=
  dilatedIntegerMatrix q (L.sortedDeterminingMatrix bW e)

theorem dilatedCenteredDeterminingPolynomial_support (q : ℕ)
    (hdegree : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (L j).poly)
    (a : Fin (Fintype.card (Σ j, E j))) :
    L.dilatedCenteredDeterminingPolynomial bW c hmem q a ∈
      weightedSupportLE (fun _ : X => 1) (sortedLayerCoordinateWeight E a) :=
  (weightedSupportLE _ _).smul_mem _
    (L.centeredDeterminingPolynomial_support bW c hmem hdegree a)

@[simp] theorem dilatedCenteredDeterminingPolynomial_eval (q : ℕ)
    (x : X → ℝ) (a : Fin (Fintype.card (Σ j, E j))) :
    MvPolynomial.aeval x (L.dilatedCenteredDeterminingPolynomial bW c hmem q a) =
      MvPolynomial.aeval x (L.centeredDeterminingPolynomial bW c hmem a) / (q : ℝ) := by
  simp [dilatedCenteredDeterminingPolynomial, map_smul, smul_eq_mul, div_eq_mul_inv,
    mul_comm]

noncomputable def dilatedCenteredDeterminingPatch (q : ℕ) {s : ℕ} (hm : m ≤ s)
    (hdegree : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (L j).poly)
    (Φ : PatchKernel (Fintype.card (Σ j, E j))) :
    PolynomialPatch X s (Fintype.card (Σ j, E j)) :=
  PolynomialPatch.ofCoordinates (sortedLayerCoordinateWeight E)
    (sortedLayerCoordinateWeight_pos E)
    (fun i => (sortedLayerCoordinateWeight_le E i).trans hm)
    (sortedLayerCoordinateWeight_mono E)
    (L.dilatedCenteredDeterminingPolynomial bW c hmem q)
    (L.dilatedCenteredDeterminingPolynomial_support bW c hmem q hdegree) Φ

@[simp] theorem dilatedCenteredDeterminingPatch_weight (q : ℕ) {s : ℕ} (hm : m ≤ s)
    (hdegree : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (L j).poly)
    (Φ : PatchKernel (Fintype.card (Σ j, E j))) :
    (L.dilatedCenteredDeterminingPatch bW c hmem q hm hdegree Φ).weight =
      sortedLayerCoordinateWeight E := rfl

@[simp] theorem dilatedCenteredDeterminingPatch_kernel (q : ℕ) {s : ℕ} (hm : m ≤ s)
    (hdegree : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (L j).poly)
    (Φ : PatchKernel (Fintype.card (Σ j, E j))) :
    (L.dilatedCenteredDeterminingPatch bW c hmem q hm hdegree Φ).kernel = Φ := rfl

end Erdos3.RankPreparationFamily

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankPreparedBlocks
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

def enlargedPreparedRankSpatialEmbedding (m Jalloc J : ℕ) (hJ : J ≤ Jalloc) :
    Fin J ↪ EnlargedPreparedCommonKernel m Jalloc :=
  (Fin.castLEEmb (hJ.trans (by nlinarith : Jalloc ≤ (m + 1) * Jalloc))).trans
    (Fin.natAddEmb ((m + 1) * (m + 3)))

def enlargedPreparedRankKernelEmbedding (m Jalloc J : ℕ) (hJ : J ≤ Jalloc) (j : Fin m) :
    Fin J × Fin (j.val + 1) ↪ EnlargedPreparedCommonKernel m Jalloc :=
  (finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb (by
    calc
      J * (j.val + 1) ≤ Jalloc * (m + 1) := Nat.mul_le_mul hJ (by omega)
      _ = (m + 1) * Jalloc := Nat.mul_comm _ _))).trans
    (Fin.natAddEmb ((m + 1) * (m + 3)))

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m)

noncomputable def enlargedPreparedRankPrincipalEmbedding (Jalloc J : ℕ) (hJ : J ≤ Jalloc)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    Fin J ↪ EnlargedPreparedCommonSamplerBlock L Jalloc a :=
  (Fin.castLEEmb hJ).trans (Fin.natAddEmb (preparedCommonBlockCount m a.1))

variable {E : Fin m → Type*}

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedEnlargedModularAllocation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {X₀ J₀ : Type} {m : ℕ} (prep : RankPreparationFamily X₀ J₀ m)

def preparedInitialRankSpatialEmbedding (nX M : ℕ) :
    Fin (modularInitialBlockCount m (nX + m * M)) ↪
      EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)) :=
  enlargedPreparedRankSpatialEmbedding m _ _ le_rfl

def preparedInitialRankKernelEmbedding (nX M : ℕ) (j : Fin m) :
    Fin (modularInitialBlockCount m (nX + m * M)) × Fin (j.val + 1) ↪
      EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)) :=
  enlargedPreparedRankKernelEmbedding m _ _ le_rfl j

noncomputable def preparedInitialRankPrincipalEmbedding (nX M : ℕ)
    (inactive : LayerSamplerAxis (PreparedSamplerContinuous prep)
      (preparedSamplerTransverse prep) → Prop)
    (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j) :
    Fin (modularInitialBlockCount m (nX + m * M)) ↪
      EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))
        ⟨j, a.val⟩ :=
  enlargedPreparedRankPrincipalEmbedding prep _ _ le_rfl ⟨j, a.val⟩

section Dimension

variable {J E : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

include U o bW

end Dimension

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFamilyCanonicalGeometry
namespace OAI

section

namespace Erdos3.RankPreparationFamily
open Module Submodule VectorPolynomial

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem PreparedHeights.exists_canonical_sampler_geometry
    {p : ℝ} {R M : ℕ} (hL : L.PreparedHeights p R)
    (hp : 0 ≤ p) (hR : 1 ≤ R)
    (hM : ∀ j, Fintype.card (L j).Coord ≤ M) :
    ∃ (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ
        (euclideanSubspace (L j).space)ᗮ)
      (_o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ
        (euclideanSubspace (L j).space))
      (_bW : ∀ j, Basis (PreparedSamplerContinuous L j) ℤ
        (latticeSection (standardEuclideanLattice (L j).Coord)
          (euclideanSubspace (L j).space))),
      (∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (L j).space)) ∧
      (∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (L j).space) (b j) z‖ ≤
        Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖) ∧
      (∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (L j).space) (b j)).symm z‖ ≤
        Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖) ∧
      (∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (L j).space) (b j) ∧
        mixedDensityCovolumeRatio (euclideanSubspace (L j).space) (b j) ≤
          Real.exp (allocatedUniformChartLog (M : ℝ))) := by
  let := fun j => hL.lattice_full L hp hR j
  obtain ⟨b, hb, hf, hi, hv⟩ := hL.exists_uniform_charts L hp hR
    (fun j => Nat.cast_le.mpr (hM j))
  let o (j : Fin m) : OrthonormalBasis (PreparedSamplerContinuous L j) ℝ
      (euclideanSubspace (L j).space) :=
    (stdOrthonormalBasis ℝ (euclideanSubspace (L j).space)).reindex
      (finCongr (L j).euclidean_finrank)
  let bW (j : Fin m) : Basis (PreparedSamplerContinuous L j) ℤ
      (latticeSection (standardEuclideanLattice (L j).Coord)
        (euclideanSubspace (L j).space)) :=
    (finiteLatticeBasis (latticeSection (standardEuclideanLattice (L j).Coord)
      (euclideanSubspace (L j).space))).reindex (finCongr (L j).euclidean_finrank)
  exact ⟨b, o, bW, hb, hf, hi, hv⟩

end Erdos3.RankPreparationFamily

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeInitializerScalarInputs
namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {m s D nX : ℕ}

noncomputable abbrev preparedRelativeInitializerVariableCount
    (prep : RankPreparationFamily (Fin nX) (Fin D) m) (s M : ℕ) : ℕ :=
  Fintype.card (LayerSamplerVariables
    (EnlargedPreparedCommonKernel (max m s)
      (modularInitialBlockCount (max m s) (nX + max m s * M)))
    (PreparedSamplerContinuous (prep.pad (max m s)))
    (preparedSamplerTransverse (prep.pad (max m s)))
    (EnlargedPreparedCommonSamplerBlock (prep.pad (max m s))
      (modularInitialBlockCount (max m s) (nX + max m s * M))))

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial

structure PreparedRelativeInitializerScalarInputs
    {X : Type*} {s D E q : ℕ} (oldPatch : PolynomialPatch X s (D + E))
    (coordinates : Fin q → ℕ) (variableCount : ℕ)
    (p pRelative precisionBudget chartLog a Λ : ℝ) (n₀ d₀ : ℕ) : Prop where
  hpInit : 2 ≤ pRelative
  hDlog : (D : ℝ) ≤ Real.exp pRelative
  hqlog : (q : ℝ) ≤ Real.exp pRelative
  hLlog : (oldPatch.kernel.lip : ℝ) ≤ Real.exp pRelative
  hNlog : ∀ j, (coordinates j : ℝ) ≤ Real.exp pRelative
  hClog : ∀ _j : Fin q, Real.exp chartLog ≤ Real.exp pRelative
  hgainlog : Real.exp (-pRelative) ≤ Real.exp (-p)
  hδearly : Real.exp (-precisionBudget) ≤ Real.exp (-(3 * pRelative + 130))
  hpchild : pRelative + 2 ≤ pRelative + 2
  ha : Real.exp (-pRelative) ≤ a
  habsolute : RelativePatchAbsoluteRule s n₀ pRelative a Λ d₀
  hDim : (variableCount : ℝ) ≤ pRelative + 2
  hOldComplexity : relativePatchComplexity oldPatch ≤ pRelative + 2
  hgain1 : Real.exp (-p) ≤ 1
  hδ : 0 ≤ Real.exp (-precisionBudget)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedSlicedForecastComparisonLogs
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedSlicedForecastPrimitiveCap : ℝ :=
  max 1 (scalarCubePrimitiveEnvelope Empty scalarSourceTransitionBound 1 0 1)

noncomputable def preparedSlicedForecastTailCap (cost : ℝ) : ℝ :=
  max preparedSlicedForecastPrimitiveCap (2 * Real.exp cost)

noncomputable def preparedSlicedForecastTailLog (cost : ℝ) : ℝ :=
  preparedSlicedForecastPrimitiveCap + cost + 1

noncomputable def preparedSlicedForecastDensity (cost : ℝ) : ℝ :=
  Real.exp (-cost)

def preparedSlicedForecastKernelLog (cost : ℝ) : ℝ := cost + 1

noncomputable def preparedSlicedForecastChildSize (childLog : ℝ) : ℕ :=
  ⌈Real.exp childLog⌉₊

theorem preparedSlicedForecastPrimitiveCap_one_le :
    1 ≤ preparedSlicedForecastPrimitiveCap := le_max_left _ _

theorem preparedSlicedForecastTailLog_nonneg {cost : ℝ} (hcost : 0 ≤ cost) :
    0 ≤ preparedSlicedForecastTailLog cost := by
  unfold preparedSlicedForecastTailLog
  linarith only [hcost, preparedSlicedForecastPrimitiveCap_one_le]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedSlicedForecastCommonFloorExponent
    (periodLog childLog cost comparisonLog : ℝ) : ℝ :=
  max 0 (max periodLog (max childLog (max (cost + 1) comparisonLog)))

noncomputable def preparedSlicedForecastCommonFloor
    (periodLog childLog cost comparisonLog : ℝ) : ℕ :=
  ⌈Real.exp (preparedSlicedForecastCommonFloorExponent
    periodLog childLog cost comparisonLog)⌉₊

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

noncomputable def preparedSlicedForecastSourceLog (m M Jalloc : ℕ) (Ptest : ℝ) : ℝ :=
  2 + (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ)) ^ 2 +
    preparedSlicedForecastPrimitiveCap + max 0 Ptest

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedEarlyLateSamplerGeometry
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem PreparedHeights.mono_parameter
    {pPrep pLate : ℝ} {R : ℕ} (hL : L.PreparedHeights pPrep R)
    (hpPrep : 0 ≤ pPrep) (hPrepLate : pPrep ≤ pLate) :
    L.PreparedHeights pLate R := by
  intro j
  apply (hL j).mono_height
  unfold preparationHeight
  apply Nat.floor_mono
  apply Real.exp_le_exp.mpr
  exact pow_le_pow_left₀ (by linarith : 0 ≤ pPrep + 2)
    (by linarith : pPrep + 2 ≤ pLate + 2) _

theorem PreparedHeights.basisAxisScale_le_exp
    {p : ℝ} {R : ℕ} (hL : L.PreparedHeights p R)
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ
      (euclideanSubspace (L j).space)ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) =
      projectedIntegerLattice (euclideanSubspace (L j).space))
    (hp : 0 ≤ p) (hRp : (R : ℝ) ≤ Real.exp p)
    (hcoord : ∀ j, (Fintype.card (L j).Coord : ℝ) ≤ p)
    (hcols : ∀ j, (Fintype.card (L j).Column : ℝ) ≤ p)
    (hrows : ∀ j, (Fintype.card (L j).Row : ℝ) ≤ p) :
    ∀ j i, (basisAxisScale (b j) i : ℝ) ≤
      Real.exp ((p + 2) ^ preparedIntegralBasisExponent m) := by
  let q := (p + 2) ^ budgetDepthExponent 38 m
  have hpq : p ≤ q := le_power_budget hp (preparationExponent_pos m)
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hheight (j : Fin m) :
      (preparationHeight p (m - 1 - j.val) : ℝ) ≤ Real.exp q :=
    (Nat.cast_le.mpr (preparationHeight_mono hp (by omega : m - 1 - j.val ≤ m))).trans
      (preparationHeight_le_exp p m)
  have hRpq : (R : ℝ) ≤ Real.exp q := hRp.trans (Real.exp_le_exp.mpr hpq)
  intro j i
  have haxis := (L j).basisAxisScale_le_exp (hL j) (preparationHeight_pos hp _)
    (b j) (hb j) hq ((hcoord j).trans hpq) ((hcols j).trans hpq)
    ((hrows j).trans hpq) (hheight j) hRpq i
  apply haxis.trans (Real.exp_le_exp.mpr ?_)
  calc
    (q + 2) ^ 28 ≤ (q + 2) ^ 124 :=
      pow_le_pow_right₀ (by linarith : 1 ≤ q + 2) (by decide)
    _ ≤ (p + 2) ^ preparedIntegralBasisExponent m :=
      shifted_power_budget_le hp (budgetDepthExponent 38 m) 124

theorem PreparedHeights.exists_early_late_sampler_geometry
    {pPrep pLate : ℝ} {R D t T : ℕ} (hL : L.PreparedHeights pPrep R)
    (hpPrep : 0 ≤ pPrep) (hR : 1 ≤ R) (hPrepLate : pPrep ≤ pLate)
    (hRLate : (R : ℝ) ≤ Real.exp pLate)
    (hsize : L.Sized D t) (ht : t ≤ T)
    (hcapLate : (preparationCoordinateCap m D T : ℝ) ≤ pLate) :
    let M := preparationCoordinateCap m D T
    ∃ (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ
        (euclideanSubspace (L j).space)ᗮ)
      (_o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ
        (euclideanSubspace (L j).space))
      (bW : ∀ j, Basis (PreparedSamplerContinuous L j) ℤ
        (latticeSection (standardEuclideanLattice (L j).Coord)
          (euclideanSubspace (L j).space))),
      (∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (L j).space)) ∧
      (∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (L j).space) (b j) z‖ ≤
        Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖) ∧
      (∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (L j).space) (b j)).symm z‖ ≤
        Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖) ∧
      (∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (L j).space) (b j) ∧
        mixedDensityCovolumeRatio (euclideanSubspace (L j).space) (b j) ≤
          Real.exp (allocatedUniformChartLog (M : ℝ))) ∧
      (∀ j a, ‖(bW j a).val‖ ≤
        Real.exp ((pLate + 2) ^ preparedIntegralBasisExponent m)) ∧
      (∀ j i, (basisAxisScale (b j) i : ℝ) ≤
        Real.exp ((pLate + 2) ^ preparedIntegralBasisExponent m)) := by
  intro M
  have hLate := hL.mono_parameter L hpPrep hPrepLate
  have hpLate : 0 ≤ pLate := hpPrep.trans hPrepLate
  obtain ⟨b, o, _oldIntegralBasis, hb, hf, hi, hv⟩ :=
    hL.exists_canonical_sampler_geometry L hpPrep hR
      (fun j => (preparationCoordinateCap_bounds hsize ht j).1)
  obtain ⟨bW, hbW⟩ := hLate.exists_bounded_integral_bases_of_sized L
    hpLate hR hRLate hsize ht hcapLate
  refine ⟨b, o, bW, hb, hf, hi, hv, hbW, ?_⟩
  apply hLate.basisAxisScale_le_exp L b hb hpLate hRLate
  · intro j
    exact (Nat.cast_le.mpr (preparationCoordinateCap_bounds hsize ht j).1).trans hcapLate
  · intro j
    exact (Nat.cast_le.mpr (preparationCoordinateCap_bounds hsize ht j).2.1).trans hcapLate
  · intro j
    have h := (preparationCoordinateCap_bounds hsize ht j).2.2
    exact (Nat.cast_le.mpr (Nat.le_trans (Nat.le_succ _) h)).trans hcapLate

end Erdos3.RankPreparationFamily

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchPositivePowerInduction
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial
open scoped BigOperators TensorProduct Classical

namespace ResidueBoxSlice

end ResidueBoxSlice

namespace PolynomialPatch.LowestLayerModel

variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {s D E j R : ℕ} {A : PolynomialPatch X s (D + E)}

end PolynomialPatch.LowestLayerModel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

variable {K X : Type*} [Fintype K] [Fintype X] [DecidableEq K] [DecidableEq X]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3
open VectorPolynomial
open scoped BigOperators TensorProduct

namespace PolynomialPatch.LowestLayerModel

end PolynomialPatch.LowestLayerModel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators

variable {K X : Type*} [Fintype K]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators TensorProduct Classical

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial Module
open scoped BigOperators TensorProduct Classical

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial Module
open scoped BigOperators TensorProduct Classical

def PreparedRelativePatchPowerPassage
    (s n₀ stage : ℕ) (discount : ℝ)
    (requiredPower precisionPower preparationPower passagePower : ℕ) : Prop :=
  ∀ (p a Λ : ℝ) (d₀ : ℕ), 2 ≤ p → Real.exp (-p) ≤ a → a ≤ Λ → Λ ≤ 1 →
    RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
    ∀ (nX : ℕ), 0 < nX → (nX : ℝ) ≤ p →
    ∀ (N : Fin nX → ℕ),
      (∀ i, Real.exp ((p + 2) ^ passagePower) ≤ (N i : ℝ)) →
    ∀ (f : (Fin nX → ℤ) → ℝ), (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
      IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
    ∀ (D E m : ℕ), 0 < D → 0 < m → m ≤ s →
    ∀ (oldPatch : PolynomialPatch (Fin nX) s (D + E))
      (F : oldPatch.LowestLayerModel m),
      (∀ i : Fin E, m < oldPatch.weight (i.natAdd D)) →
      relativePatchComplexity oldPatch ≤ p →
      relativePatchDistinctWeights oldPatch ≤ stage + 1 →
      Real.exp (-p) ≤ relativePatchBoxScore N f a oldPatch →
    ∀ (L : RankPreparationFamily (Fin nX) (Fin D) m),
      L.Sized D (m * D) →
      L.PreparedHeights ((p + 2) ^ preparationPower) (preparedRoundedRank p requiredPower) →
      (∑ j, (L j).rank) ≤ m * D →
      (∀ j, Fintype.card (L j).Coord ≤ preparationCoordinateCap m D (m * D)) →
      (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ))
        (preparedRoundedRank p requiredPower) (L j).space (L j).poly) →
    ∀ (ip : Fin D → MvPolynomial (Fin nX) ℤ) (c : Fin D → ℝ)
      (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ)),
      (∀ i, (ip i).totalDegree ≤ m) → DegreeLE (fun _ => 1) m err →
      ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
        L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + err →
      (∀ x ∈ integerBox N, ∀ i,
        |eval (fun k => (x k : ℝ)) err i| ≤ Real.exp (-((p + 2) ^ precisionPower))) →
      RelativePatchSliceConclusion s N f ((1 - discount) ^ (stage + 2) * Λ)
        (d₀ + s * (D + E)) ((p + 2) ^ passagePower)

def RelativePatchFinPositivePowerRule
    (s n₀ stage : ℕ) (discount : ℝ) (power : ℕ) : Prop :=
  ∀ (p a Λ : ℝ) (d₀ : ℕ), 2 ≤ p → Real.exp (-p) ≤ a → a ≤ Λ → Λ ≤ 1 →
    RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
    ∀ (nX : ℕ), 0 < nX → (nX : ℝ) ≤ p →
    ∀ (N : Fin nX → ℕ), (∀ i, Real.exp ((p + 2) ^ power) ≤ (N i : ℝ)) →
    ∀ (f : (Fin nX → ℤ) → ℝ),
      (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
      IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
    ∀ (d : ℕ) (A : PolynomialPatch (Fin nX) s d), 0 < d →
      relativePatchComplexity A ≤ p → relativePatchDistinctWeights A ≤ stage + 1 →
      Real.exp (-p) ≤ relativePatchBoxScore N f a A →
      RelativePatchSliceConclusion s N f ((1 - discount) ^ (stage + 2) * Λ)
        (d₀ + s * d) ((p + 2) ^ power)

end Erdos3

end

section

namespace Erdos3

open scoped Classical

def RelativePatchFinPowerInductionRule (s n₀ stage : ℕ) (discount : ℝ)
    (power : ℕ) : Prop :=
  RelativePatchFinInductionRule s n₀ stage discount
    (fun p => (p + 2) ^ power) (fun p => (p + 2) ^ power)

end Erdos3

end

end OAI

end


