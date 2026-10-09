-- Prove2me | Definitions.Def_OAIErdos3B097
-- name    : OAIErdos3B097
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T18:26:50.809583+00:00
-- url     : https://prove2.me/theorems/0bb8620a-7823-4521-99bb-d9758ec65182
-- title:
--   OpenAI Erdős-3 split, definitions bundle 98 of 106
-- statement:
--   Definitions bundle 98 of 106 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B096`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 98 available.
--
--   Modules: `OAI.Erdos3.BasisFamilyLogHeight`, `OAI.Erdos3.BoxNiltestDetection`, `OAI.Erdos3.CyclicProductNiltestDetection`, `OAI.Erdos3.CyclicShiftTestingDetection`, `OAI.Erdos3.CyclicTranslatedShiftTestingDetection`, `OAI.Erdos3.DegreeRankLieFiltration.realHorizontalPolynomialHom`, `OAI.Erdos3.DegreeRankLieFiltration.realHorizontalSymbolCoefficient_extended`, `OAI.Erdos3.DegreeRankLieFiltration.realHorizontalSymbolHom`, `OAI.Erdos3.DegreeRankLieFiltration.realHorizontalSymbolHom_apply`, `OAI.Erdos3.NilpotentLieBCHGroup.PolynomialDerivativeSystemMod.absorb`, `OAI.Erdos3.NilpotentLieBCHGroup.formal_remove_and_absorb`, `OAI.Erdos3.NilpotentLieBCHGroup.realificationMap_injective`, `OAI.Erdos3.NilpotentLieFiltration.constantGroupOrbit`, `OAI.Erdos3.NilpotentLieFiltration.exists_bounded_polynomial_normalization`, `OAI.Erdos3.NilpotentLieFiltration.formal_current_derivative_advance`, `OAI.Erdos3.NilpotentLieFiltration.formal_degree_two_reabsorption`, `OAI.Erdos3.NilpotentLieFiltration.formal_derivative_horizontal_balance`, `OAI.Erdos3.NilpotentLieFiltration.formal_extra_horizontal_equation`, `OAI.Erdos3.NilpotentLieFiltration.formal_horizontal_logDerivative`, `OAI.Erdos3.NilpotentLieFiltration.formal_lift_nonhorizontal_remainder`, `OAI.Erdos3.NilpotentLieFiltration.formal_logDerivative_sub_pderiv_mem_two`, `OAI.Erdos3.NilpotentLieFiltration.formal_reabsorption_preserves_layer_two`, `OAI.Erdos3.NilpotentLieFiltration.piRealOrbit_projection_log`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbitEval_constantGroupOrbit`, `OAI.Erdos3.NilpotentLieFiltration.realFilteredSymbolGroupMap`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolQuotientEquiv`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolQuotientEquiv_map`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolQuotientHom`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolQuotientHom_bijective`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolQuotientLinear`, `OAI.Erdos3.NilpotentLieFiltration.realPolynomialSymbolQuotientLinear_map`, `OAI.Erdos3.NilpotentLieFiltration.stepOne_coordinates_lipschitz`, `OAI.Erdos3.NilpotentLieFiltration.stepOne_norm_mfderiv_coordinates_le`, `OAI.Erdos3.NilpotentLieFiltration.stepOne_rightTranslate`, `OAI.Erdos3.NilpotentLieFiltration.stepOne_rightVelocity`, `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_frozen_niltest`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.detection_step_zero_sample`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.norm_correlation_step_zero_sample`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.unitComparison`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.unitComparison_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.withLeftTranslatedOrbit`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.withLeftTranslatedOrbit_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.withLeftTranslatedOrbit_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.withLeftTranslatedOrbit_observable`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.withOrbit`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.withOrbit_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.withOrbit_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.RankAlphabet`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_canonical_rank_basis_budget`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_rankLayer_basis_height`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_totalDegree_layer_basis`, `OAI.Erdos3.RationalFilteredNilmanifold.finiteRankGenerators`, `OAI.Erdos3.RationalFilteredNilmanifold.finiteRankGenerators_height`, `OAI.Erdos3.RationalFilteredNilmanifold.finiteRankGenerators_span`, `OAI.Erdos3.RationalFilteredNilmanifold.frozenDiagramKernelInvariance_of_injective`, `OAI.Erdos3.RationalFilteredNilmanifold.observable_frozen_right_eq`, `OAI.Erdos3.RationalFilteredNilmanifold.paddedLayerVector`, `OAI.Erdos3.RationalFilteredNilmanifold.paddedLayerVector_height`, `OAI.Erdos3.RationalFilteredNilmanifold.paddedLayerVector_span`, `OAI.Erdos3.RationalFilteredNilmanifold.productFinBasis_repr_component`, `OAI.Erdos3.RationalFilteredNilmanifold.productRestrictionIndex`, `OAI.Erdos3.RationalFilteredNilmanifold.rankAlphabetVector`, `OAI.Erdos3.RationalFilteredNilmanifold.rankAlphabetVector_mem`, `OAI.Erdos3.RationalFilteredNilmanifold.rankAlphabetWeight`, `OAI.Erdos3.RationalFilteredNilmanifold.rankAlphabetWeight_pos`, `OAI.Erdos3.RationalFilteredNilmanifold.rankAlphabet_span_layer`, `OAI.Erdos3.RationalFilteredNilmanifold.rankAlphabet_spans_layer`, `OAI.Erdos3.RationalFilteredNilmanifold.rationalModelCoordinates`, `OAI.Erdos3.RationalFilteredNilmanifold.rationalModelCoordinates_height`, `OAI.Erdos3.RationalFilteredNilmanifold.realLattice_functional_integral`, `OAI.Erdos3.RationalFilteredNilmanifold.refilteredReconstructionMap`, `OAI.Erdos3.RationalFilteredNilmanifold.sumFactors`, `OAI.Erdos3.RationalFilteredNilmanifold.sumOrbits`, `OAI.Erdos3.RationalFilteredNilmanifold.totalDegreeMultidegree`, `OAI.Erdos3.RationalFilteredNilmanifold.totalDegreeMultidegree_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.vertical_left_translate`, `OAI.Erdos3.RationalModelCoordinateIndex`, `OAI.Erdos3.VectorPolynomial.directionalDerivative_coordinate`, `OAI.Erdos3.VectorPolynomial.directionalDerivative_integral_coordinate`, `OAI.Erdos3.VectorPolynomial.directionalDerivative_scaled_coordinate_bound`, `OAI.Erdos3.VectorPolynomial.homogeneous_one_pderiv`, `OAI.Erdos3.basisFrequency_logHeight_le`, `OAI.Erdos3.boxNiltestDetection_zero`, `OAI.Erdos3.comparisonBasisBudget`, `OAI.Erdos3.comparisonBasisHeight`, `OAI.Erdos3.comparisonBasisHeight_ge_ceil`, `OAI.Erdos3.comparisonBasisHeight_ge_factorial`, `OAI.Erdos3.comparisonBasisHeight_le_exp`, `OAI.Erdos3.comparisonBasisHeight_pos`, `OAI.Erdos3.exists_controlled_integral_grid`, `OAI.Erdos3.exists_controlled_subspace_correction_polynomials`, `OAI.Erdos3.exists_native_polynomial_normalization`, `OAI.Erdos3.exists_native_slow_left_constant_bound`, `OAI.Erdos3.layerOne_basis_transport_height_le_exp`, `OAI.Erdos3.multidegreeFactorial_le_total`, `OAI.Erdos3.multidegreeFactorial_mono`, `OAI.Erdos3.norm_sub_positive_sum_le_weighted`, `OAI.Erdos3.normalizedUniformCubeSource`, `OAI.Erdos3.paddedResidueDensityCap_scale`, `OAI.Erdos3.principalIntervalLength`, `OAI.Erdos3.principalIntervalLength_bounds`, `OAI.Erdos3.principalIntervalLength_pos`, `OAI.Erdos3.principalIntervalLength_support`, `OAI.Erdos3.principalIntervalWeight`, `OAI.Erdos3.principalIntervalWeight_grid`, `OAI.Erdos3.principalIntervalWeight_lipschitz`, `OAI.Erdos3.principalIntervalWeight_range`, `OAI.Erdos3.principalNormalizedSource`, `OAI.Erdos3.principalSupportedAxisSources`, `OAI.Erdos3.principalSupportedAxisTuplePMF`, `OAI.Erdos3.principalSupportedCoordinateWeights`, `OAI.Erdos3.rationalLogHeight_nat_mul`, `OAI.Erdos3.rationalTagProjectionComplement`, `OAI.Erdos3.rationalTagProjectionComplement_apply`, `OAI.Erdos3.rationalTagProjectionComplement_coordinate_bound`, `OAI.Erdos3.rationalTagProjectionComplement_coordinate_exp_bound`, `OAI.Erdos3.rationalTagProjectionComplement_denominator_grid`, `OAI.Erdos3.rationalTagProjectionComplement_idempotent`, `OAI.Erdos3.rationalTagProjectionComplement_integer_grid`, `OAI.Erdos3.rationalTagProjectionComplement_ker`, `OAI.Erdos3.realificationLieHom_injective`, `OAI.Erdos3.realifyFunctionalLie`, `OAI.Erdos3.realifyFunctional_lieBCH`, `OAI.Erdos3.realifyFunctional_lie_eq_zero`, `OAI.Erdos3.realifyFunctional_nsmul`, `OAI.Erdos3.scalarCubePrimitiveEnvelope`, `OAI.Erdos3.scalarCubePrimitiveEnvelope_le_scaled`, `OAI.Erdos3.scalarCubePrimitiveEnvelope_nonneg`, `OAI.Erdos3.scalarCubePrimitiveEnvelope_split`, `OAI.Erdos3.scalarSourceTransitionBound`, `OAI.Erdos3.scalarSourceTransitionBound_spec`, `OAI.Erdos3.shiftDetectionLoss`, `OAI.Erdos3.shiftDetectionPolynomial`, `OAI.Erdos3.sumLieAlgebra`, `OAI.Erdos3.sumLieRing`, `OAI.Erdos3.sumLieSpace`, `OAI.Erdos3.sumRealificationContinuousSMul`, `OAI.Erdos3.sumRealificationT2Space`, `OAI.Erdos3.sumRealificationTopologicalAddGroup`, `OAI.Erdos3.sumRealificationTopology`, `OAI.Erdos3.weighted_partition_mean_error`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B098

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDerivativeBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

theorem directionalDerivative_coordinate (f : L →ₗ[ℚ] ℝ) (h : σ → ℚ)
    (p : VectorPolynomial σ ℚ L) (α : σ →₀ ℕ) :
    f (coefficients (directionalDerivative h p) α) =
      ∑ i, (h i : ℝ) * (α i + 1 : ℝ) * f (coefficients p (α + Finsupp.single i 1)) := by
  rw [coefficients_directionalDerivative, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Rat.smul_def, mul_assoc]

theorem directionalDerivative_scaled_coordinate_bound
    (f : L →ₗ[ℚ] ℝ) (p : VectorPolynomial σ ℚ L)
    (d : ℕ) (hdegree : ∀ (β : σ →₀ ℕ) (i : σ), d < β i → f (coefficients p β) = 0)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M : ℝ) (hM : 0 ≤ M)
    (hp : ∀ β, |f (coefficients p β)| ≤ M / monomialScale T β)
    (h : σ → ℚ) (hh : ∀ i, |(h i : ℝ)| ≤ T i) (α : σ →₀ ℕ) :
    |f (coefficients (directionalDerivative h p) α)| ≤
      (Fintype.card σ : ℝ) * d * M / monomialScale T α := by
  classical
  rw [directionalDerivative_coordinate]
  have hscale := monomialScale_pos T hT α
  have hterm (i : σ) :
      |(h i : ℝ) * (α i + 1 : ℝ) * f (coefficients p (α + Finsupp.single i 1))| ≤
        d * M / monomialScale T α := by
    by_cases hd : d < α i + 1
    · rw [hdegree _ i (by simpa using hd), mul_zero, abs_zero]
      positivity
    · have hdi : α i + 1 ≤ d := Nat.le_of_not_gt hd
      have hdir : (α i + 1 : ℝ) ≤ d := by exact_mod_cast hdi
      have hiScale : monomialScale T (α + Finsupp.single i 1) = monomialScale T α * T i := by
        rw [monomialScale_add]
        congr 1
        simp [monomialScale]
      have hcoef := hp (α + Finsupp.single i 1)
      rw [hiScale] at hcoef
      calc
        _ = |(h i : ℝ)| * (α i + 1 : ℝ) * |f (coefficients p (α + Finsupp.single i 1))| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ α i + 1)]
        _ ≤ (T i * d) * (M / (monomialScale T α * T i)) :=
          mul_le_mul (mul_le_mul (hh i) hdir (by positivity) (hT i).le) hcoef
            (abs_nonneg _) (mul_nonneg (hT i).le (Nat.cast_nonneg d))
        _ = d * M / monomialScale T α := by
          field_simp [ne_of_gt hscale, ne_of_gt (hT i)]
  calc
    _ ≤ ∑ i, |(h i : ℝ) * (α i + 1 : ℝ) * f (coefficients p (α + Finsupp.single i 1))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : σ, (d : ℝ) * M / monomialScale T α := Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by simp [mul_assoc, mul_div_assoc]

theorem directionalDerivative_integral_coordinate
    (f : L →ₗ[ℚ] ℝ) (p : VectorPolynomial σ ℚ L) (l : ℕ)
    (hp : ∀ β, ∃ z : ℤ, (z : ℝ) = (l : ℝ) * f (coefficients p β))
    (h : σ → ℤ) (α : σ →₀ ℕ) :
    ∃ z : ℤ, (z : ℝ) = (l : ℝ) *
      f (coefficients (directionalDerivative (fun i => (h i : ℚ)) p) α) := by
  classical
  let z : σ → ℤ := fun i => Classical.choose (hp (α + Finsupp.single i 1))
  have hz (i : σ) : (z i : ℝ) = (l : ℝ) * f (coefficients p (α + Finsupp.single i 1)) :=
    Classical.choose_spec (hp (α + Finsupp.single i 1))
  refine ⟨∑ i, h i * (α i + 1 : ℤ) * z i, ?_⟩
  rw [directionalDerivative_coordinate, Finset.mul_sum]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_one, Rat.cast_intCast]
  apply Finset.sum_congr rfl
  intro i _
  rw [hz]
  ring

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ComparisonBasisBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [Fintype σ]

theorem multidegreeFactorial_mono {a b : σ → ℕ} (h : a ≤ b) :
    multidegreeFactorial a ≤ multidegreeFactorial b :=
  Finset.prod_le_prod' (fun i _ => Nat.factorial_le (h i))

theorem multidegreeFactorial_le_total (a : σ → ℕ) :
    multidegreeFactorial a ≤ (∑ i, a i).factorial :=
  Nat.le_of_dvd (Nat.factorial_pos _) (Nat.prod_factorial_dvd_factorial_sum Finset.univ a)

noncomputable def comparisonBasisHeight (bound : σ → ℕ) (p : ℝ) : ℕ :=
  ⌈Real.exp p⌉₊ * multidegreeFactorial bound

def comparisonBasisBudget (t : ℕ) (p : ℝ) : ℝ := p + 1 + (t : ℝ) ^ 2

theorem comparisonBasisHeight_ge_ceil (bound : σ → ℕ) (p : ℝ) :
    ⌈Real.exp p⌉₊ ≤ comparisonBasisHeight bound p :=
  Nat.le_mul_of_pos_right _ (multidegreeFactorial_pos bound)

theorem comparisonBasisHeight_ge_factorial (bound : σ → ℕ) (p : ℝ) :
    multidegreeFactorial bound ≤ comparisonBasisHeight bound p :=
  Nat.le_mul_of_pos_left _ (one_le_ceil_exp p)

theorem comparisonBasisHeight_pos (bound : σ → ℕ) (p : ℝ) :
    0 < comparisonBasisHeight bound p :=
  (multidegreeFactorial_pos bound).trans_le (comparisonBasisHeight_ge_factorial bound p)

theorem comparisonBasisHeight_le_exp (bound : σ → ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (comparisonBasisHeight bound p : ℝ) ≤ Real.exp (comparisonBasisBudget (∑ i, bound i) p) := by
  have hf : (multidegreeFactorial bound : ℝ) ≤ Real.exp (((∑ i, bound i : ℕ) : ℝ) ^ 2) := by
    exact (Nat.cast_le.mpr (multidegreeFactorial_le_total bound)).trans (factorial_le_exp_sq _)
  rw [comparisonBasisHeight, Nat.cast_mul]
  calc
    _ ≤ Real.exp (p + 1) * Real.exp (((∑ i, bound i : ℕ) : ℝ) ^ 2) :=
      mul_le_mul (ceil_exp_le_exp_add_one hp) hf (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.StepOneCoordinateMetric
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module Manifold NilpotentLieBCHGroup
open scoped Manifold ContDiff Bundle NNReal ENNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  (F : NilpotentLieFiltration L 1) (e : Basis ι ℝ L)

omit [IsScalarTower ℚ ℝ L] in
theorem stepOne_rightTranslate (g : F.Group) (x : ι → ℝ) :
    rightTranslate e g x = x + e.equivFun g.coord := by
  simp only [rightTranslate, basisHomeomorph_apply, F.stepOne_coord_mul, map_add]
  rw [← basisHomeomorph_apply, Homeomorph.apply_symm_apply]

omit [IsScalarTower ℚ ℝ L] in
theorem stepOne_rightVelocity (g : F.Group) :
    rightVelocity e g = ContinuousLinearMap.id ℝ (ι → ℝ) := by
  unfold rightVelocity
  have heq : rightTranslate e g⁻¹ = fun x => x + e.equivFun (g⁻¹).coord :=
    funext (F.stepOne_rightTranslate e g⁻¹)
  rw [heq]
  simp

theorem stepOne_norm_mfderiv_coordinates_le (g : F.Group) :
    letI := basisChartedSpace (hnil := F.lowerCentralSeries_eq_bot) e
    letI := rightRiemannianBundle (hnil := F.lowerCentralSeries_eq_bot) e
    ∀ v : TangentSpace 𝓘(ℝ, ι → ℝ) g,
      ‖tangentModelVector (mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (basisHomeomorph e) g v)‖ ≤ ‖v‖ := by
  let := basisChartedSpace (hnil := F.lowerCentralSeries_eq_bot) e
  let := rightRiemannianBundle (hnil := F.lowerCentralSeries_eq_bot) e
  intro v
  calc
    _ = ‖tangentModelVector v‖ := congrArg (fun w => ‖tangentModelVector w‖)
      (mfderiv_basisHomeomorph_coordinates e g v)
    _ ≤ coordinateL2Norm v := norm_le_coordinateL2Norm _
    _ = ‖v‖ := by
      rw [norm_tangent_eq_coordinateL2Norm, F.stepOne_rightVelocity]
      rfl

theorem stepOne_coordinates_lipschitz :
    letI := rightMetricSpace (hnil := F.lowerCentralSeries_eq_bot) e
    LipschitzWith 1 (basisHomeomorph (hnil := F.lowerCentralSeries_eq_bot) e) := by
  let := basisChartedSpace (hnil := F.lowerCentralSeries_eq_bot) e
  let := rightRiemannianBundle (hnil := F.lowerCentralSeries_eq_bot) e
  let := rightMetricSpace (hnil := F.lowerCentralSeries_eq_bot) e
  intro x y
  let r : ℝ≥0 := ⟨dist x y + 1, by positivity⟩
  have hnear : (1 : ℝ≥0∞) * riemannianEDist 𝓘(ℝ, ι → ℝ) x y < r := by
    change (1 : ℝ≥0∞) * edist x y < r
    rw [one_mul, edist_dist]
    rw [← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal (dist x y) < ENNReal.ofReal (dist x y + 1)
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  have hbound : ∀ z : F.Group, basisHomeomorph e z ∈ Metric.closedBall (basisHomeomorph e x) r →
      ∀ v : TangentSpace 𝓘(ℝ, ι → ℝ) z,
        ‖tangentModelVector (mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (basisHomeomorph e) z v)‖ₑ ≤
          (1 : ℝ≥0∞) * ‖v‖ₑ := by
    intro z _ v
    simpa only [one_mul, ofReal_norm] using
      ENNReal.ofReal_le_ofReal (F.stepOne_norm_mfderiv_coordinates_le e z v)
  exact coordinate_edist_le_of_riemannianEDist_lt (C := 1) (r := r) (by norm_num)
    (contMDiff_basisHomeomorph e 1) x y hbound hnear

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RationalLatticeFunctional
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem realLattice_functional_integral (η : L →ₗ[ℚ] ℚ)
    (hη : ∀ g : D.filtration.Group, g ∈ D.lattice → ∃ n : ℤ, η g.coord = n)
    (z : D.RealGroup) (hz : z ∈ D.realLattice) :
    ∃ n : ℤ, realifyFunctional η z.coord = n := by
  obtain ⟨g, hg, rfl⟩ := hz
  obtain ⟨n, hn⟩ := hη g hg
  refine ⟨n, ?_⟩
  change realifyFunctional η ((1 : ℝ) ⊗ₜ[ℚ] g.coord) = _
  rw [realifyFunctional_tmul, one_mul, hn, Rat.cast_intCast]

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalScalarSourceEnvelope
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def principalIntervalLength (K T γ : ℝ) : ℕ :=
  Nat.ceil (2 * γ * (K / T))

noncomputable def principalIntervalWeight (K T γ : ℝ) (x : Option Empty → ℝ) : ℝ :=
  (principalIntervalLength K T γ : ℝ) / (K / T) *
    normalizedIntegerInterpolation (K / T) (3 * γ / 2) (γ / 2)
      ((principalIntervalLength K T γ : ℝ) / (K / T) * x none)

variable {K T γ : ℝ} (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
variable (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))

include hK hT hγ in
theorem principalIntervalLength_pos : 0 < principalIntervalLength K T γ := by
  apply Nat.ceil_pos.mpr
  positivity

include hK hT hγ hlarge in
theorem principalIntervalLength_bounds :
    2 * γ * (K / T) ≤ (principalIntervalLength K T γ : ℝ) ∧
      (principalIntervalLength K T γ : ℝ) ≤ 4 * γ * (K / T) := by
  have hP : (1 : ℝ) ≤ probabilityProfileLipschitz := probabilityProfileLipschitz_one_le
  have hwidth : 16 ≤ γ * (K / T) := by nlinarith
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 2 * γ * (K / T) by positivity)
  constructor
  · exact Nat.le_ceil _
  · change (Nat.ceil (2 * γ * (K / T)) : ℝ) ≤ _
    nlinarith

theorem principalIntervalLength_support {k : ℤ}
    (hk : k ∈ (principalIntegerPMF K T γ hK hT hγ hlarge).support) :
    k ∈ Finset.Ico 0 (principalIntervalLength K T γ : ℤ) := by
  have hb := principalIntegerPMF_support hK hT hγ hlarge hk
  have he : T * (k : ℝ) / K = (k : ℝ) / (K / T) := by field_simp
  rw [he] at hb
  have hlo := (lt_div_iff₀ (div_pos hK hT)).mp hb.1
  have hhi := (div_lt_iff₀ (div_pos hK hT)).mp hb.2
  have hk0 : (0 : ℝ) ≤ k := (mul_pos hγ (div_pos hK hT)).le.trans hlo.le
  have hkL : (k : ℝ) < principalIntervalLength K T γ :=
    hhi.trans_le (Nat.le_ceil _)
  exact Finset.mem_Ico.mpr ⟨by exact_mod_cast hk0, by exact_mod_cast hkL⟩

theorem principalIntervalWeight_grid (k : ℤ) :
    principalIntervalWeight K T γ (fun _ => (k : ℝ) / principalIntervalLength K T γ) =
      (principalIntervalLength K T γ : ℝ) *
        (principalIntegerPMF K T γ hK hT hγ hlarge k).toReal := by
  have hL : (principalIntervalLength K T γ : ℝ) ≠ 0 :=
    by exact_mod_cast (Nat.ne_of_gt (principalIntervalLength_pos hK hT hγ))
  have hQ := (div_pos hK hT).ne'
  unfold principalIntervalWeight
  rw [show (principalIntervalLength K T γ : ℝ) / (K / T) *
      ((k : ℝ) / principalIntervalLength K T γ) = (k : ℝ) / (K / T) by field_simp]
  rw [normalizedIntegerInterpolation_grid (K / T) (3 * γ / 2) (γ / 2)
    (div_pos hK hT) (by positivity) hlarge k]
  change _ = (principalIntervalLength K T γ : ℝ) *
    (normalizedIntegerPMF (K / T) (3 * γ / 2) (γ / 2) _ _ _ k).toReal
  field_simp

include hK hT hγ hlarge in
theorem principalIntervalWeight_range (x : Option Empty → ℝ) :
    0 ≤ principalIntervalWeight K T γ x ∧ principalIntervalWeight K T γ x ≤ 16 := by
  have hL := principalIntervalLength_pos hK hT hγ
  have ha0 : 0 ≤ (principalIntervalLength K T γ : ℝ) / (K / T) := by positivity
  have ha : (principalIntervalLength K T γ : ℝ) / (K / T) ≤ 4 * γ :=
    (div_le_iff₀ (div_pos hK hT)).mpr (principalIntervalLength_bounds hK hT hγ hlarge).2
  have hb := normalizedIntegerInterpolation_range (K / T) (3 * γ / 2) (γ / 2)
    (div_pos hK hT) (by positivity) hlarge
      ((principalIntervalLength K T γ : ℝ) / (K / T) * x none)
  constructor
  · exact mul_nonneg ha0 hb.1
  · calc
      principalIntervalWeight K T γ x ≤
          ((principalIntervalLength K T γ : ℝ) / (K / T)) * (2 / (γ / 2)) :=
        mul_le_mul_of_nonneg_left hb.2 ha0
      _ ≤ (4 * γ) * (2 / (γ / 2)) :=
        mul_le_mul_of_nonneg_right ha (by positivity)
      _ = 16 := by field_simp; ring

include hK hT hγ hlarge in
theorem principalIntervalWeight_lipschitz :
    LipschitzWith (128 * probabilityProfileLipschitz) (principalIntervalWeight K T γ) := by
  let a : ℝ := (principalIntervalLength K T γ : ℝ) / (K / T)
  have hL := principalIntervalLength_pos hK hT hγ
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha : a ≤ 4 * γ :=
    (div_le_iff₀ (div_pos hK hT)).mpr (principalIntervalLength_bounds hK hT hγ hlarge).2
  have hcoef : a ^ 2 * (2 * (probabilityProfileLipschitz : ℝ) / (γ / 2) ^ 2) ≤
      128 * (probabilityProfileLipschitz : ℝ) := by
    calc
      _ ≤ (4 * γ) ^ 2 * (2 * (probabilityProfileLipschitz : ℝ) / (γ / 2) ^ 2) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha0 ha 2) (by positivity)
      _ = _ := by field_simp; ring
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hxy : |x none - y none| ≤ dist x y := by
    simpa only [Real.dist_eq] using dist_le_pi_dist x y none
  have hb := normalizedIntegerInterpolation_lipschitz_bound (K / T) (3 * γ / 2) (γ / 2)
    (div_pos hK hT) (by positivity) hlarge (a * x none) (a * y none)
  rw [Real.dist_eq]
  change |a * normalizedIntegerInterpolation (K / T) (3 * γ / 2) (γ / 2) (a * x none) -
    a * normalizedIntegerInterpolation (K / T) (3 * γ / 2) (γ / 2) (a * y none)| ≤
      (128 * (probabilityProfileLipschitz : ℝ)) * dist x y
  rw [← mul_sub, abs_mul, abs_of_nonneg ha0]
  calc
    _ ≤ a * ((2 * (probabilityProfileLipschitz : ℝ) / (γ / 2) ^ 2) *
        |a * x none - a * y none|) := mul_le_mul_of_nonneg_left hb ha0
    _ = (a ^ 2 * (2 * (probabilityProfileLipschitz : ℝ) / (γ / 2) ^ 2)) *
        |x none - y none| := by rw [← mul_sub, abs_mul, abs_of_nonneg ha0]; ring
    _ ≤ (128 * (probabilityProfileLipschitz : ℝ)) * dist x y :=
      mul_le_mul hcoef hxy (abs_nonneg _) (by positivity)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def scalarCubePrimitiveEnvelope (I : Type*) [Fintype I]
    (A B T : ℝ≥0) (M : ℕ) : ℝ :=
  let q := (Fintype.card I : ℝ) + 1
  let V := (2 * q) ^ (Fintype.card I + 1)
  1 + q + M + B + T + 4 * V * ((2 : ℝ) ^ Fintype.card I) ^ 2 +
    2 * scalarCubeGridBoundaryConstant I * V + scalarCubeCutoffDerivativeNumerator I A +
      paddedResidueDensityCap I M

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem scalarCubePrimitiveEnvelope_nonneg (I : Type*) [Fintype I]
    (A B T : ℝ≥0) (M : ℕ) : 0 ≤ scalarCubePrimitiveEnvelope I A B T M := by
  unfold scalarCubePrimitiveEnvelope scalarCubeGridBoundaryConstant
    scalarCubeCutoffDerivativeNumerator paddedResidueDensityCap scalarCubeResidueDensityCap
  positivity

theorem paddedResidueDensityCap_scale (I : Type*) [Fintype I] (M : ℕ) :
    paddedResidueDensityCap I M =
      paddedResidueDensityCap I 1 * (M : ℝ) ^ (Fintype.card I + 1) := by
  simp only [paddedResidueDensityCap, scalarCubeResidueDensityCap, Nat.cast_one, mul_one, mul_pow]
  ring

theorem scalarCubePrimitiveEnvelope_split (I : Type*) [Fintype I]
    (A B T : ℝ≥0) (M : ℕ) :
    scalarCubePrimitiveEnvelope I A B T M =
      scalarCubePrimitiveEnvelope I A B T 0 + M + paddedResidueDensityCap I M := by
  simp only [scalarCubePrimitiveEnvelope, paddedResidueDensityCap, scalarCubeResidueDensityCap,
    Nat.cast_zero, mul_zero, zero_pow (Nat.succ_ne_zero _), add_zero]
  ring

theorem scalarCubePrimitiveEnvelope_le_scaled (I : Type*) [Fintype I]
    (A B T : ℝ≥0) {M : ℕ} (hM : 1 ≤ M) :
    scalarCubePrimitiveEnvelope I A B T M ≤
      scalarCubePrimitiveEnvelope I A B T 1 * (M : ℝ) ^ (Fintype.card I + 1) := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hpow : (1 : ℝ) ≤ (M : ℝ) ^ (Fintype.card I + 1) := one_le_pow₀ hM'
  have hMp : (M : ℝ) ≤ (M : ℝ) ^ (Fintype.card I + 1) := by
    calc
      _ = 1 * (M : ℝ) := (one_mul _).symm
      _ ≤ (M : ℝ) ^ Fintype.card I * M :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ hM') (Nat.cast_nonneg _)
      _ = _ := (pow_succ _ _).symm
  have hzero := scalarCubePrimitiveEnvelope_nonneg I A B T 0
  have hc : scalarCubePrimitiveEnvelope I A B T 0 ≤
      scalarCubePrimitiveEnvelope I A B T 0 * (M : ℝ) ^ (Fintype.card I + 1) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hzero
  calc
    _ = scalarCubePrimitiveEnvelope I A B T 0 + M +
        paddedResidueDensityCap I 1 * (M : ℝ) ^ (Fintype.card I + 1) := by
      rw [scalarCubePrimitiveEnvelope_split I A B T M, paddedResidueDensityCap_scale]
    _ ≤ scalarCubePrimitiveEnvelope I A B T 0 * (M : ℝ) ^ (Fintype.card I + 1) +
        (M : ℝ) ^ (Fintype.card I + 1) +
        paddedResidueDensityCap I 1 * (M : ℝ) ^ (Fintype.card I + 1) := by
      gcongr
    _ = _ := by rw [scalarCubePrimitiveEnvelope_split I A B T 1]; push_cast; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def normalizedUniformCubeSource (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1) * M ≤ L) :
    NormalizedScalarCubeSource I where
  length := L
  modulusBound := M
  length_pos := hL
  modulus := m
  residue := r
  modulus_pos := hm
  modulus_le := hmM
  size := hsize
  weight := fun _ => 1
  weightBound := 1
  weightLipschitz := 0
  weightBound_pos := by norm_num
  weight_range := fun _ => by norm_num
  weight_lipschitz := LipschitzWith.const 1
  normalized := (scalarCubeResidueWeights I L M hL m r hm hmM hsize).mean_const 1

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def principalNormalizedSource {K T γ : ℝ}
    (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T)) :
    NormalizedScalarCubeSource Empty :=
  normalizedScalarCubeSourceOfIntegerPMF
    (principalIntervalLength K T γ) (principalIntervalLength_pos hK hT hγ)
    (principalIntegerPMF K T γ hK hT hγ hlarge)
    (fun k hk => principalIntervalLength_support hK hT hγ hlarge hk)
    (principalIntervalWeight K T γ) 16 (128 * probabilityProfileLipschitz) (by norm_num)
    (principalIntervalWeight_range hK hT hγ hlarge)
    (principalIntervalWeight_lipschitz hK hT hγ hlarge)
    (principalIntervalWeight_grid hK hT hγ hlarge)

variable {K T γ : ℝ} (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
variable (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

noncomputable def scalarSourceTransitionBound : ℝ≥0 :=
  Classical.choose exists_smoothTransition_lipschitz

theorem scalarSourceTransitionBound_spec :
    1 ≤ scalarSourceTransitionBound ∧
      LipschitzWith scalarSourceTransitionBound Real.smoothTransition :=
  Classical.choose_spec exists_smoothTransition_lipschitz

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RationalFrequencyHeight
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

variable {L ι κ : Type*} [AddCommGroup L] [Module ℚ L]

theorem basisFrequency_logHeight_le (e : Basis κ ℚ L) (b : Basis ι ℚ L)
    (S : Set ι) [Fintype S] (N : ℕ) (hN : 0 < N) (n : S → ℤ)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card S : ℝ) ≤ p)
    (hNp : (N : ℝ) ≤ Real.exp p) (hn : ∀ j, (|n j| : ℝ) ≤ Real.exp p)
    (hb : ∀ i j, rationalLogHeight (b.repr (e i) j) ≤ p) (i : κ) :
    rationalLogHeight (basisFrequency b S N n (e i)) ≤ (p + 2) ^ 4 := by
  classical
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hfrac (j : S) : RationalHeightLE ((n j : ℚ) / (N : ℚ)) H := by
    have ha : (n j).natAbs ≤ H := by
      apply (Nat.cast_le (α := ℝ)).mp
      simpa only [Nat.cast_natAbs, Int.cast_abs] using (hn j).trans (Nat.le_ceil (Real.exp p))
    have hbN : (N : ℤ).natAbs ≤ H := by
      simpa only [Int.natAbs_natCast] using
        (Nat.cast_le.mp (hNp.trans (Nat.le_ceil (Real.exp p))) : N ≤ H)
    simpa only [Int.cast_natCast] using
      rationalHeightLE_fraction (n j) (N : ℤ) (by exact_mod_cast hN.ne') ha hbN
  have hterms (j : S) :
      RationalHeightLE (((n j : ℚ) / (N : ℚ)) * b.repr (e i) j) (H * H) :=
    (hfrac j).mul (rationalHeightLE_ceil_exp (hb i j))
  have hHH : ((H * H : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp (p + 1) * Real.exp (p + 1) := by gcongr
      _ = Real.exp (2 * p + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
  rw [basisFrequency_apply]
  apply (rationalLogHeight_le_iff _ _).mpr
  simpa only [show (2 + 1 + 1 : ℕ) = 4 from rfl] using
    rational_sum_exp_height _ hterms hp 2 1 hHH (by simpa using hd.trans (by linarith : p ≤ p + 2))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LocalNiltestFixedNativePartners
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {L σ τ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

noncomputable def withOrbit (T : D.Niltest w)
    (g : D.filtration.realification.PolynomialOrbit v) : D.Niltest v where
  orbit := g
  observable := T.observable
  normBound := T.normBound
  lipBound := T.lipBound
  norm_le := T.norm_le
  lipschitz := T.lipschitz

theorem withOrbit_complexity (T : D.Niltest w)
    (g : D.filtration.realification.PolynomialOrbit v) (p : ℝ) :
    (T.withOrbit g).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

theorem withOrbit_eval (T : D.Niltest w)
    (g : D.filtration.realification.PolynomialOrbit v) (x : τ → ℤ) :
    (T.withOrbit g).eval x = T.observable
      (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval v x g)) := rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def constantGroupOrbit (g : F.Group) : F.PolynomialOrbit w :=
  polynomialOrbitOfLog (monomial (R := ℚ) 0 g.coord)
    ((F.mem_adaptedSubmodule w _).mp
      (F.monomial_mem_adaptedSubmodule w 0 (by
        simp only [map_zero]
        exact F.antitone (Nat.zero_le 1) (by simp [F.one_eq_top]))))

@[simp] theorem polynomialOrbitEval_constantGroupOrbit (g : F.Group) (x : σ → ℤ) :
    F.polynomialOrbitEval w x (F.constantGroupOrbit w g) = g := by
  apply NilpotentLieBCHGroup.ext
  simp [polynomialOrbitEval_coord, constantGroupOrbit, eval_monomial]

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {L σ τ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

noncomputable def withLeftTranslatedOrbit (T : D.Niltest w) (g : D.RealGroup)
    (orbit : D.filtration.realification.PolynomialOrbit v) : D.Niltest v :=
  T.withOrbit (D.filtration.realification.constantGroupOrbit v g * orbit)

@[simp] theorem withLeftTranslatedOrbit_observable (T : D.Niltest w) (g : D.RealGroup)
    (orbit : D.filtration.realification.PolynomialOrbit v) :
    (T.withLeftTranslatedOrbit g orbit).observable = T.observable := rfl

@[simp] theorem withLeftTranslatedOrbit_complexity (T : D.Niltest w) (g : D.RealGroup)
    (orbit : D.filtration.realification.PolynomialOrbit v) (p : ℝ) :
    (T.withLeftTranslatedOrbit g orbit).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

@[simp] theorem withLeftTranslatedOrbit_eval (T : D.Niltest w) (g : D.RealGroup)
    (orbit : D.filtration.realification.PolynomialOrbit v) (x : τ → ℤ) :
    (T.withLeftTranslatedOrbit g orbit).eval x = T.observable
      (g • QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval v x orbit)) := by
  rw [withLeftTranslatedOrbit, withOrbit_eval, map_mul,
    NilpotentLieFiltration.polynomialOrbitEval_constantGroupOrbit]
  rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {L X Y Ω T : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L 0 d} {w : Y → ℕ}

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open scoped BigOperators TensorProduct Classical

variable {L Y Ω T X K : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : Y → ℕ}

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.NaturalFrequencyMultiples
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem rationalLogHeight_nat_mul (n : ℕ) {x : ℚ} {p : ℝ}
    (hx : rationalLogHeight x ≤ p) : rationalLogHeight ((n : ℚ) * x) ≤ p + n + 1 := by
  have hp : 0 ≤ p := (rationalLogHeight_nonneg x).trans hx
  have hn : RationalHeightLE (n : ℚ) (n + 1) := by
    simp [RationalHeightLE]
  apply rationalLogHeight_le_of_height (hn.mul (rationalHeightLE_ceil_exp hx))
  calc
    (((n + 1) * ⌈Real.exp p⌉₊ : ℕ) : ℝ) = ((n : ℝ) + 1) * (⌈Real.exp p⌉₊ : ℝ) := by push_cast; rfl
    _ ≤ Real.exp (n : ℝ) * Real.exp (p + 1) :=
      mul_le_mul (Real.add_one_le_exp _) (ceil_exp_le_exp_add_one hp)
        (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (p + n + 1) := by rw [← Real.exp_add]; congr 1; ring

theorem realifyFunctional_nsmul {L : Type*} [AddCommGroup L] [Module ℚ L]
    (n : ℕ) (η : L →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] L) :
    realifyFunctional (n • η) x = n • realifyFunctional η x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [realifyFunctional_tmul, LinearMap.smul_apply, nsmul_eq_mul,
      Rat.cast_mul, Rat.cast_natCast]
    ring
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductComponentCoordinates
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem productFinBasis_repr_component (x : ∀ i, L i) (a : ι) (k : Fin (d a)) :
    (D a).basis.repr (x a) k =
      (pi D).basis.repr x (Fintype.equivFin (Σ i, Fin (d i)) ⟨a, k⟩) := by
  symm
  exact (productFinBasis_repr D x _).trans
    (congrArg (fun z : Σ i, Fin (d i) => (D z.1).basis.repr (x z.1) z.2)
      (Equiv.symm_apply_apply _ _))

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeRankBudget
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

abbrev RankAlphabet := Σ i : Fin (s + 1), Fin (finrank ℚ (D.filtration.layer (i.val + 1)))

def rankAlphabetWeight (a : D.RankAlphabet) : ℕ := a.1.val + 1

noncomputable def rankAlphabetVector (a : D.RankAlphabet) : L := D.layerBasis a.1 a.2

theorem rankAlphabetWeight_pos (a : D.RankAlphabet) : 0 < D.rankAlphabetWeight a := Nat.succ_pos _

theorem rankAlphabetVector_mem (a : D.RankAlphabet) :
    D.rankAlphabetVector a ∈ D.filtration.layer (D.rankAlphabetWeight a) :=
  (D.layerBasis a.1 a.2).property

theorem rankAlphabet_spans_layer (i : ℕ) (hi : 0 < i) :
    D.filtration.layer i ≤ Submodule.span ℚ
      (D.rankAlphabetVector '' {a | D.rankAlphabetWeight a = i}) := by
  by_cases his : i ≤ s + 1
  · let j : Fin (s + 1) := ⟨i - 1, by omega⟩
    have hj : j.val + 1 = i := by dsimp [j]; omega
    have heq : D.filtration.layer i = Submodule.span ℚ
        (Set.range (fun k => ((D.layerBasis j k : D.filtration.layer (j.val + 1)) : L))) := by
      rw [span_submodule_basis, hj]
    rw [heq]
    apply Submodule.span_mono
    rintro x ⟨k, rfl⟩
    exact ⟨⟨j, k⟩, hj, rfl⟩
  · have hbot : D.filtration.layer i = ⊥ := by
      apply bot_unique
      exact (D.filtration.antitone (show s + 1 ≤ i by omega)).trans D.filtration.terminal.le
    rw [hbot]
    exact bot_le

theorem rankAlphabet_span_layer (i : ℕ) (hi : 0 < i) :
    Submodule.span ℚ (D.rankAlphabetVector '' {a | D.rankAlphabetWeight a = i}) =
      D.filtration.layer i := by
  apply le_antisymm _ (D.rankAlphabet_spans_layer i hi)
  apply Submodule.span_le.mpr
  rintro x ⟨a, ha, rfl⟩
  exact ha ▸ D.rankAlphabetVector_mem a

noncomputable def finiteRankGenerators (i r : ℕ) : Finset L := by
  classical
  exact ((Finset.univ.filter (fun a : D.RankAlphabet => D.rankAlphabetWeight a = i + 1)).image
    D.rankAlphabetVector) ∪ finiteWeightedLieValues D.rankAlphabetVector D.rankAlphabetWeight i r

theorem finiteRankGenerators_span (i r : ℕ) :
    Submodule.span ℚ (D.finiteRankGenerators i r : Set L) = D.filtration.rankLayer i r := by
  classical
  rw [D.filtration.rankLayer_eq_weighted_tree_span D.rankAlphabetVector D.rankAlphabetWeight
    D.rankAlphabetWeight_pos D.rankAlphabetVector_mem D.rankAlphabet_spans_layer]
  rw [weightedLieTreeSpan_eq_finite_span _ _ D.rankAlphabetWeight_pos]
  have hleaf : Submodule.span ℚ
      (((Finset.univ.filter (fun a : D.RankAlphabet => D.rankAlphabetWeight a = i + 1)).image
        D.rankAlphabetVector : Finset L) : Set L) = D.filtration.layer (i + 1) := by
    simpa only [Finset.coe_image, Finset.coe_filter, Finset.mem_univ,
      true_and] using D.rankAlphabet_span_layer (i + 1) (Nat.succ_pos i)
  change Submodule.span ℚ ((_ ∪ _ : Finset L) : Set L) = _
  rw [Finset.coe_union, Submodule.span_union, hleaf]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem finiteRankGenerators_height {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    (hb : ∀ i j k, RationalHeightLE (D.basis.repr (D.layerBasis i j) k) H)
    (i r : ℕ) (hi : i ≤ s) (x : L) (hx : x ∈ D.finiteRankGenerators i r) (k : Fin d) :
    RationalHeightLE (D.basis.repr x k) (lieTreeHeight d H s) := by
  classical
  rcases Finset.mem_union.mp hx with h | h
  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp h
    exact (hb a.1 a.2 k).mono (lieTreeHeight_ge_input d H s)
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
    have h := finiteLieTrees_coordinate_height D.basis D.rankAlphabetVector hc
      (fun a j => hb a.1 a.2 j) i a (Finset.mem_filter.mp ha).1 k
    simp only [Fintype.card_fin] at h
    exact h.mono (lieTreeHeight_mono d H hi)

theorem exists_rankLayer_basis_height {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    (hb : ∀ i j k, RationalHeightLE (D.basis.repr (D.layerBasis i j) k) H)
    (i r : ℕ) (hi : i ≤ s) :
    ∃ b : Basis (Fin (finrank ℚ (D.filtration.rankLayer i r))) ℚ (D.filtration.rankLayer i r),
      ∀ j k, RationalHeightLE (D.basis.repr (b j : L) k) (lieTreeHeight d H s) := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (D.finiteRankGenerators i r : Set L)
  rw [D.finiteRankGenerators_span] at hex
  obtain ⟨v, hv, hvspan, hli⟩ := hex
  refine ⟨(Basis.span hli).map (LinearEquiv.ofEq _ _ hvspan), ?_⟩
  intro j k
  simp only [Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]
  exact D.finiteRankGenerators_height hc hb i r hi (v j) (hv j) k

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_canonical_rank_basis_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → ∀ i r : ℕ, i ≤ s →
      ∃ b : Basis (Fin (finrank ℚ (D.filtration.rankLayer i r))) ℚ (D.filtration.rankLayer i r),
        (finrank ℚ (D.filtration.rankLayer i r) : ℝ) ≤ p ∧
        ∀ j k, rationalLogHeight (D.basis.repr (b j : L) k) ≤ (p + C) ^ C := by
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + 3 : Polynomial ℕ) ^ (6 * s + 2))
  refine ⟨C, hC, ?_⟩
  intro L _ _ d D p hp hD i r hi
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  have hcost : (p + 3) ^ (6 * s + 2) ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  have htree : (lieTreeHeight d ⌈Real.exp p⌉₊ s : ℝ) ≤ Real.exp ((p + 3) ^ (6 * s + 2)) := by
    simpa only [add_assoc, show (1 : ℝ) + 2 = 3 by norm_num] using
      lieTreeHeight_le_exp d ⌈Real.exp p⌉₊ s (p := p + 1) (by linarith)
        (hD.1.trans (by linarith)) (ceil_exp_le_exp_add_one hp)
  obtain ⟨b, hb⟩ := D.exists_rankLayer_basis_height
    (fun a b c => rationalHeightLE_ceil_exp (hD.2.2.1 a b c))
    (fun a b c => rationalHeightLE_ceil_exp (hD.2.2.2 a b c)) i r hi
  refine ⟨b, ?_, fun j k => rationalLogHeight_le_of_height (hb j k)
    (htree.trans (Real.exp_le_exp.mpr hcost))⟩
  have hdim : finrank ℚ (D.filtration.rankLayer i r) ≤ d := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using
      (D.filtration.rankLayer i r).finrank_le
  exact (Nat.cast_le.mpr hdim).trans hD.1

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSlowConstantProduct
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

theorem exists_native_slow_left_constant_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) (weight : Fin d → ℕ)
      (_hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ weight i}))
      (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      ∀ A : σ → ℝ, (∀ i, 0 < A i) → ∀ a : D.RealGroup,
      (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp p) →
      ∀ e : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      D.filtration.PolynomialSlowBound D.basis (fun _ => 1) A (Real.exp p) e →
      D.filtration.PolynomialSlowBound D.basis (fun _ => 1) A (Real.exp ((p + C) ^ C))
        (D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) a * e) := by
  obtain ⟨c, _, hproduct⟩ := exists_polynomial_slow_product_bound s 1 2
  let P : Polynomial ℕ := (Polynomial.X + 1 + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ d D weight hF p hp hD hσ A hA a ha e he
  have hbound : (p + 1 + c) ^ c ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  let cA := D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) a
  have hcA : D.filtration.PolynomialSlowBound D.basis (fun _ => 1) A (Real.exp p) cA :=
    D.filtration.polynomialSlowBound_constant D.basis (fun _ => 1) A hA (Real.exp_nonneg p) a ha
  have hsmall : Real.exp p ≤ Real.exp ((p + 1 + 2) ^ (1 : ℕ)) :=
    Real.exp_le_exp.mpr (by simp only [pow_one]; linarith)
  have hlist : ∀ r ∈ [cA, e], D.filtration.PolynomialSlowBound D.basis (fun _ => 1) A
      (Real.exp ((p + 1 + 2) ^ (1 : ℕ))) r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact D.filtration.polynomialSlowBound_mono D.basis (fun _ => 1) A hA hsmall cA hcA
    · have hr' : r = e := List.mem_singleton.mp hr
      subst r
      exact D.filtration.polynomialSlowBound_mono D.basis (fun _ => 1) A hA hsmall e he
  have hout := hproduct D.filtration D.basis weight hF (fun _ : σ => 1)
    (fun _ => Nat.zero_lt_one) ⌈Real.exp p⌉₊ (p + 1) (one_le_ceil_exp p) (by linarith)
    (by simpa only [Fintype.card_fin] using hD.1.trans (by linarith : p ≤ p + 1))
    (hσ.trans (by linarith)) (ceil_exp_le_exp_add_one hp)
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)) A hA [cA, e]
    (by simp) hlist
  have hslow : D.filtration.PolynomialSlowBound D.basis (fun _ => 1) A
      (Real.exp ((p + 1 + c) ^ c)) (cA * e) := by
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hout
  exact D.filtration.polynomialSlowBound_mono D.basis (fun _ => 1) A hA
    (Real.exp_le_exp.mpr hbound) (cA * e) hslow

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealRankHorizontalSymbol
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

noncomputable def realHorizontalSymbolHom (hs : 1 ≤ s) (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.associatedDegree.RealPolynomialSymbolGroup w →*
      Multiplicative (ℝ ⊗[ℚ] F.HigherHorizontal (Finsupp.weight w α)) where
  toFun X := Multiplicative.ofAdd ((F.higherHorizontalSymbolCoefficient w α).baseChange ℝ X.coord)
  map_one' := by
    change Multiplicative.ofAdd ((F.higherHorizontalSymbolCoefficient w α).baseChange ℝ 0) = 1
    rw [map_zero]
    rfl
  map_mul' X Y := by
    change Multiplicative.ofAdd ((F.higherHorizontalSymbolCoefficient w α).baseChange ℝ
      (lieBCH s X.coord Y.coord)) = Multiplicative.ofAdd
        ((F.higherHorizontalSymbolCoefficient w α).baseChange ℝ X.coord +
          (F.higherHorizontalSymbolCoefficient w α).baseChange ℝ Y.coord)
    exact congrArg Multiplicative.ofAdd (linearMap_baseChange_lieBCH_eq_add
      (F.higherHorizontalSymbolCoefficient w α) (F.higherHorizontalSymbolCoefficient_lie w α)
      hs X.coord Y.coord)

@[simp] theorem realHorizontalSymbolHom_apply (hs : 1 ≤ s) (w : σ → ℕ) (α : σ →₀ ℕ)
    (X : F.associatedDegree.RealPolynomialSymbolGroup w) :
    Multiplicative.toAdd (F.realHorizontalSymbolHom hs w α X) =
      (F.higherHorizontalSymbolCoefficient w α).baseChange ℝ X.coord := rfl

theorem realHorizontalSymbolCoefficient_extended (w : σ → ℕ) (α : σ →₀ ℕ)
    (x : ℝ ⊗[ℚ] F.associatedDegree.adaptedLieSubalgebra w) :
    (F.higherHorizontalSymbolCoefficient w α).baseChange ℝ
      (F.associatedDegree.realExtendedSymbolMap w x) =
        (F.higherHorizontalCoefficient w α).baseChange ℝ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a p =>
    change (F.higherHorizontalSymbolCoefficient w α).baseChange ℝ
      (a ⊗ₜ[ℚ] F.associatedDegree.polynomialSymbolMap w p) =
        (F.higherHorizontalCoefficient w α).baseChange ℝ (a ⊗ₜ[ℚ] p)
    simp only [LinearMap.baseChange_tmul, F.higherHorizontalSymbolCoefficient_map]
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def realHorizontalPolynomialHom (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) :
    (F.associatedDegree.realification.adaptedPolynomialFiltration w).Group →*
      Multiplicative (ℝ ⊗[ℚ] F.HigherHorizontal (Finsupp.weight w α)) :=
  (F.realHorizontalSymbolHom hs w α).comp
    (F.associatedDegree.realPolynomialSymbolHom b ω hF w)

end Erdos3.DegreeRankLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PrescribedFastPolynomialFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def realPolynomialSymbolQuotientLinear :
    F.realification.PolynomialSymbol w →ₗ[ℚ] F.RealPolynomialSymbol w :=
  (F.realification.shiftedAdaptedIdeal w).toSubmodule.liftQ
    (F.realPolynomialSymbolMap b ω hlayers w).toLinearMap (by
      intro p hp
      apply (F.realPolynomialSymbolMap_eq_zero_iff b ω hlayers w p).mpr
      exact (F.realification.polynomialSymbolMap_eq_zero_iff w p).mpr hp)

@[simp] theorem realPolynomialSymbolQuotientLinear_map
    (p : F.realification.adaptedLieSubalgebra w) :
    F.realPolynomialSymbolQuotientLinear b ω hlayers w
      (F.realification.polynomialSymbolMap w p) = F.realPolynomialSymbolMap b ω hlayers w p := rfl

noncomputable def realPolynomialSymbolQuotientHom :
    F.realification.PolynomialSymbol w →ₗ⁅ℚ⁆ F.RealPolynomialSymbol w where
  toLinearMap := F.realPolynomialSymbolQuotientLinear b ω hlayers w
  map_lie' {x y} := by
    obtain ⟨p, rfl⟩ := F.realification.polynomialSymbolMap_surjective w x
    obtain ⟨q, rfl⟩ := F.realification.polynomialSymbolMap_surjective w y
    change F.realPolynomialSymbolQuotientLinear b ω hlayers w
      ⁅F.realification.polynomialSymbolMap w p, F.realification.polynomialSymbolMap w q⁆ = _
    rw [← LieHom.map_lie, F.realPolynomialSymbolQuotientLinear_map]
    exact (F.realPolynomialSymbolMap b ω hlayers w).map_lie p q

theorem realPolynomialSymbolQuotientHom_bijective :
    Function.Bijective (F.realPolynomialSymbolQuotientHom b ω hlayers w) := by
  constructor
  · intro x y hxy
    obtain ⟨p, rfl⟩ := F.realification.polynomialSymbolMap_surjective w x
    obtain ⟨q, rfl⟩ := F.realification.polynomialSymbolMap_surjective w y
    apply (F.realSymbolOfPolynomial_eq_iff_symbolMap_eq b ω hlayers w p q).mp
    exact hxy
  · intro x
    obtain ⟨p, hp⟩ := F.realPolynomialSymbolMap_surjective b ω hlayers w x
    exact ⟨F.realification.polynomialSymbolMap w p, hp⟩

noncomputable def realPolynomialSymbolQuotientEquiv :
    F.realification.PolynomialSymbol w ≃ₗ⁅ℚ⁆ F.RealPolynomialSymbol w :=
  LieEquiv.ofBijective (F.realPolynomialSymbolQuotientHom b ω hlayers w)
    (F.realPolynomialSymbolQuotientHom_bijective b ω hlayers w)

@[simp] theorem realPolynomialSymbolQuotientEquiv_map
    (p : F.realification.adaptedLieSubalgebra w) :
    F.realPolynomialSymbolQuotientEquiv b ω hlayers w
      (F.realification.polynomialSymbolMap w p) = F.realPolynomialSymbolMap b ω hlayers w p := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_bounded_polynomial_normalization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ) (Γ : Subgroup F.Group) (l H : ℕ) (p : ℝ),
      0 < l → scaledIntegerGrid l ⊆ bchSubgroupCoordinates b Γ →
      (∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      ∀ g : (F.realification.adaptedPolynomialFiltration w).Group,
      ∃ (r γ : F.realification.Group) (q : (F.realification.adaptedPolynomialFiltration w).Group),
        (∀ i, |(b.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
        γ ∈ Γ.map NilpotentLieBCHGroup.realificationHom ∧
        F.realification.adaptedConstantGroupHom w r * q *
          F.realification.adaptedConstantGroupHom w γ = g ∧
        coefficients (q.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        F.realPolynomialSymbolHom b ω hlayers w q = F.realPolynomialSymbolHom b ω hlayers w g := by
  obtain ⟨C, hC, hrep⟩ := exists_realification_representatives_exp_bound s
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ _ _ F b ω hlayers w Γ l H p hl hinner hb hp hd hH hlp g
  obtain ⟨r, hr, γ, hγ, hconst⟩ := hrep b F.lowerCentralSeries_eq_bot Γ l H p hl hinner hb hp hd hH hlp
    (F.realification.adaptedPolynomialConstantHom w g)
  obtain ⟨q, hfactor, hzero, hsymbol⟩ := F.realification.exists_constant_normalized_polynomial w g r γ hconst
  refine ⟨r, γ, q, hr, hγ, hfactor, hzero, ?_⟩
  apply NilpotentLieBCHGroup.ext
  exact congrArg (F.realPolynomialSymbolQuotientEquiv b ω hlayers w)
    (congrArg NilpotentLieBCHGroup.coord hsymbol)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

theorem exists_native_polynomial_normalization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (weight : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ weight i}))
      (w : σ → ℕ) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      ∀ g : (D.filtration.realification.adaptedPolynomialFiltration w).Group,
      ∃ (a κ : D.RealGroup) (q : (D.filtration.realification.adaptedPolynomialFiltration w).Group),
        (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
        κ ∈ D.realLattice ∧
        D.filtration.realification.adaptedConstantGroupHom w a * q *
          D.filtration.realification.adaptedConstantGroupHom w κ = g ∧
        coefficients (q.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        D.filtration.realPolynomialSymbolHom D.basis weight hF w q =
          D.filtration.realPolynomialSymbolHom D.basis weight hF w g := by
  obtain ⟨c, _, hnormalize⟩ := exists_bounded_polynomial_normalization s
  let P : Polynomial ℕ := (Polynomial.X + 1 + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ D weight hF w p hp hD g
  have hbound : (p + 1 + c) ^ c ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨a, κ, q, ha, hκ, hfactor, hzero, hsymbol⟩ :=
    hnormalize D.filtration D.basis weight hF w D.lattice D.grid ⌈Real.exp p⌉₊ (p + 1)
      D.grid_pos D.inner_grid
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)) (by linarith)
      (by simpa only [Fintype.card_fin] using hD.1.trans (by linarith : p ≤ p + 1))
      (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith))) g
  exact ⟨a, κ, q, fun i => (ha i).trans (Real.exp_le_exp.mpr hbound), hκ,
    hfactor, hzero, hsymbol⟩

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (w : σ → ℕ)

noncomputable def realFilteredSymbolGroupMap :
    F.RealPolynomialSymbolGroup w →* G.RealPolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (hM := G.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (F.filteredPolynomialSymbolMap G φ hφ w)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeFrozenMultidegreeNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (S : Finset σ)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.weightedSubalgebra (retainedCoordinateWeight S))]

theorem exists_frozen_niltest {n : ℕ}
    (E : RationalFilteredNilmanifold (M.filtration.weightedSubalgebra (retainedCoordinateWeight S))
      (multidegreeWeight (retainedCoordinateWeight S) bound) n)
    (hEF : E.filtration = M.filtration.weightedFiltration (retainedCoordinateWeight S))
    (hEL : E.lattice = D.lattice.comap
      (mapOfSteps (M.filtration.weightedSubalgebra (retainedCoordinateWeight S)).incl))
    (b : σ → ℤ) (p : M.filtration.realification.PolynomialOrbit)
    (u : D.Space → ℂ) (ℓ B : ℝ≥0)
    (hu : letI := D.metricSpace; LipschitzWith ℓ u) (hub : ∀ x, ‖u x‖ ≤ B)
    (a γ : D.RealGroup) (hγ : γ ∈ D.realLattice)
    (hfactor : M.filtration.realification.polynomialOrbitEval (freezeCoordinates S b 0) p = a * γ)
    (A : ℝ≥0) (hA : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => a • x))
    (H : ℕ) (he : ∀ i k, RationalHeightLE (D.basis.repr (E.basis i : L) k) H) :
    ∃ T : E.Niltest (fun _ : S => 1), T.normBound = B ∧
      T.lipBound = ℓ * (A * coordinateLipschitzBound d n H) ∧
      E.filtration.realification.polynomialOrbitEval _ 0 T.orbit = 1 ∧
      ∀ x, T.eval x = u (QuotientGroup.mk
        (M.filtration.realification.polynomialOrbitEval (freezeCoordinates S b x) p)) := by
  let c := retainedCoordinateWeight S
  let K := M.filtration.weightedSubalgebra c
  let F := M.filtration.weightedFiltration c
  have hΓ : E.lattice ≤ D.lattice.comap (mapOfSteps K.incl) := by rw [hEL]
  let φ : E.RealGroup →* D.RealGroup := realificationMap
    (hnil := E.filtration.lowerCentralSeries_eq_bot) (hM := D.filtration.lowerCentralSeries_eq_bot) K.incl
  have hφ : E.realLattice ≤ D.realLattice.comap φ :=
    realificationMap_subgroup K.incl E.lattice D.lattice hΓ
  let π : E.Space → D.Space := cosetMap E.realLattice D.realLattice φ hφ
  have hπ : letI := E.metricSpace; letI := D.metricSpace
      LipschitzWith (coordinateLipschitzBound d n H) π := by
    let : MetricSpace (E.RealGroup ⧸ E.lattice.map realificationHom) :=
      realificationQuotientMetricSpace E.basis E.lattice E.grid E.grid_pos E.outer_grid
    let : MetricSpace (D.RealGroup ⧸ D.lattice.map realificationHom) :=
      realificationQuotientMetricSpace D.basis D.lattice D.grid D.grid_pos D.outer_grid
    exact (lipschitz_realificationMap_quotient E.basis D.basis K.incl E.lattice D.lattice hΓ
      E.grid D.grid E.grid_pos D.grid_pos E.outer_grid D.outer_grid H
      (fun k i => he i k)).weaken (by simp only [Fintype.card_fin]; exact le_rfl)
  obtain ⟨q, hq, hval⟩ := M.filtration.exists_real_normalized_frozen_orbit S b p a γ hfactor
  have hF : F.realification = E.filtration.realification := by rw [hEF]
  let qE := F.realification.orbitEquivOfEq hF (fun _ : S => 1) q
  have hqE (x : S → ℤ) : E.filtration.realification.polynomialOrbitEval _ x qE =
      F.realification.polynomialOrbitEval _ x q :=
    F.realification.orbitEquivOfEq_eval hF _ q x
  have hvalE (x : S → ℤ) : φ (E.filtration.realification.polynomialOrbitEval _ x qE) =
      a⁻¹ * M.filtration.realification.polynomialOrbitEval (freezeCoordinates S b x) p * γ⁻¹ := by
    rw [hqE]
    exact hval x
  let T : E.Niltest (fun _ : S => 1) :=
    { orbit := qE
      observable := fun x => u (a • π x)
      normBound := B
      lipBound := ℓ * (A * coordinateLipschitzBound d n H)
      norm_le := fun _ => hub _
      lipschitz := by
        let := E.metricSpace
        let := D.metricSpace
        exact hu.comp (hA.comp hπ) }
  refine ⟨T, rfl, rfl, (hqE 0).trans hq, ?_⟩
  intro x
  change u (a • π (QuotientGroup.mk
    (E.filtration.realification.polynomialOrbitEval _ x qE))) = _
  rw [show π (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval _ x qE)) =
      QuotientGroup.mk (φ (E.filtration.realification.polynomialOrbitEval _ x qE)) from rfl, hvalE]
  simp only [MulAction.Quotient.smul_mk, smul_eq_mul, ← mul_assoc, mul_inv_cancel, one_mul]
  exact congrArg u (QuotientGroup.mk_mul_of_mem _ (D.realLattice.inv_mem hγ))

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VerticalTranslations
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup CircleFourier

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem vertical_left_translate (F : D.Space → ℂ) (eta : L →ₗ[ℚ] ℚ)
    (hF : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
      F (z • x) = character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * F x)
    (a : D.RealGroup) (z : D.RealGroup) (hz : z ∈ D.filtration.realification.subgroup s)
    (x : D.Space) :
    F (a • (z • x)) =
      character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * F (a • x) := by
  have hc : Commute z a := commute_of_lie_eq_zero z a
    (D.filtration.realification.top_layer_central hz a.coord)
  rw [← mul_smul, hc.eq.symm, mul_smul]
  exact hF z hz (a • x)

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeTotalDegreeMultifiltration
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem exists_totalDegree_layer_basis (n : ℕ) {p : ℝ} (hD : D.GeometryComplexityLE p) :
    ∃ b : Basis (Fin (finrank ℚ (D.filtration.layer n))) ℚ (D.filtration.layer n),
      ∀ j k, rationalLogHeight (D.basis.repr (b j : L) k) ≤ p := by
  by_cases hn : n = 0
  · subst n
    have hzero : D.filtration.layer 0 = D.filtration.layer 1 :=
      D.filtration.totalDegree_zero_layer.trans D.filtration.one_eq_top.symm
    rw [hzero]
    exact D.exists_positive_layer_basis 1 le_rfl hD
  · exact D.exists_positive_layer_basis n (by omega) hD

noncomputable def totalDegreeMultidegree (σ : Type*) [Fintype σ] [Nonempty σ]
    {p : ℝ} (hD : D.GeometryComplexityLE p) : D.MultidegreeStructure (fun _ : σ => s) where
  filtration := D.filtration.totalDegreeMultifiltration σ
  ordinary := rfl
  basis a := Classical.choose (D.exists_totalDegree_layer_basis (∑ i, (a i).val) hD)

theorem totalDegreeMultidegree_complexity (σ : Type*) [Fintype σ] [Nonempty σ]
    {p : ℝ} (hD : D.GeometryComplexityLE p) :
    (D.totalDegreeMultidegree σ hD).ComplexityLE p :=
  ⟨hD, fun a => Classical.choose_spec (D.exists_totalDegree_layer_basis (∑ i, (a i).val) hD)⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AntisymmetricPartitionApproximation
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

namespace NativeAntisymmetricOrbitFactors

variable {p q : ℝ}
  {N : ℕ}

end NativeAntisymmetricOrbitFactors

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold

end Erdos3

end

section

namespace Erdos3.NativeAntisymmetricOrbitFactors

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

variable {p q : ℝ}
  {N : ℕ}

end Erdos3.NativeAntisymmetricOrbitFactors

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

theorem RationalFilteredNilmanifold.observable_frozen_right_eq
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (u : D.Space → ℂ)
    (a b r r' : D.RealGroup)
    (h : (QuotientGroup.mk r : D.Space) = QuotientGroup.mk r') :
    u (QuotientGroup.mk (a * b * r)) = u (QuotientGroup.mk (a * b * r')) :=
  congrArg (fun x : D.Space => u ((a * b) • x)) h

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BoxNiltestDetection
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct BigOperators

variable {σ L Ω : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L 0 d) {w : σ → ℕ}

theorem norm_correlation_step_zero_sample (T : D.Niltest w)
    (Q : Finset Ω) (x : Ω → (σ → ℤ)) (f : Ω → ℂ) :
    ‖finiteCorrelation Q f (fun a => T.eval (x a))‖ ≤
      (T.normBound : ℝ) * ‖𝔼 a ∈ Q, f a‖ := by
  calc
    _ = ‖𝔼 a ∈ Q, f a‖ * ‖T.observable (QuotientGroup.mk (1 : D.RealGroup))‖ := by
      simp only [finiteCorrelation, eval_step_zero D, ← Finset.expect_mul, norm_mul, norm_star]
    _ ≤ _ := by
      rw [mul_comm (T.normBound : ℝ)]
      exact mul_le_mul_of_nonneg_left (T.norm_le _) (norm_nonneg _)

theorem detection_step_zero_sample (T : D.Niltest w) {p ρ : ℝ}
    (hT : T.ComplexityLE p) (Q : Finset Ω) (x : Ω → (σ → ℤ)) (f : Ω → ℂ)
    (hcorr : ρ ≤ ‖finiteCorrelation Q f (fun a => T.eval (x a))‖) :
    ρ / Real.exp p ≤ ‖𝔼 a ∈ Q, f a‖ := by
  apply (div_le_iff₀ (Real.exp_pos p)).mpr
  have hB : (T.normBound : ℝ) ≤ Real.exp p := by
    have hh := T.observable_budget hT
    linarith [T.lipBound.coe_nonneg]
  have hc := hcorr.trans (norm_correlation_step_zero_sample D T Q x f)
  exact hc.trans (by nlinarith [norm_nonneg (𝔼 a ∈ Q, f a)])

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open scoped TensorProduct

def BoxNiltestDetection.{u,v} (s : ℕ) (F : ℝ → ℝ) : Prop :=
  ∀ {σ : Type v} [Fintype σ] [DecidableEq σ] {L : Type u} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d) (p : ℝ),
    0 ≤ p → (Fintype.card σ : ℝ) ≤ p → ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
    ∀ (T : D.Niltest w), T.ComplexityLE p →
    ∀ (a : σ → ℤ) (lengths : σ → ℕ) [∀ i, NeZero (lengths i)] (f : (σ → ℤ) → ℂ),
    (∀ x ∈ translatedIntegerBox a lengths, ‖f x‖ ≤ 1) →
    Real.exp (-p) ≤ ‖finiteCorrelation (translatedIntegerBox a lengths) f T.eval‖ →
    Real.exp (-F p) ≤ finiteSupportGowersNorm (s + 1) (translatedIntegerBox a lengths) f

theorem boxNiltestDetection_zero.{u,v} : BoxNiltestDetection.{u,v} 0 (fun p => 2 * p) := by
  intro σ _ _ L _ _ d _ _ _ _ D p hp hσ w hw T hT a lengths _ f hf hc
  have hb := RationalFilteredNilmanifold.Niltest.detection_step_zero_sample
    D T hT (translatedIntegerBox a lengths) id f hc
  have he : Real.exp (-p) / Real.exp p = Real.exp (-(2 * p)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [he] at hb
  rw [translatedIntegerBox_norm_degree_one]
  exact hb

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RationalModelCoordinates
namespace OAI

section

namespace Erdos3

open Module

abbrev RationalModelCoordinateIndex (s d : ℕ) :=
  (Fin d × Fin d × Fin d) ⊕ (Fin (s + 1) × Fin d × Fin d)

namespace RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

noncomputable def paddedLayerVector (i : Fin (s + 1)) (k : Fin d) : L :=
  if h : k.val < finrank ℚ (D.filtration.layer (i.val + 1)) then
    (D.layerBasis i ⟨k.val, h⟩ : L) else 0

theorem paddedLayerVector_span (i : Fin (s + 1)) :
    Submodule.span ℚ (Set.range (D.paddedLayerVector i)) = D.filtration.layer (i.val + 1) := by
  classical
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  have hd : finrank ℚ (D.filtration.layer (i.val + 1)) ≤ d := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using
      (D.filtration.layer (i.val + 1)).finrank_le
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    dsimp only [paddedLayerVector]
    split_ifs
    · exact (D.layerBasis i _).property
    · exact Submodule.zero_mem _
  · intro x hx
    have hb (k : Fin (finrank ℚ (D.filtration.layer (i.val + 1)))) :
        (D.layerBasis i k : L) ∈ Submodule.span ℚ (Set.range (D.paddedLayerVector i)) := by
      apply Submodule.subset_span
      refine ⟨⟨k.val, k.isLt.trans_le hd⟩, ?_⟩
      simp only [paddedLayerVector, k.isLt, dite_true]
    have heq : (∑ k, (D.layerBasis i).repr ⟨x, hx⟩ k • (D.layerBasis i k : L)) = x := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using
        congrArg Subtype.val ((D.layerBasis i).sum_repr ⟨x, hx⟩)
    rw [← heq]
    exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (hb k))

theorem paddedLayerVector_height {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (i : Fin (s + 1)) (j k : Fin d) :
    rationalLogHeight (D.basis.repr (D.paddedLayerVector i j) k) ≤ p := by
  dsimp only [paddedLayerVector]
  split_ifs
  · exact hD.2.2.2 i _ k
  · simpa [rationalLogHeight] using hp

noncomputable def rationalModelCoordinates : RationalModelCoordinateIndex s d → ℚ
  | .inl z => lieStructureConstants D.basis z.1 z.2.1 z.2.2
  | .inr z => D.basis.repr (D.paddedLayerVector z.1 z.2.1) z.2.2

theorem rationalModelCoordinates_height {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (z : RationalModelCoordinateIndex s d) :
    rationalLogHeight (D.rationalModelCoordinates z) ≤ p := by
  rcases z with z | z
  · exact hD.2.2.1 z.1 z.2.1 z.2.2
  · exact D.paddedLayerVector_height hp hD z.1 z.2.1 z.2.2

end RationalFilteredNilmanifold
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.SumNilmanifoldFactors
namespace OAI

section

universe u

namespace Erdos3

open scoped TensorProduct

def sumLieSpace {ι κ : Type*} (L : ι → Type u) (M : κ → Type u) : ι ⊕ κ → Type u
  | .inl i => L i
  | .inr j => M j

instance sumLieRing {ι κ : Type*} {L : ι → Type u} {M : κ → Type u}
    [∀ i, LieRing (L i)] [∀ j, LieRing (M j)] (k : ι ⊕ κ) : LieRing (sumLieSpace L M k) := by
  cases k <;> dsimp [sumLieSpace] <;> infer_instance

instance sumLieAlgebra {ι κ : Type*} {L : ι → Type u} {M : κ → Type u}
    [∀ i, LieRing (L i)] [∀ j, LieRing (M j)]
    [∀ i, LieAlgebra ℚ (L i)] [∀ j, LieAlgebra ℚ (M j)] (k : ι ⊕ κ) :
    LieAlgebra ℚ (sumLieSpace L M k) := by
  cases k <;> dsimp [sumLieSpace] <;> infer_instance

instance sumRealificationTopology {ι κ : Type*} {L : ι → Type u} {M : κ → Type u}
    [∀ i, LieRing (L i)] [∀ j, LieRing (M j)]
    [∀ i, LieAlgebra ℚ (L i)] [∀ j, LieAlgebra ℚ (M j)]
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] (k : ι ⊕ κ) :
    TopologicalSpace (ℝ ⊗[ℚ] sumLieSpace L M k) := by
  cases k with
  | inl i => exact (inferInstance : TopologicalSpace (ℝ ⊗[ℚ] L i))
  | inr j => exact (inferInstance : TopologicalSpace (ℝ ⊗[ℚ] M j))

instance sumRealificationTopologicalAddGroup {ι κ : Type*} {L : ι → Type u} {M : κ → Type u}
    [∀ i, LieRing (L i)] [∀ j, LieRing (M j)]
    [∀ i, LieAlgebra ℚ (L i)] [∀ j, LieAlgebra ℚ (M j)]
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)]
    [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
    (k : ι ⊕ κ) : IsTopologicalAddGroup (ℝ ⊗[ℚ] sumLieSpace L M k) := by
  cases k with
  | inl i => exact (inferInstance : IsTopologicalAddGroup (ℝ ⊗[ℚ] L i))
  | inr j => exact (inferInstance : IsTopologicalAddGroup (ℝ ⊗[ℚ] M j))

instance sumRealificationContinuousSMul {ι κ : Type*} {L : ι → Type u} {M : κ → Type u}
    [∀ i, LieRing (L i)] [∀ j, LieRing (M j)]
    [∀ i, LieAlgebra ℚ (L i)] [∀ j, LieAlgebra ℚ (M j)]
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)]
    (k : ι ⊕ κ) : ContinuousSMul ℝ (ℝ ⊗[ℚ] sumLieSpace L M k) := by
  cases k with
  | inl i => exact (inferInstance : ContinuousSMul ℝ (ℝ ⊗[ℚ] L i))
  | inr j => exact (inferInstance : ContinuousSMul ℝ (ℝ ⊗[ℚ] M j))

instance sumRealificationT2Space {ι κ : Type*} {L : ι → Type u} {M : κ → Type u}
    [∀ i, LieRing (L i)] [∀ j, LieRing (M j)]
    [∀ i, LieAlgebra ℚ (L i)] [∀ j, LieAlgebra ℚ (M j)]
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)]
    [∀ i, T2Space (ℝ ⊗[ℚ] L i)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
    (k : ι ⊕ κ) : T2Space (ℝ ⊗[ℚ] sumLieSpace L M k) := by
  cases k with
  | inl i => exact (inferInstance : T2Space (ℝ ⊗[ℚ] L i))
  | inr j => exact (inferInstance : T2Space (ℝ ⊗[ℚ] M j))

namespace RationalFilteredNilmanifold

variable {ι κ σ : Type*} {L : ι → Type u} {M : κ → Type u}
  [∀ i, LieRing (L i)] [∀ j, LieRing (M j)]
  [∀ i, LieAlgebra ℚ (L i)] [∀ j, LieAlgebra ℚ (M j)] {s : ℕ} {d : ι → ℕ} {e : κ → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (e j))

noncomputable def sumFactors : ∀ k : ι ⊕ κ,
    RationalFilteredNilmanifold (sumLieSpace L M k) s (Sum.elim d e k)
  | .inl i => D i
  | .inr j => E j

noncomputable def sumOrbits {w : σ → ℕ}
    (g : ∀ i, (D i).filtration.realification.PolynomialOrbit w)
    (h : ∀ j, (E j).filtration.realification.PolynomialOrbit w) :
    ∀ k : ι ⊕ κ, (sumFactors D E k).filtration.realification.PolynomialOrbit w
  | .inl i => g i
  | .inr j => h j

end RationalFilteredNilmanifold
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RefilteredReconstructionDiagram
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

noncomputable def refilteredReconstructionMap (a : ι)
    (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) :
    let H := (pi D).filtration.gradedRefiltrationSubalgebra W
    H →ₗ⁅ℚ⁆ (H ⧸ ((pi D).filtration.gradedRefiltration W).layerIdeal s) ×
      (∀ i : {i : ι // i ≠ a}, L i.val) :=
  (lieQuotientMap (((pi D).filtration.gradedRefiltration W).layerIdeal s)).prod
    (liePiMap (fun i : {i : ι // i ≠ a} =>
      (liePiEval i.val).comp ((pi D).filtration.gradedRefiltrationSubalgebra W).incl))

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FrozenDiagramKernelInvariance
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem realificationLieHom_injective
    {H M : Type*} [LieRing H] [LieAlgebra ℚ H] [LieRing M] [LieAlgebra ℚ M]
    (ψ : H →ₗ⁅ℚ⁆ M) (hψ : Function.Injective ψ) :
    Function.Injective (realificationLieHom ψ) := by
  let _ : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ) ψ.toLinearMap hψ

namespace NilpotentLieBCHGroup

theorem realificationMap_injective
    {H M : Type*} [LieRing H] [LieAlgebra ℚ H] [LieRing M] [LieAlgebra ℚ M]
    {s t : ℕ} {hH : LieModule.lowerCentralSeries ℚ H H s = ⊥}
    {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}
    (ψ : H →ₗ⁅ℚ⁆ M) (hψ : Function.Injective ψ) :
    Function.Injective (realificationMap (hnil := hH) (hM := hM) ψ) := by
  intro x y hxy
  apply ext
  apply realificationLieHom_injective ψ hψ
  exact congrArg coord hxy

end NilpotentLieBCHGroup

namespace RationalFilteredNilmanifold

open NilpotentLieBCHGroup

theorem frozenDiagramKernelInvariance_of_injective
    {H L M : Type*} [LieRing H] [LieAlgebra ℚ H]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t r d e f : ℕ}
    (D : RationalFilteredNilmanifold H s d)
    (E : RationalFilteredNilmanifold L t e)
    (T : RationalFilteredNilmanifold M r f)
    (φ : H →ₗ⁅ℚ⁆ L) (ψ : H →ₗ⁅ℚ⁆ M) (hψ : Function.Injective ψ)
    (u : E.Space → ℂ) (a b : E.RealGroup) :
    ∀ z ∈ (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := T.filtration.lowerCentralSeries_eq_bot) ψ).ker, ∀ x : D.RealGroup,
      u (QuotientGroup.mk (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ (z * x) * b)) =
      u (QuotientGroup.mk (a * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ x * b)) := by
  intro z hz x
  have hz1 : z = 1 := realificationMap_injective ψ hψ
    ((MonoidHom.mem_ker.mp hz).trans (map_one _).symm)
  rw [hz1, one_mul]

end RationalFilteredNilmanifold

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisFamilyLogHeight
namespace OAI

section

namespace Erdos3

def BasisFamilyLogHeight {ι κ V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Module.Basis ι ℚ V) (v : κ → V) (p : ℝ) : Prop :=
  ∀ i j, rationalLogHeight (b.repr (v i) j) ≤ p

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FormalCurrentDerivativeAdvance
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {μ σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem formal_current_derivative_advance
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V) (j : ℕ)
    (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hAU : ∀ α, coefficients A.coord α ∈ U) (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hA : ∀ α, coefficients A.coord α ∈ F.realification.layer j)
    (hB : ∀ α, coefficients B.coord α ∈ F.realification.layer j)
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsmall : ∀ i α, coefficients (small i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hvanish : ∀ i α, coefficients
        (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
          (dualAdjoint A⁻¹ (small i - formalLogDerivative i A))) α ∈ V ∧
      coefficients (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
          (dualAdjoint B (rational i) - formalLogDerivative i B)) α ∈ V) :
    ∀ i α,
      coefficients (dualAdjoint A⁻¹ (small i - formalLogDerivative i A)) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule ∧
      coefficients (dualAdjoint B (rational i) - formalLogDerivative i B) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  let W := V.restrictScalars ℚ ⊔ F.realification.layer j
  have hWiff (x : ℝ ⊗[ℚ] L) : x ∈ W ↔ x ∈ V ⊔ (F.realLayer j).toSubmodule := by
    change x ∈ V.restrictScalars ℚ ⊔ (F.realLayer j).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  have advance (x : ℝ ⊗[ℚ] L) (hx : x ∈ W)
      (hπ : basisGradeProjection (b.baseChange ℝ) w j x ∈ V) :
      x ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    have hrem := F.real_sub_grade_mem_sup_next b w hlayers V hV j x ((hWiff x).mp hx)
    have h := (V ⊔ (F.realLayer (j + 1)).toSubmodule).add_mem hrem (Submodule.mem_sup_left hπ)
    simpa only [sub_add_cancel] using h
  intro i α
  have hpres := polynomial_derivative_removal_preserves_coefficients U W
    (F.realification.invariant_sup_layer U (V.restrictScalars ℚ) hUV j)
    i A B (small i) (rational i) hAU hBU
    (fun β => Submodule.mem_sup_right (hA β)) (fun β => Submodule.mem_sup_right (hB β))
    (fun β => (hWiff _).mpr (hsmall i β)) (fun β => (hWiff _).mpr (hrational i β))
  have hv := hvanish i α
  simp only [coefficients_map, LinearMap.restrictScalars_apply] at hv
  exact ⟨advance _ (hpres.1 α) hv.1, advance _ (hpres.2 α) hv.2⟩

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledSubspaceCorrectionPolynomials
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped Matrix TensorProduct

variable {L μ ι ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype ι] [Fintype ν] {E V : Submodule ℚ L}

theorem exists_controlled_subspace_correction_polynomials
    (b : Basis μ ℚ L) (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V))
    {H J l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i n, RationalHeightLE (subspaceQuotientMatrix e f i n) H)
    (he : ∀ i j, RationalHeightLE (b.repr (e j : L) i) J)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card ν : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (P small rational : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hPE : ∀ α, coefficients P α ∈ E.baseChange ℝ)
    (hsmall0 : coefficients small 0 = 0) (hrational0 : coefficients rational 0 = 0)
    (hsmall : ∀ α, ‖realQuotientCoordinateMap f (coefficients small α)‖ ≤
      Real.exp p / monomialScale T α)
    (hrational : ∀ α, realQuotientCoordinateMap f (coefficients rational α) ∈
      realDenominatorGrid l)
    (hsplit : ∀ α, coefficients (P - small - rational) α ∈ V.baseChange ℝ) :
    ∃ (m : ℕ) (A B : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      map ((realQuotientCoordinateMap f).restrictScalars ℚ) A =
        map ((realQuotientCoordinateMap f).restrictScalars ℚ) small ∧
      map ((realQuotientCoordinateMap f).restrictScalars ℚ) B =
        map ((realQuotientCoordinateMap f).restrictScalars ℚ) rational ∧
      (∀ α, coefficients A α ∈ E.baseChange ℝ ∧ coefficients B α ∈ E.baseChange ℝ) ∧
      (∀ α, coefficients small α = 0 → coefficients A α = 0) ∧
      (∀ α, coefficients rational α = 0 → coefficients B α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A α)‖ ≤
        (((Fintype.card ν : ℝ) + 1) * (J + 1)) *
          Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B α) ∈
        realDenominatorGrid (matrixDenominator (bracketLiftMatrix b e) * m)) ∧
      ∀ α, coefficients (P - A - B) α ∈ (E ⊓ V).baseChange ℝ := by
  have h := exists_controlled_linear_splitting (subspaceQuotientMatrix e f)
    hH hl hA hp hrows hcols hHp hlp T hT
  obtain ⟨Q, m, hm, hmp, hQ⟩ := h
  let q := realQuotientCoordinateMap f
  let C : (ι → ℝ) →ₗ[ℝ] (ν → ℝ) := Matrix.mulVecLin (fun i j => (Q i j : ℝ))
  let D := (bracketSystemLift e).comp (C.comp q)
  let A := map (D.restrictScalars ℚ) small
  let B := map (D.restrictScalars ℚ) rational
  have hAc (α : σ →₀ ℕ) : coefficients A α =
      bracketSystemLift e (C (q (coefficients small α))) := coefficients_map _ _ _
  have hBc (α : σ →₀ ℕ) : coefficients B α =
      bracketSystemLift e (C (q (coefficients rational α))) := coefficients_map _ _ _
  have hcoeff (α : σ →₀ ℕ) :
      q (bracketSystemLift e (C (q (coefficients small α)))) = q (coefficients small α) ∧
      q (bracketSystemLift e (C (q (coefficients rational α)))) = q (coefficients rational α) ∧
      ‖C (q (coefficients small α))‖ ≤
        Real.exp ((p + 2) ^ 18 + p) / monomialScale T α ∧
      C (q (coefficients rational α)) ∈ realDenominatorGrid m := by
    by_cases hα : α = 0
    · simp only [hα, hsmall0, hrational0, map_zero, norm_zero, monomialScale_zero, div_one]
      exact ⟨True.intro, True.intro, Real.exp_nonneg _, ⟨0, by ext i; simp⟩⟩
    · obtain ⟨v, hv⟩ := exists_subspace_basis_coordinates e _ (hPE α)
      have hz : q (coefficients P α) - q (coefficients small α) -
          q (coefficients rational α) = 0 := by
        have hz := (realQuotientCoordinateMap_eq_zero_iff f _).mpr (hsplit α)
        simpa only [map_sub, Finsupp.sub_apply] using hz
      have heq : (fun i n => (subspaceQuotientMatrix e f i n : ℝ)) *ᵥ v =
          q (coefficients small α) + q (coefficients rational α) := by
        rw [subspaceQuotientMatrix_real_apply, hv]
        exact sub_eq_zero.mp (by simpa only [sub_sub] using hz)
      have hd := hQ α hα (q (coefficients small α)) (q (coefficients rational α)) v
        (hsmall α) (hrational α) heq
      rcases hd with ⟨hleft, hright, hnorm, hgrid, _⟩
      rw [subspaceQuotientMatrix_real_apply] at hleft hright
      exact ⟨hleft, hright, hnorm, hgrid⟩
  refine ⟨m, A, B, hm, hmp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply coefficients.injective
    apply Finsupp.ext
    intro α
    simp only [coefficients_map, LinearMap.restrictScalars_apply, hAc]
    exact (hcoeff α).1
  · apply coefficients.injective
    apply Finsupp.ext
    intro α
    simp only [coefficients_map, LinearMap.restrictScalars_apply, hBc]
    exact (hcoeff α).2.1
  · intro α
    rw [hAc, hBc]
    exact ⟨bracketSystemLift_mem e _, bracketSystemLift_mem e _⟩
  · intro α hα
    rw [hAc, hα, map_zero, map_zero, map_zero]
  · intro α hα
    rw [hBc, hα, map_zero, map_zero, map_zero]
  · intro α
    rw [hAc]
    apply (bracketSystemLift_norm_bound b e he _).trans
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (hcoeff α).2.2.1
      (by positivity : 0 ≤ ((Fintype.card ν : ℝ) + 1) * (J + 1))
  · intro α
    rw [hBc]
    exact bracketSystemLift_grid b e m _ (hcoeff α).2.2.2
  · intro α
    rw [realification_inf]
    refine ⟨?_, ?_⟩
    · simp only [map_sub, Finsupp.sub_apply, hAc, hBc]
      exact (E.baseChange ℝ).sub_mem
        ((E.baseChange ℝ).sub_mem (hPE α) (bracketSystemLift_mem e _))
        (bracketSystemLift_mem e _)
    · apply (realQuotientCoordinateMap_eq_zero_iff f _).mp
      simp only [map_sub, Finsupp.sub_apply, hAc, hBc]
      change q (coefficients P α) - q (bracketSystemLift e (C (q (coefficients small α)))) -
        q (bracketSystemLift e (C (q (coefficients rational α)))) = 0
      rw [(hcoeff α).1, (hcoeff α).2.1]
      have hz := (realQuotientCoordinateMap_eq_zero_iff f _).mpr (hsplit α)
      simpa only [map_sub, Finsupp.sub_apply] using hz

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FormalKernelAbsorption
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace VectorPolynomial

theorem homogeneous_one_pderiv {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (P : VectorPolynomial σ ℚ L)
    (hP : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ 1 → coefficients P α = 0)
    (i : σ) :
    (MvPolynomial.pderiv i).toLinearMap.rTensor L P = monomial 0 (coefficients P (Finsupp.single i 1)) := by
  classical
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [coefficients_pderiv, coefficients_monomial]
  by_cases hα : α = 0
  · subst α
    simp only [Finsupp.zero_apply, Nat.cast_zero, zero_add, one_smul, Finsupp.single_eq_same]
  · have hp := NilpotentLieFiltration.positive_weight_of_ne_zero (fun _ : σ => 1) (by simp) hα
    have hweight : Finsupp.weight (fun _ : σ => (1 : ℕ)) (α + Finsupp.single i 1) ≠ 1 := by
      rw [map_add, Finsupp.weight_single]
      simp only [one_smul]
      omega
    rw [hP _ hweight, smul_zero, Finsupp.single_eq_of_ne hα]

end VectorPolynomial

namespace NilpotentLieBCHGroup

variable {σ K L : Type*} [AddCommGroup K] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem PolynomialDerivativeSystemMod.absorb (V : Submodule ℚ L)
    (P : PolynomialGroup σ hnil) (S R : K →+ VectorPolynomial σ ℚ L)
    (small rational : σ → VectorPolynomial σ ℚ L) (k a b : σ → K)
    (hSR : PolynomialLiftSystemMod V P S R)
    (hsystem : PolynomialDerivativeSystemMod V P small rational (fun i => S (k i))) :
    PolynomialDerivativeSystemMod V P
      (fun i => small i + S (a i)) (fun i => rational i + R (b i))
      (fun i => S (k i - a i - b i)) := by
  intro i
  have h := (coefficientSubmodule V).add_mem (hsystem i) (hSR (b i))
  change formalLogDerivative i P -
    ((small i + S (a i)) + dualAdjoint P (rational i + R (b i)) + S (k i - a i - b i)) ∈ _
  convert h using 1
  simp only [map_sub, dualAdjoint_add]
  abel

theorem formal_remove_and_absorb (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (P A B : PolynomialGroup σ hnil) (hA : ∀ α, coefficients A.coord α ∈ U)
    (S R : K →+ VectorPolynomial σ ℚ L)
    (small rational : σ → VectorPolynomial σ ℚ L) (k a b : σ → K)
    (hSR : PolynomialLiftSystemMod V P S R)
    (hsystem : PolynomialDerivativeSystemMod V P small rational (fun i => S (k i))) :
    let S' := (dualAdjointAddEquiv A⁻¹).toAddMonoidHom.comp S
    let R' := (dualAdjointAddEquiv B).toAddMonoidHom.comp R
    PolynomialLiftSystemMod V (A⁻¹ * P * B⁻¹) S' R' ∧
      PolynomialDerivativeSystemMod V (A⁻¹ * P * B⁻¹)
        (fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A) + S' (a i))
        (fun i => dualAdjoint B (rational i) - formalLogDerivative i B + R' (b i))
        (fun i => S' (k i - a i - b i)) := by
  intro S' R'
  have hlifts : PolynomialLiftSystemMod V (A⁻¹ * P * B⁻¹) S' R' :=
    PolynomialLiftSystemMod.remove U V hUV P A B hA S R hSR
  have hderivative := PolynomialDerivativeSystemMod.remove U V hUV P A B hA
    small rational (fun i => S (k i)) hsystem
  exact ⟨hlifts, PolynomialDerivativeSystemMod.absorb V (A⁻¹ * P * B⁻¹) S' R'
    _ _ k a b hlifts hderivative⟩

end NilpotentLieBCHGroup
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FormalHorizontalReabsorption
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {μ σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hF in
theorem formal_horizontal_logDerivative (hs : 1 ≤ s) (i : σ)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot) :
    VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ) (formalLogDerivative i P) =
      VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
        ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord) := by
  have hP : ∀ α, coefficients P.coord α ∈ F.realification.layer 1 := by
    intro α
    rw [F.realification.one_eq_top]
    trivial
  have hD := pderiv_mem_submodule (F.realification.layer 1) P.coord hP i
  have hrem := F.realification.polynomialFiltration.dualLogDerivative_sub_tangent_mem_layer hs
    (i := 1) (j := 1) (formalPolynomialJetHom i P)
    (by rw [formalPolynomialJet_base]; exact hP)
    (by rw [formalPolynomialJet_tangent]; exact hD)
  rw [formalPolynomialJet_tangent] at hrem
  exact F.polynomial_grade_eq_of_sub_mem_next b w hF 1 _ _ hrem

include hF in
theorem formal_derivative_horizontal_balance (hs : 2 ≤ s)
    (V : Submodule ℝ (ℝ ⊗[ℚ] L)) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (small rational extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsystem : PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P small rational extra)
    (hsmall : ∀ i α, coefficients (small i) α ∈ V ⊔ (F.realLayer 2).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer 2).toSubmodule) :
    ∀ i α, coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
          ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord) -
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ) (extra i)) α ∈ V := by
  intro i α
  have hP : ∀ β, coefficients P.coord β ∈ F.realification.layer 1 := by
    intro β
    rw [F.realification.one_eq_top]
    trivial
  have hY := congrArg (fun Q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) => coefficients Q α)
    (F.formal_horizontal_logDerivative b w hF (by omega) i P)
  have hAd := congrArg (fun Q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) => coefficients Q α)
    (F.polynomial_grade_adjoint_eq b w hF hs 1 P hP (rational i))
  simp only [coefficients_map, LinearMap.restrictScalars_apply] at hY hAd
  have herr := hV 1 _ (hsystem i α)
  simp only [map_sub, map_add, Finsupp.sub_apply, Finsupp.add_apply] at herr
  rw [hY, hAd] at herr
  have hS := F.realGradeProjection_mem_of_mem_sup_next b w hF V hV 1 _ (hsmall i α)
  have hR := F.realGradeProjection_mem_of_mem_sup_next b w hF V hV 1 _ (hrational i α)
  have h := V.add_mem herr (V.add_mem hS hR)
  simp only [map_sub, Finsupp.sub_apply, coefficients_map, LinearMap.restrictScalars_apply]
  convert h using 1
  abel

include hF in
theorem formal_extra_horizontal_equation (hs : 2 ≤ s)
    (V : Submodule ℝ (ℝ ⊗[ℚ] L)) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V) (j : ℕ)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (small rational extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsystem : PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P small rational extra)
    (hsmall : ∀ i α, coefficients (small i) α ∈ V ⊔ (F.realLayer 2).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer 2).toSubmodule)
    (hextra : ∀ i α, coefficients (extra i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ) (extra i)) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    ∀ i α, coefficients (extra i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord)) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  intro i α
  have hbalance := F.formal_derivative_horizontal_balance b w hF hs V hV P small rational extra
    hsystem hsmall hrational i α
  have h := (V ⊔ (F.realLayer (j + 1)).toSubmodule).sub_mem (hextra i α) (Submodule.mem_sup_left hbalance)
  simp only [map_sub, Finsupp.sub_apply] at h ⊢
  convert h using 1
  abel

include hF in
theorem formal_lift_nonhorizontal_remainder
    (V : Submodule ℝ (ℝ ⊗[ℚ] L)) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    {j : ℕ} (hj : 1 ≤ j) (X : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k : ℝ ⊗[ℚ] L)
    (hk : basisGradeProjection (b.baseChange ℝ) w 1 k = k)
    (hX : ∀ α, coefficients (X - monomial 0 k) α ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    ∀ α, coefficients (X - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ) X) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  have hproj (x : ℝ ⊗[ℚ] L) (hx : x ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule) :
      basisGradeProjection (b.baseChange ℝ) w 1 x ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    obtain ⟨v, hv, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, F.realGradeProjection_eq_zero_of_mem_next_layer b w hF 1 z
      (F.realification.antitone (by omega) hz), add_zero]
    exact Submodule.mem_sup_left (hV 1 v hv)
  intro α
  have hkα : basisGradeProjection (b.baseChange ℝ) w 1 (coefficients (monomial 0 k : VectorPolynomial σ ℚ _) α) =
      coefficients (monomial 0 k : VectorPolynomial σ ℚ _) α := by
    rw [coefficients_monomial]
    by_cases hα : α = 0
    · subst α
      simpa only [Finsupp.single_eq_same] using hk
    · rw [Finsupp.single_eq_of_ne hα, map_zero]
  have h := (V ⊔ (F.realLayer (j + 1)).toSubmodule).sub_mem (hX α) (hproj _ (hX α))
  simp only [map_sub, Finsupp.sub_apply, hkα] at h
  simp only [map_sub, Finsupp.sub_apply, coefficients_map, LinearMap.restrictScalars_apply]
  convert h using 1
  abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

section General

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem formal_logDerivative_sub_pderiv_mem_two (hs : 1 ≤ s) (i : σ)
    (A : PolynomialGroup σ F.lowerCentralSeries_eq_bot) :
    ∀ α, coefficients (formalLogDerivative i A - (MvPolynomial.pderiv i).toLinearMap.rTensor L A.coord) α ∈ F.layer 2 := by
  have hA : ∀ α, coefficients A.coord α ∈ F.layer 1 := by intro α; rw [F.one_eq_top]; trivial
  have hD := pderiv_mem_submodule (F.layer 1) A.coord hA i
  have h := F.polynomialFiltration.dualLogDerivative_sub_tangent_mem_layer hs
    (i := 1) (j := 1) (formalPolynomialJetHom i A)
    (by rw [formalPolynomialJet_base]; exact hA) (by rw [formalPolynomialJet_tangent]; exact hD)
  rw [formalPolynomialJet_tangent] at h
  exact h

theorem formal_reabsorption_preserves_layer_two (hs : 2 ≤ s) (V : Submodule ℚ L) (i : σ)
    (A B : PolynomialGroup σ F.lowerCentralSeries_eq_bot)
    (small rational left right : VectorPolynomial σ ℚ L)
    (hsmall : ∀ α, coefficients small α ∈ V ⊔ F.layer 2)
    (hrational : ∀ α, coefficients rational α ∈ V ⊔ F.layer 2)
    (hleft : ∀ α, coefficients (left - (MvPolynomial.pderiv i).toLinearMap.rTensor L A.coord) α ∈ V ⊔ F.layer 2)
    (hright : ∀ α, coefficients (right - (MvPolynomial.pderiv i).toLinearMap.rTensor L B.coord) α ∈ V ⊔ F.layer 2) :
    (∀ α, coefficients (dualAdjoint A⁻¹ (small - formalLogDerivative i A) + left) α ∈ V ⊔ F.layer 2) ∧
      ∀ α, coefficients (dualAdjoint B rational - formalLogDerivative i B + right) α ∈ V ⊔ F.layer 2 := by
  let W := coefficientSubmodule (σ := σ) (V ⊔ F.layer 2)
  have hA : ∀ α, coefficients A⁻¹.coord α ∈ F.layer 1 := by intro α; rw [F.one_eq_top]; trivial
  have hB : ∀ α, coefficients B.coord α ∈ F.layer 1 := by intro α; rw [F.one_eq_top]; trivial
  have ha := F.polynomialFiltration.adjoint_correction_sub_mem_layer hs 1 A⁻¹ hA (small - formalLogDerivative i A)
  have hb := F.polynomialFiltration.adjoint_correction_sub_mem_layer hs 1 B hB rational
  have hYa := F.formal_logDerivative_sub_pderiv_mem_two (by omega) i A
  have hYb := F.formal_logDerivative_sub_pderiv_mem_two (by omega) i B
  have haW : dualAdjoint A⁻¹ (small - formalLogDerivative i A) - (small - formalLogDerivative i A) ∈ W :=
    fun α => Submodule.mem_sup_right (ha α)
  have hbW : dualAdjoint B rational - rational ∈ W := fun α => Submodule.mem_sup_right (hb α)
  have hYaW : formalLogDerivative i A - (MvPolynomial.pderiv i).toLinearMap.rTensor L A.coord ∈ W :=
    fun α => Submodule.mem_sup_right (hYa α)
  have hYbW : formalLogDerivative i B - (MvPolynomial.pderiv i).toLinearMap.rTensor L B.coord ∈ W :=
    fun α => Submodule.mem_sup_right (hYb α)
  constructor
  · have h : dualAdjoint A⁻¹ (small - formalLogDerivative i A) + left ∈ W := by
      convert W.add_mem (W.sub_mem (W.add_mem hsmall haW) hYaW) hleft using 1
      abel
    exact h
  · have h : dualAdjoint B rational - formalLogDerivative i B + right ∈ W := by
      convert W.add_mem (W.sub_mem (W.add_mem hrational hbW) hYbW) hright using 1
      abel
    exact h

end General

variable {μ σ K L : Type*} [AddCommGroup K] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hF in
theorem formal_degree_two_reabsorption (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (I : K →+ ℝ ⊗[ℚ] L) (hI : ∀ x, basisGradeProjection (b.baseChange ℝ) w 1 (I x) = I x)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hAU : ∀ α, coefficients A.coord α ∈ U)
    (hAhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ 1 → coefficients A.coord α = 0)
    (hBhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ 1 → coefficients B.coord α = 0)
    (S R : K →+ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k a c : σ → K)
    (ha : ∀ i, I (a i) = coefficients A.coord (Finsupp.single i 1))
    (hc : ∀ i, I (c i) = coefficients B.coord (Finsupp.single i 1))
    (hSR : PolynomialLiftSystemMod (V.restrictScalars ℚ) P S R)
    (hsystem : PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P small rational (fun i => S (k i)))
    (hsmall : ∀ i α, coefficients (small i) α ∈ V ⊔ (F.realLayer 2).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer 2).toSubmodule)
    (hS : ∀ x α, coefficients (dualAdjoint A⁻¹ (S x) - monomial 0 (I x)) α ∈ V ⊔ (F.realLayer 3).toSubmodule)
    (hR : ∀ x α, coefficients (dualAdjoint B (R x) - monomial 0 (I x)) α ∈ V ⊔ (F.realLayer 3).toSubmodule) :
    let P' := A⁻¹ * P * B⁻¹
    let S' := (dualAdjointAddEquiv A⁻¹).toAddMonoidHom.comp S
    let R' := (dualAdjointAddEquiv B).toAddMonoidHom.comp R
    let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A) + S' (a i)
    let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B + R' (c i)
    let extra' := fun i => S' (k i - a i - c i)
    PolynomialLiftSystemMod (V.restrictScalars ℚ) P' S' R' ∧
      PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P' small' rational' extra' ∧
      (∀ i α, coefficients (small' i) α ∈ V ⊔ (F.realLayer 2).toSubmodule ∧
        coefficients (rational' i) α ∈ V ⊔ (F.realLayer 2).toSubmodule) ∧
      ∀ i α, coefficients (extra' i - VectorPolynomial.map
        ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
        ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P'.coord)) α ∈ V ⊔ (F.realLayer 3).toSubmodule := by
  intro P' S' R' small' rational' extra'
  have hsystem' := formal_remove_and_absorb U (V.restrictScalars ℚ) hUV P A B hAU S R
    small rational k a c hSR hsystem
  have hWiff (d : ℕ) (x : ℝ ⊗[ℚ] L) :
      x ∈ V.restrictScalars ℚ ⊔ F.realification.layer d ↔ x ∈ V ⊔ (F.realLayer d).toSubmodule := by
    change x ∈ V.restrictScalars ℚ ⊔ (F.realLayer d).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  have h32 : V.restrictScalars ℚ ⊔ F.realification.layer 3 ≤ V.restrictScalars ℚ ⊔ F.realification.layer 2 :=
    sup_le_sup_left (F.realification.antitone (by decide : 2 ≤ 3)) _
  have hlow (i : σ) := F.realification.formal_reabsorption_preserves_layer_two hs (V.restrictScalars ℚ) i A B
    (small i) (rational i) (S' (a i)) (R' (c i))
    (fun α => (hWiff 2 _).mpr (hsmall i α)) (fun α => (hWiff 2 _).mpr (hrational i α))
    (fun α => by
      rw [homogeneous_one_pderiv A.coord hAhom i, ← ha i]
      exact h32 ((hWiff 3 _).mpr (hS (a i) α)))
    (fun α => by
      rw [homogeneous_one_pderiv B.coord hBhom i, ← hc i]
      exact h32 ((hWiff 3 _).mpr (hR (c i) α)))
  have hsmall' : ∀ i α, coefficients (small' i) α ∈ V ⊔ (F.realLayer 2).toSubmodule :=
    fun i α => (hWiff 2 _).mp ((hlow i).1 α)
  have hrational' : ∀ i α, coefficients (rational' i) α ∈ V ⊔ (F.realLayer 2).toSubmodule :=
    fun i α => (hWiff 2 _).mp ((hlow i).2 α)
  refine ⟨hsystem'.1, hsystem'.2, (fun i α => ⟨hsmall' i α, hrational' i α⟩), ?_⟩
  apply F.formal_extra_horizontal_equation b w hF hs V hV 2 P' small' rational' extra'
    hsystem'.2 hsmall' hrational'
  intro i
  exact F.formal_lift_nonhorizontal_remainder b w hF V hV (by decide : 1 ≤ 2)
    (extra' i) (I (k i - a i - c i)) (hI _) (hS _)

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LayerOneTransportBudget
namespace OAI

section

namespace Erdos3

theorem layerOne_basis_transport_height_le_exp (a m J : ℕ) (C p : ℝ)
    (hp : 0 ≤ p) (ha : (a : ℝ) ≤ p) (hm : (m : ℝ) ≤ Real.exp p)
    (hC0 : 0 ≤ C) (hC : C ≤ Real.exp p) (hJ : (J : ℝ) ≤ Real.exp p) :
    (((a + 1) * (max m (Nat.ceil ((m : ℝ) * C)) * J) ^ a : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 3) := by
  have hprod : (m : ℝ) * C ≤ Real.exp (2 * p) := by
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hm hC hC0 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hheight : ((max m (Nat.ceil ((m : ℝ) * C)) : ℕ) : ℝ) ≤ Real.exp (2 * p + 1) := by
    rw [Nat.cast_max]
    apply max_le
    · exact hm.trans (Real.exp_le_exp.mpr (by linarith))
    · calc
        _ ≤ (Nat.ceil (Real.exp (2 * p)) : ℝ) := Nat.cast_le.mpr (Nat.ceil_mono hprod)
        _ ≤ _ := ceil_exp_le_exp_add_one (by positivity)
  have hHJ : ((max m (Nat.ceil ((m : ℝ) * C)) : ℕ) : ℝ) * J ≤ Real.exp (3 * p + 1) := by
    calc
      _ ≤ Real.exp (2 * p + 1) * Real.exp p :=
        mul_le_mul hheight hJ (Nat.cast_nonneg J) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hpow := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg J)) hHJ a
  rw [← Real.exp_nat_mul] at hpow
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_mul]
  calc
    _ ≤ Real.exp a * Real.exp ((a : ℝ) * (3 * p + 1)) :=
      mul_le_mul (Real.add_one_le_exp a) hpow (by positivity) (Real.exp_nonneg _)
    _ = Real.exp ((a : ℝ) * (3 * p + 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (p * (3 * p + 2)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha (by positivity))
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hp (sq_nonneg p)])

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ControlledIntegralGrid
namespace OAI

section

namespace Erdos3

open Module

theorem exists_controlled_integral_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (L ι : Type*) [LieRing L] [LieAlgebra ℚ L] [Fintype ι]
      (e : Basis ι ℚ L) (_hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (l : ℕ), 0 < l → ∀ (p : ℝ), 0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
      (l : ℝ) ≤ Real.exp p →
      (∀ i j k, rationalLogHeight (lieStructureConstants e i j k) ≤ p) →
      p ≤ (p + C) ^ C ∧ ∃ B : ℕ, 0 < B ∧ l ∣ B ∧ (B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ x ∈ coordinateGridModule e B, ∀ y ∈ coordinateGridModule e B,
          lieBCH s x y ∈ coordinateGridModule e B := by
  let K := bchIntegralDenominatorBound s
  let Q : Polynomial ℕ := Polynomial.C K + (Polynomial.X + 1) * Polynomial.X ^ 3 + Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + Polynomial.X)
  refine ⟨C, hC, ?_⟩
  intro L ι _ _ _ e hnil l hl p hp hd hlp hc
  let H := ⌈Real.exp p⌉₊
  let E := (K : ℝ) + (p + 1) * p ^ 3 + p
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have htotal : E + p ≤ (p + C) ^ C := by
    simpa [Q, E, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p ≤ (p + C) ^ C := (le_add_of_nonneg_left hE).trans htotal
  have hEC : E ≤ (p + C) ^ C := (le_add_of_nonneg_right hp).trans htotal
  have hH : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hn3 : ((Fintype.card ι ^ 3 : ℕ) : ℝ) ≤ p ^ 3 := by
    rw [Nat.cast_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hd _
  have hHpow : (H : ℝ) ^ (Fintype.card ι ^ 3) ≤ Real.exp ((p + 1) * p ^ 3) := by
    apply (pow_le_pow_left₀ (Nat.cast_nonneg H) hH _).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_right hn3 (by linarith)).trans_eq (mul_comm _ _)
  have hK : (K : ℝ) ≤ Real.exp (K : ℝ) :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  obtain ⟨B, hB, hdiv, hbound, hstable⟩ := exists_bch_stable_integral_grid e hnil l hl
    (fun i j k => rationalHeightLE_ceil_exp (hc i j k))
  have hBexp : (B : ℝ) ≤ Real.exp E := by
    calc
      _ ≤ (K : ℝ) * (H : ℝ) ^ (Fintype.card ι ^ 3) * (l : ℝ) := by exact_mod_cast hbound
      _ ≤ Real.exp (K : ℝ) * Real.exp ((p + 1) * p ^ 3) * Real.exp p :=
        mul_le_mul (mul_le_mul hK hHpow (by positivity) (Real.exp_nonneg _)) hlp
          (Nat.cast_nonneg l) (by positivity)
      _ = Real.exp E := by rw [← Real.exp_add, ← Real.exp_add]
  exact ⟨hpC, B, hB, hdiv, hBexp.trans (Real.exp_le_exp.mpr hEC), hstable⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.UnitComparisonNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  (T U : D.Niltest w) (hT : ∀ x, ‖T.observable x‖ ≤ 1)
  (hU : ∀ x, ‖U.observable x‖ ≤ 1)

noncomputable def unitComparison : D.Niltest w where
  orbit := T.orbit
  observable x := T.observable x * star (U.observable x)
  normBound := 1
  lipBound := U.lipBound + T.lipBound
  norm_le x := by
    change ‖T.observable x * star (U.observable x)‖ ≤ (1 : ℝ)
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hT x)).trans (hU x)
  lipschitz := by
    let := D.metricSpace
    simpa only [one_mul] using lipschitz_mul_star_of_bounds T.observable U.observable
      (Bf := 1) (Bg := 1) T.lipschitz U.lipschitz hT hU

theorem unitComparison_complexity {p : ℝ}
    (hTc : T.ComplexityLE p) (hUc : U.ComplexityLE p) :
    (T.unitComparison U hT hU).ComplexityLE (p + 4) := by
  refine ⟨hTc.1.mono D (by linarith), ?_⟩
  change Real.log (2 + 1 + ((U.lipBound + T.lipBound : ℝ≥0) : ℝ)) ≤ p + 4
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  have hT' := T.observable_budget hTc
  have hU' := U.observable_budget hUc
  calc
    _ ≤ 5 * Real.exp p := by
      simp only [NNReal.coe_add]
      linarith [T.normBound.coe_nonneg, U.normBound.coe_nonneg, Real.exp_nonneg p]
    _ ≤ Real.exp 4 * Real.exp p := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (p + 4) := by rw [← Real.exp_add, add_comm]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ProductPolynomialMaps
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct

namespace NilpotentLieFiltration

theorem piRealOrbit_projection_log {ι σ : Type*} [Fintype ι]
    {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
    (F : ∀ i, NilpotentLieFiltration (L i) s) {w : σ → ℕ}
    (g : ∀ i, (F i).realification.PolynomialOrbit w) (a : ι) :
    VectorPolynomial.map ((realificationLieHom (liePiEval a)).toLinearMap.restrictScalars ℚ)
      (piRealOrbit F g).log = (g a).log := by
  classical
  apply coefficients.injective
  ext α
  simp only [coefficients_map, piRealOrbit, polynomialOrbitOfLog_log, map_sum,
    Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single a]
  · exact realProductSingle_projection a _
  · intro j _ hja
    exact realProductSingle_projection_ne (Ne.symm hja) _
  · simp

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (f : κ → ι)

noncomputable def productRestrictionIndex
    (k : Fin (Fintype.card (Σ j : κ, Fin (d (f j))))) :
    Fin (Fintype.card (Σ i, Fin (d i))) :=
  let z := (Fintype.equivFin (Σ j : κ, Fin (d (f j)))).symm k
  Fintype.equivFin (Σ i, Fin (d i)) ⟨f z.1, z.2⟩

end RationalFilteredNilmanifold
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubicPairPartitionPrecision
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold

end Erdos3

end

section

namespace Erdos3.NativePolynomialOrbitFactors

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

variable {p q r : ℝ}
  {N : ℕ}
  [NeZero N]
  {shift : ℤ}

end Erdos3.NativePolynomialOrbitFactors

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ}
  {N : ℕ}
  [NeZero N]
  {shift : ℤ}

end NativePolynomialOrbitFactors

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

namespace NativePolynomialOrbitFactors.FrozenMiddleRealization

variable {p q r b : ℝ}
  {N : ℕ}
  [NeZero N]
  {shift : ℤ}

end NativePolynomialOrbitFactors.FrozenMiddleRealization

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

theorem norm_sub_positive_sum_le_weighted {I : Type*} [Fintype I]
    (w : I → ℝ) (c : I → ℂ) (t : ℂ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    ‖t - ∑ i, (w i : ℂ) * c i‖ ≤ ∑ i, w i * ‖t - c i‖ := by
  have hsumC : (∑ i, (w i : ℂ)) = 1 := by exact_mod_cast hsum
  have hid : t - ∑ i, (w i : ℂ) * c i = ∑ i, (w i : ℂ) * (t - c i) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsumC, one_mul]
  rw [hid]
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]

theorem weighted_partition_mean_error {I X : Type*}
    [Fintype I] [Fintype X] [Nonempty X]
    (E : Finset X) (w : I → X → ℝ) (c : I → X → ℂ) (T : X → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε) (hw : ∀ i x, 0 ≤ w i x)
    (hsum : ∀ x, ∑ i, w i x = 1) (hc : ∀ i x, ‖c i x‖ ≤ 1)
    (hT : ∀ x, ‖T x‖ ≤ 1)
    (hgood : ∀ i x, x ∉ E → 0 < w i x → ‖T x - c i x‖ ≤ ε) :
    (𝔼 x, ∑ i, w i x * ‖T x - c i x‖) ≤ ε + 2 * (E.card : ℝ) / Fintype.card X := by
  have hn (x : X) : 0 ≤ ∑ i, w i x * ‖T x - c i x‖ :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i x) (norm_nonneg _))
  have hb (x : X) (d : ℝ) (h : ∀ i, 0 < w i x → ‖T x - c i x‖ ≤ d) :
      (∑ i, w i x * ‖T x - c i x‖) ≤ d := by
    calc
      _ ≤ ∑ i, w i x * d := by
        apply Finset.sum_le_sum
        intro i _
        rcases (hw i x).eq_or_lt with hi | hi
        · rw [← hi, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (h i hi) (hw i x)
      _ = d := by rw [← Finset.sum_mul, hsum, one_mul]
  have ha (x : X) : |∑ i, w i x * ‖T x - c i x‖| = ∑ i, w i x * ‖T x - c i x‖ :=
    abs_of_nonneg (hn x)
  have herr := expect_abs_le_of_exceptional_set E
    (fun x => ∑ i, w i x * ‖T x - c i x‖) hε
    (fun x => by
      rw [ha]
      exact hb x 2 (fun i _ => (norm_sub_le _ _).trans (by linarith [hT x, hc i x])))
    (fun x hx => by rw [ha]; exact hb x ε (fun i hi => hgood i x hx hi))
  simpa only [ha] using herr

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ}
  {N : ℕ}
  [NeZero N]
  {shift : ℤ}

end NativePolynomialOrbitFactors

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

section Data

variable {p q r : ℝ}
  {N : ℕ}
  [NeZero N]
  {shift : ℤ}

end Data

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicProductDetection
namespace OAI

section

open scoped TensorProduct BigOperators

namespace Erdos3

def CyclicProductNiltestDetection.{u,v} (s : ℕ) (F : ℝ → ℝ) : Prop :=
  ∀ {ι : Type v} [Fintype ι] {L : ι → Type u}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (p : ℝ),
    0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
    ∀ (w : Fin 1 → ℕ), (∀ j, 0 < w j) →
    ∀ (T : ∀ i, (D i).Niltest w), (∀ i, (T i).ComplexityLE p) →
    ∀ (N : ℕ) [NeZero N] (h : ι → ZMod N) (f : ZMod N → ℂ),
    (∀ x, ‖f x‖ ≤ 1) →
    Real.exp (-p) ≤ ‖finiteCorrelation Finset.univ f
      (translatedCyclicProduct h (fun i n => (T i).eval (fun _ => n)))‖ →
    Real.exp (-F p) ≤ gowersNorm (s + 1) f

end Erdos3

end

section

open scoped TensorProduct BigOperators

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveShiftTestingGowers
namespace OAI

section

namespace Erdos3

def shiftDetectionLoss (s C : ℕ) (p : ℝ) : ℝ :=
  6 * p + (2 ^ (s + 1) : ℕ) * (6 * p + C) ^ C

noncomputable def shiftDetectionPolynomial (s C : ℕ) : Polynomial ℕ :=
  Polynomial.C 6 * Polynomial.X + Polynomial.C (2 ^ (s + 1)) *
    (Polynomial.C 6 * Polynomial.X + Polynomial.C C) ^ C

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

def CyclicShiftTestingDetection.{u,v} (s : ℕ) (F : ℝ → ℝ) : Prop :=
  ∀ {ι : Type v} [Nonempty ι] {L : ι → Type u}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (p : ℝ),
    2 ≤ p → ∀ (w : Fin 1 → ℕ), (∀ j, 0 < w j) →
    ∀ (T : ∀ i, (D i).Niltest w), (∀ i, (T i).ComplexityLE p) →
    ∀ (N : ℕ) [NeZero N], (∀ i (x : ZMod N), ‖(T i).eval (fun _ => (x.val : ℤ))‖ ≤ 1) →
    ∀ (v B : ZMod N → ℂ), (∀ x, ‖v x‖ ≤ 1) → (∀ x, ‖B x‖ ≤ Real.exp p) →
    Real.exp (-p) ≤ shiftTestingSeminorm B (fun i x => (T i).eval (fun _ => (x.val : ℤ))) v →
    Real.exp (-F p) ≤ gowersNorm (s + 2) v

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

def CyclicTranslatedShiftTestingDetection.{u,v} (s : ℕ) (F : ℝ → ℝ) : Prop :=
  ∀ {ι : Type v} [Nonempty ι] {L : ι → Type u}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (p : ℝ),
    2 ≤ p → ∀ (w : Fin 1 → ℕ), (∀ j, 0 < w j) →
    ∀ (T : ∀ i, (D i).Niltest w), (∀ i, (T i).ComplexityLE p) →
    ∀ (N : ℕ) [NeZero N], (∀ i (x : ZMod N), ‖(T i).eval (fun _ => (x.val : ℤ))‖ ≤ 1) →
    ∀ (v B : ZMod N → ℂ), (∀ x, ‖v x‖ ≤ 1) → (∀ x, ‖B x‖ ≤ Real.exp p) →
    Real.exp (-p) ≤ shiftTestingSeminorm B
      (translatedTestFamily (fun i x => (T i).eval (fun _ => (x.val : ℤ)))) v →
    Real.exp (-F p) ≤ gowersNorm (s + 2) v

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u

namespace PositiveShiftBasis

end PositiveShiftBasis
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedResidueInterpolationMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

noncomputable def principalSupportedCoordinateWeights (t : PrincipalTupleIndex B h) :
    FiniteProbabilityWeights (IntegerScalarCubeBox α (L t)) :=
  (integerScalarCubeWeights α (L t) (hL t)).condition
    (Finset.univ.filter (fun z => (fun i => ((z i : ℤ) : ZMod q)) = r t))
    (FiniteProbabilityWeights.coordinate_fiber_mass_pos
      (fun t => integerScalarCubeWeights α (L t) (hL t))
      (fun t (z : IntegerScalarCubeBox α (L t)) i => ((z i : ℤ) : ZMod q)) r hcell t)

local notation "coord" => principalSupportedCoordinateWeights B h L hL q r hcell
local notation "conditioned" => FiniteProbabilityWeights.condition
  (principalTupleWeights B h L hL)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

noncomputable def principalSupportedAxisTuplePMF (a : D) :
    PMF (∀ b : B a, ∀ v : Fin (h a), IntegerScalarCubeBox α (L ⟨a, b, v⟩)) :=
  dependentProductPMF (fun b => dependentProductPMF (fun v => ((coord) ⟨a, b, v⟩).toPMF))

end Erdos3

end

section

namespace Erdos3

open scoped Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (a : D) (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ L ⟨a, b, v⟩)

noncomputable def principalSupportedAxisSources (b : B a) (v : Fin (h a)) :
    NormalizedScalarCubeSource α :=
  normalizedUniformCubeSource α (L ⟨a, b, v⟩) q (hL ⟨a, b, v⟩) (fun _ => q) (r ⟨a, b, v⟩)
    (fun _ => hq) (fun _ => le_rfl) (hsize b v)

local notation "sources" => principalSupportedAxisSources B h L hL q hq r a hsize

variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "conditioned" => FiniteProbabilityWeights.condition (principalTupleWeights (α := α) B h L hL)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j))
variable (q : ℕ) (hq : 0 < q)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ}
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j))
variable (q : ℕ) (hq : 0 < q)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ)
variable (j : Fin m) (i : Fin (n j))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ)
variable (j : Fin m) (i : Fin (n j))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealFunctionalBCH
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem realifyFunctional_lie_eq_zero (η : L →ₗ[ℚ] ℚ)
    (hη : ∀ x y : L, η ⁅x, y⁆ = 0) (x y : ℝ ⊗[ℚ] L) :
    realifyFunctional η ⁅x, y⁆ = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b y =>
      simp only [LieAlgebra.ExtendScalars.bracket_tmul, realifyFunctional_tmul,
        hη, Rat.cast_zero, mul_zero]
    | add y z hy hz => simp only [LieRing.lie_add, map_add, hy, hz, add_zero]
  | add x z hx hz => simp only [LieRing.add_lie, map_add, hx, hz, add_zero]

attribute [local instance] LieRing.ofAssociativeRing

noncomputable def realifyFunctionalLie (η : L →ₗ[ℚ] ℚ)
    (hη : ∀ x y : L, η ⁅x, y⁆ = 0) : (ℝ ⊗[ℚ] L) →ₗ⁅ℚ⁆ ℝ where
  toLinearMap := (realifyFunctional η).restrictScalars ℚ
  map_lie' {x y} := by
    change realifyFunctional η ⁅x, y⁆ = ⁅realifyFunctional η x, realifyFunctional η y⁆
    rw [realifyFunctional_lie_eq_zero η hη]
    simp only [Ring.lie_def, mul_comm, sub_self]

theorem realifyFunctional_lieBCH (η : L →ₗ[ℚ] ℚ)
    (hη : ∀ x y : L, η ⁅x, y⁆ = 0) {s : ℕ} (hs : 1 ≤ s)
    (x y : ℝ ⊗[ℚ] L) :
    realifyFunctional η (lieBCH s x y) = realifyFunctional η x + realifyFunctional η y := by
  change realifyFunctionalLie η hη (lieBCH s x y) = _
  rw [map_lieBCH, lieBCH_eq_add_of_lie_eq_zero_pos hs
    (by simp only [Ring.lie_def, mul_comm, sub_self])]
  rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTagProjectionComplement
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {T : Type*} [Fintype T]

noncomputable def rationalTagProjectionComplement (P : Matrix T T ℚ) :
    (T → ℝ) →ₗ[ℝ] (T → ℝ) :=
  LinearMap.id - Matrix.mulVecLin (fun i j => (P i j : ℝ))

@[simp] theorem rationalTagProjectionComplement_apply (P : Matrix T T ℚ) (x : T → ℝ) :
    rationalTagProjectionComplement P x = x - (fun i j => (P i j : ℝ)) *ᵥ x := rfl

theorem rationalTagProjectionComplement_ker
    (P : Matrix T T ℚ) (V : Submodule ℚ (T → ℚ))
    (hrange : LinearMap.range (Matrix.mulVecLin (fun i j => (P i j : ℝ))) =
      realRationalCoordinateSpan V)
    (hfix : ∀ x ∈ realRationalCoordinateSpan V,
      Matrix.mulVecLin (fun i j => (P i j : ℝ)) x = x) :
    LinearMap.ker (rationalTagProjectionComplement P) = realRationalCoordinateSpan V := by
  ext x
  change x - Matrix.mulVecLin (fun i j => (P i j : ℝ)) x = 0 ↔
    x ∈ realRationalCoordinateSpan V
  constructor
  · intro hx
    rw [sub_eq_zero] at hx
    rw [hx, ← hrange]
    exact ⟨x, rfl⟩
  · intro hx
    rw [hfix x hx, sub_self]

theorem rationalTagProjectionComplement_idempotent
    (P : Matrix T T ℚ) (V : Submodule ℚ (T → ℚ))
    (hrange : LinearMap.range (Matrix.mulVecLin (fun i j => (P i j : ℝ))) =
      realRationalCoordinateSpan V)
    (hfix : ∀ x ∈ realRationalCoordinateSpan V,
      Matrix.mulVecLin (fun i j => (P i j : ℝ)) x = x)
    (x : T → ℝ) :
    rationalTagProjectionComplement P (rationalTagProjectionComplement P x) =
      rationalTagProjectionComplement P x := by
  let L := Matrix.mulVecLin (fun i j => (P i j : ℝ))
  have hmem : L x ∈ realRationalCoordinateSpan V := by
    rw [← hrange]
    exact ⟨x, rfl⟩
  have hLL : L (L x) = L x := hfix _ hmem
  change x - L x - L (x - L x) = x - L x
  rw [map_sub, hLL, sub_self, sub_zero]

theorem rationalTagProjectionComplement_coordinate_bound
    (P : Matrix T T ℚ) {H : ℝ} (hH : 0 ≤ H)
    (hP : ∀ i j, |(P i j : ℝ)| ≤ H) (x : T → ℝ) (i : T) :
    |rationalTagProjectionComplement P x i| ≤
      (1 + (Fintype.card T : ℝ) * H) * ‖x‖ := by
  classical
  have hx (j : T) : |x j| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
  have hrow : |((fun i j => (P i j : ℝ)) *ᵥ x) i| ≤
      (Fintype.card T : ℝ) * H * ‖x‖ := by
    calc
      _ ≤ ∑ j, |(P i j : ℝ) * x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : T, H * ‖x‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hP i j) (hx j) (abs_nonneg _) hH
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  rw [rationalTagProjectionComplement_apply, Pi.sub_apply]
  calc
    _ ≤ |x i| + |((fun i j => (P i j : ℝ)) *ᵥ x) i| := abs_sub _ _
    _ ≤ ‖x‖ + (Fintype.card T : ℝ) * H * ‖x‖ := add_le_add (hx i) hrow
    _ = _ := by ring

theorem rationalTagProjectionComplement_coordinate_exp_bound
    (P : Matrix T T ℚ) {p h : ℝ} (hp : 0 ≤ p) (hh : 0 ≤ h)
    (hdim : (Fintype.card T : ℝ) ≤ p)
    (hP : ∀ i j, rationalLogHeight (P i j) ≤ h) (x : T → ℝ) (i : T) :
    |rationalTagProjectionComplement P x i| ≤ Real.exp (p + h + 1) * ‖x‖ := by
  have hentry : ∀ i j, |(P i j : ℝ)| ≤ Real.exp h := fun i j =>
    (rational_abs_real_le_numerator (P i j)).trans
      ((rationalLogHeight_le_iff _ _).mp (hP i j)).1
  apply (rationalTagProjectionComplement_coordinate_bound P (Real.exp_nonneg _) hentry x i).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hdimexp : (Fintype.card T : ℝ) ≤ Real.exp p :=
    hdim.trans (by linarith [Real.add_one_le_exp p])
  have h1 : 1 ≤ Real.exp (p + h) := Real.one_le_exp_iff.mpr (add_nonneg hp hh)
  calc
    1 + (Fintype.card T : ℝ) * Real.exp h ≤ 1 + Real.exp p * Real.exp h := by gcongr
    _ = 1 + Real.exp (p + h) := by rw [Real.exp_add]
    _ ≤ 2 * Real.exp (p + h) := by linarith
    _ ≤ Real.exp 1 * Real.exp (p + h) := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (p + h + 1) := by rw [← Real.exp_add]; congr 1; ring

theorem rationalTagProjectionComplement_denominator_grid
    (P : Matrix T T ℚ) (D l : ℕ)
    (hP : ∀ i j, ∃ z : ℤ, (D : ℝ) * (P i j : ℝ) = z)
    (x : T → ℝ) (hx : x ∈ realDenominatorGrid l) :
    rationalTagProjectionComplement P x ∈ realDenominatorGrid (D * l) :=
  real_matrix_complement_linearMap_specified_denominator_grid
    (fun i j => (P i j : ℝ)) D l hP x hx

theorem rationalTagProjectionComplement_integer_grid
    (P : Matrix T T ℚ) (D : ℕ)
    (hP : ∀ i j, ∃ z : ℤ, (D : ℝ) * (P i j : ℝ) = z)
    (x : T → ℤ) :
    ∃ z : T → ℤ, ∀ i,
      (D : ℝ) * rationalTagProjectionComplement P (fun j => (x j : ℝ)) i = (z i : ℝ) := by
  have hx : (fun j => (x j : ℝ)) ∈ realDenominatorGrid 1 :=
    ⟨x, by ext j; simp⟩
  obtain ⟨z, hz⟩ := rationalTagProjectionComplement_denominator_grid P D 1 hP _ hx
  refine ⟨z, fun i => ?_⟩
  have hi := congrFun hz i
  simpa only [mul_one, Pi.smul_apply, smul_eq_mul] using hi.symm

namespace VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

end VectorPolynomial
end Erdos3

end

end OAI

end


