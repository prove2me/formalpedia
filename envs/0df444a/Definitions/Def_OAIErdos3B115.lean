-- Prove2me | Definitions.Def_OAIErdos3B115
-- name    : OAIErdos3B115
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T05:51:08.352133+00:00
-- url     : https://prove2.me/theorems/e6c916a3-07a6-4b6d-b6fa-d3390031dd0c
-- title:
--   OpenAI Erdős-3 split, definitions bundle 116 of 132
-- statement:
--   Definitions bundle 116 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B114`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 116 available.
--
--   Modules: `OAI.Erdos3.BooleanCubeKernel.exists_fixed_kernel_bounded_section`, `OAI.Erdos3.BooleanCubeKernel.exists_fixed_kernel_bounded_section_multiple`, `OAI.Erdos3.NativeCorrelationStructure.casesOn`, `OAI.Erdos3.NativeCorrelationStructure.mono`, `OAI.Erdos3.NativeCorrelationStructure.normalizedLower`, `OAI.Erdos3.NativeCorrelationStructure.normalizedLower_norm`, `OAI.Erdos3.NativeCorrelationStructure.normalizedLower_of_mem`, `OAI.Erdos3.NativeCorrelationStructure.selectedProduct`, `OAI.Erdos3.NativeCorrelationStructure.selectedProduct_correlation`, `OAI.Erdos3.NativeCorrelationStructure.selectedWitness`, `OAI.Erdos3.NativeDegreeRankFamily`, `OAI.Erdos3.NativeDegreeRankFamily.eval`, `OAI.Erdos3.NativeDegreeRankFamily.evalCyclic`, `OAI.Erdos3.NativeDegreeRankFamily.mono`, `OAI.Erdos3.NativeDegreeRankFamily.norm_eval`, `OAI.Erdos3.NativeDegreeRankFamily.orbit_rank_normalized`, `OAI.Erdos3.NativeIntegerVectorEquivalence.ExpansionIndex`, `OAI.Erdos3.NativeIntegerVectorEquivalence.expansionIndex_card_bound`, `OAI.Erdos3.NativeMixedCorrelation.exists_fixed_normalized_residual_coordinate`, `OAI.Erdos3.NativeMixedCorrelation.mono`, `OAI.Erdos3.NativeMixedCorrelation.normalizedResidualRow`, `OAI.Erdos3.NativeMixedCorrelation.normalizedResidualRow_correlation`, `OAI.Erdos3.NativeMixedCorrelation.normalizedResidualRow_factor`, `OAI.Erdos3.NativeMixedCorrelation.normalizedResidualRow_norm`, `OAI.Erdos3.NativeMixedCorrelation.rec`, `OAI.Erdos3.NativeMixedCorrelation.residualMultiplier`, `OAI.Erdos3.NativeMixedCorrelation.residualMultiplier_expansion`, `OAI.Erdos3.NativeMixedCorrelation.residualMultiplier_norm`, `OAI.Erdos3.NativeMixedCorrelation.residualWitness`, `OAI.Erdos3.NativePolynomialOrbitFactors`, `OAI.Erdos3.NativePolynomialOrbitFactors.HasOuterValueControl`, `OAI.Erdos3.NativePolynomialOrbitFactors.eval_niltest`, `OAI.Erdos3.NativePolynomialOrbitFactors.hasOuterValueControl_mono`, `OAI.Erdos3.NativePolynomialOrbitFactors.mono`, `OAI.Erdos3.NativePolynomialOrbitFactors.rationalValue`, `OAI.Erdos3.NativePolynomialOrbitFactors.slowValue`, `OAI.Erdos3.NilpotentLieFiltration.polynomialOrbitCoordinates_realValue`, `OAI.Erdos3.PolynomialTranslationLie.central_character_eq_fourierChar`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslationTwistedObservable_central`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslation_frequency_one_of_central`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslation_selected_frequency_one`, `OAI.Erdos3.PolynomialTranslationLie.weightedTranslation_twisted_selected_frequency_one`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.conjugate_vertical`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.exists_vertical_decomposition_preserving_bounds_and_characters`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.oneOnOrbit`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.oneOnOrbit_complexity`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.oneOnOrbit_eval`, `OAI.Erdos3.RationalFilteredNilmanifold.Niltest.oneOnOrbit_vertical`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_orbit_rational_period`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_rational_period`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_orbit_factor_freezing`, `OAI.Erdos3.RationalFilteredNilmanifold.polynomialRationalGrid_uniform_cosets`, `OAI.Erdos3.VectorPolynomial.AllocatedComparisonDimensions.layer_degree`, `OAI.Erdos3.VectorPolynomial.AllocatedComparisonDimensions.recOn`, `OAI.Erdos3.VectorPolynomial.CoefficientAxisArrays`, `OAI.Erdos3.VectorPolynomial.CoefficientAxisRow`, `OAI.Erdos3.VectorPolynomial.CoefficientJetAxisRow`, `OAI.Erdos3.VectorPolynomial.CoefficientJetScalar`, `OAI.Erdos3.VectorPolynomial.DegreeLE.subtractConstant`, `OAI.Erdos3.VectorPolynomial.affineSampleCoefficientArray_subtractConstant`, `OAI.Erdos3.VectorPolynomial.affineSampleCoefficientTorus_subtractConstant`, `OAI.Erdos3.VectorPolynomial.allocatedAmbientDimension_eq`, `OAI.Erdos3.VectorPolynomial.allocatedAmbientDimension_le_axes`, `OAI.Erdos3.VectorPolynomial.allocatedAxes_card_le`, `OAI.Erdos3.VectorPolynomial.allocatedComparisonDimension`, `OAI.Erdos3.VectorPolynomial.allocatedComparisonDimension_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedComparisonDimensions_of_primitive`, `OAI.Erdos3.VectorPolynomial.allocatedDensityEnvelope`, `OAI.Erdos3.VectorPolynomial.allocatedDensityEnvelope_nonneg`, `OAI.Erdos3.VectorPolynomial.allocatedFrontEnvelope`, `OAI.Erdos3.VectorPolynomial.allocatedJointParameter_card`, `OAI.Erdos3.VectorPolynomial.allocatedKernelEnvelope`, `OAI.Erdos3.VectorPolynomial.allocatedKernelVariables_card_le_variables`, `OAI.Erdos3.VectorPolynomial.allocatedLatticeDimension_eq`, `OAI.Erdos3.VectorPolynomial.allocatedPrincipalIndex_card_le_variables`, `OAI.Erdos3.VectorPolynomial.allocatedSupportEnvelope`, `OAI.Erdos3.VectorPolynomial.allocatedSupportEnvelope_nonneg`, `OAI.Erdos3.VectorPolynomial.allocatedWitnessScaleLog`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientJetArrays`, `OAI.Erdos3.VectorPolynomial.coefficientAxisEquiv`, `OAI.Erdos3.VectorPolynomial.coefficientAxisLaw`, `OAI.Erdos3.VectorPolynomial.coefficientAxisRowMeasurable`, `OAI.Erdos3.VectorPolynomial.coefficientAxisSplitEquiv`, `OAI.Erdos3.VectorPolynomial.coefficientJetAxisEquiv`, `OAI.Erdos3.VectorPolynomial.coefficientJetAxisMap`, `OAI.Erdos3.VectorPolynomial.coefficientJetAxisReference`, `OAI.Erdos3.VectorPolynomial.coefficientJetAxisReference_sigmaFinite`, `OAI.Erdos3.VectorPolynomial.coefficientJetAxisRowMeasurable`, `OAI.Erdos3.VectorPolynomial.coefficientJetScalarEquiv`, `OAI.Erdos3.VectorPolynomial.coefficientJetScalarMeasurable`, `OAI.Erdos3.VectorPolynomial.coefficientJetScalarReference`, `OAI.Erdos3.VectorPolynomial.coefficientJetScalarReference_sigmaFinite`, `OAI.Erdos3.VectorPolynomial.coefficients_subtractConstant`, `OAI.Erdos3.VectorPolynomial.coefficients_subtractConstant_mem`, `OAI.Erdos3.VectorPolynomial.comparisonProfileBound`, `OAI.Erdos3.VectorPolynomial.eval_subtractConstant`, `OAI.Erdos3.VectorPolynomial.exists_bounded_residual_cover_budget`, `OAI.Erdos3.VectorPolynomial.hasLayerSamplingRank_subtractConstant_iff`, `OAI.Erdos3.VectorPolynomial.homogeneousPart_subtractConstant`, `OAI.Erdos3.VectorPolynomial.substitute_subtractConstant`, `OAI.Erdos3.VectorPolynomial.subtractConstant`, `OAI.Erdos3.abs_coordinate_det_le_sqrt_gram`, `OAI.Erdos3.abs_isometric_lattice_basis_det_le_covolume`, `OAI.Erdos3.circleQuarterCover`, `OAI.Erdos3.complex_expect_error_le`, `OAI.Erdos3.correlationInput`, `OAI.Erdos3.divided_derivative_horizontal_coordinates`, `OAI.Erdos3.divided_derivative_lattice_coordinates`, `OAI.Erdos3.euclideanDerivativeShiftMap`, `OAI.Erdos3.euclideanDerivativeShiftMap_apply`, `OAI.Erdos3.euclideanDerivativeShiftMap_eq_zero_iff`, `OAI.Erdos3.euclideanDerivativeShiftMap_integer`, `OAI.Erdos3.euclideanDerivative_vertical_grid_coordinates`, `OAI.Erdos3.euclideanDerivative_vertical_lattice_full`, `OAI.Erdos3.euclideanVerticalMap`, `OAI.Erdos3.euclideanVerticalMap_apply_inl`, `OAI.Erdos3.euclideanVerticalMap_apply_inr`, `OAI.Erdos3.euclidean_graph_residual_mem_kernel`, `OAI.Erdos3.euclidean_shift_subspace_surjective`, `OAI.Erdos3.exists_euclidean_lattice_graph_identity`, `OAI.Erdos3.exists_native_orbit_coefficient_control`, `OAI.Erdos3.exists_native_orbit_local_control`, `OAI.Erdos3.exists_native_orbit_outer_control`, `OAI.Erdos3.exists_native_polynomial_orbit_factors`, `OAI.Erdos3.exists_native_vertical_pair_preserving_characters_on_finset`, `OAI.Erdos3.exists_native_vertical_pair_preserving_characters_power`, `OAI.Erdos3.exists_normalized_representative_offset`, `OAI.Erdos3.exterior_norm_eq_sqrt_gram`, `OAI.Erdos3.lattice_norm_le_projection_of_grid_minor`, `OAI.Erdos3.lattice_norm_le_selected_coordinates`, `OAI.Erdos3.lattice_projection_all_minors_bound`, `OAI.Erdos3.mixedCorrelationDegree`, `OAI.Erdos3.nativeCorrelationResidual`, `OAI.Erdos3.nativeMixedResidual`, `OAI.Erdos3.normalizedCoveredChart`, `OAI.Erdos3.normalizedLatticeRepresentativeHom`, `OAI.Erdos3.quarterCoverPoint`, `OAI.Erdos3.realDenominatorGrid_div_nat`, `OAI.Erdos3.realifyFunctional_neg`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B113
import Definitions.Def_OAIErdos3B121

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.WeightedTranslationTwistedCentralFrequency
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_vertical_decomposition_preserving_bounds_and_characters (T : D.Niltest w)
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
      (∀ (z : D.RealGroup) (c : ℂ), (∀ x, T.observable (z • x) = c * T.observable x) →
        ∀ j x, (U j).observable (z • x) = c * (U j).observable x) ∧
      (∀ x, ‖(∑ j, (U j).observable x) - T.observable x‖ ≤ rho) ∧
      ∀ x : σ → ℤ, ‖(∑ j, (U j).eval x) - T.eval x‖ ≤ rho := by
  let := D.metricSpace
  have hK : (T.lipBound : ℝ) ≤ Real.exp p := by
    have h := observable_budget hT
    have hB := T.normBound.coe_nonneg
    linarith
  obtain ⟨J, inst, eta, v, hcard, hheight, hv, hchar, hpres, herr⟩ :=
    D.exists_controlled_vertical_decomposition hp hT.1 T.observable T.lipBound T.normBound
      T.lipschitz T.norm_le hK rho hrho hrhop
  let U : J → D.Niltest w := fun j =>
    { orbit := T.orbit
      observable := v j
      normBound := T.normBound
      lipBound := T.lipBound
      norm_le := (hv j).2
      lipschitz := (hv j).1 }
  refine ⟨J, inst, eta, U, hcard, hheight, fun _ => ⟨hT, rfl, rfl, rfl⟩, hchar, ?_, hpres, herr, ?_⟩
  · intro j hne z hz hGamma
    exact vertical_frequency_integral_on_lattice D.filtration D.realLattice (eta j) (v j)
      (hchar j) hne z hz hGamma
  · intro x
    exact herr (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x T.orbit))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_native_vertical_pair_preserving_characters_on_finset
    {X σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
    (D : RationalFilteredNilmanifold L s d) (D' : RationalFilteredNilmanifold M s e)
    {w : σ → ℕ} (Q : D.Niltest w) (R : D'.Niltest w)
    {p q delta rho eta : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hdelta : 0 < delta)
    (hrho : 0 < rho) (heta : 0 < eta) (hrhop : rho⁻¹ ≤ Real.exp p) (hetaq : eta⁻¹ ≤ Real.exp q)
    (hQc : Q.ComplexityLE p) (hRc : R.ComplexityLE q)
    (hQcap : (Q.normBound : ℝ) ≤ 1) (hRcap : (R.normBound : ℝ) ≤ 1)
    (hsmall : rho + Real.exp (verticalDecompositionBudget p) * eta ≤ delta / 2)
    (B : Finset X) (hB : B.Nonempty) (sample : X → σ → ℤ) (U : X → ℂ)
    (hU : ∀ x ∈ B, ‖U x‖ ≤ 1)
    (hcorr : delta ≤ ‖𝔼 x ∈ B, U x * Q.eval (sample x) * R.eval (sample x)‖) :
    ∃ (freq : L →ₗ[ℚ] ℚ) (freq' : M →ₗ[ℚ] ℚ) (V : D.Niltest w) (W : D'.Niltest w),
      V.ComplexityLE p ∧ V.orbit = Q.orbit ∧ V.normBound = Q.normBound ∧
      W.ComplexityLE q ∧ W.orbit = R.orbit ∧ W.normBound = R.normBound ∧
      (∀ i, rationalLogHeight (freq (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ i, rationalLogHeight (freq' (D'.basis i)) ≤ verticalDecompositionBudget q) ∧
      (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        V.observable (z • x) = character ((realifyFunctional freq z.coord : ℝ) : CircleFourier.Circle) *
          V.observable x) ∧
      (∀ z, z ∈ D'.filtration.realification.subgroup s → ∀ x,
        W.observable (z • x) = character ((realifyFunctional freq' z.coord : ℝ) : CircleFourier.Circle) *
          W.observable x) ∧
      (∀ (z : D.RealGroup) (c : ℂ),
        (∀ x, Q.observable (z • x) = c * Q.observable x) →
          ∀ x, V.observable (z • x) = c * V.observable x) ∧
      (∀ (z : D'.RealGroup) (c : ℂ),
        (∀ x, R.observable (z • x) = c * R.observable x) →
          ∀ x, W.observable (z • x) = c * W.observable x) ∧
      (∃ x, V.observable x ≠ 0) ∧ (∃ x, W.observable x ≠ 0) ∧
      (delta / 2) / (Real.exp (verticalDecompositionBudget p) * Real.exp (verticalDecompositionBudget q)) ≤
        ‖𝔼 x ∈ B, U x * V.eval (sample x) * W.eval (sample x)‖ := by
  obtain ⟨I, instI, freqV, V, hI, hheightV, hcertV, hvertV, _, hpresV, _, happroxV⟩ :=
    Q.exists_vertical_decomposition_preserving_bounds_and_characters hp hQc hrho hrhop
  let := instI
  obtain ⟨J, instJ, freqW, W, hJ, hheightW, hcertW, hvertW, _, hpresW, _, happroxW⟩ :=
    R.exists_vertical_decomposition_preserving_bounds_and_characters hq hRc heta hetaq
  let := instJ
  obtain ⟨i, j, hbias⟩ := exists_correlating_components_on_finset B hB U
    (fun x => Q.eval (sample x)) (fun x => R.eval (sample x))
    (fun i x => (V i).eval (sample x)) (fun j x => (W j).eval (sample x))
    hdelta (Real.exp_pos _) (Real.exp_pos _) hrho.le heta.le hI hJ hU
    (fun x _ => (R.norm_eval_le (sample x)).trans hRcap)
    (fun i x _ => ((V i).norm_eval_le (sample x)).trans (by rw [(hcertV i).2.2.1]; exact hQcap))
    (fun x _ => by simpa only [norm_sub_rev] using happroxV (sample x))
    (fun x _ => by simpa only [norm_sub_rev] using happroxW (sample x)) hsmall hcorr
  have hbiaspos : 0 < ‖𝔼 x ∈ B, U x * (V i).eval (sample x) * (W j).eval (sample x)‖ :=
    lt_of_lt_of_le (div_pos (div_pos hdelta (by norm_num))
      (mul_pos (Real.exp_pos _) (Real.exp_pos _))) hbias
  have hVne : ∃ x, (V i).observable x ≠ 0 := by
    by_contra! hzero
    have heval : ∀ x, (V i).eval (sample x) = 0 := fun x => hzero _
    simp [heval] at hbiaspos
  have hWne : ∃ x, (W j).observable x ≠ 0 := by
    by_contra! hzero
    have heval : ∀ x, (W j).eval (sample x) = 0 := fun x => hzero _
    simp [heval] at hbiaspos
  exact ⟨freqV i, freqW j, V i, W j, (hcertV i).1, (hcertV i).2.1, (hcertV i).2.2.1,
    (hcertW j).1, (hcertW j).2.1, (hcertW j).2.2.1, hheightV i, hheightW j, hvertV i, hvertW j,
    (fun z c hz => hpresV z c hz i), (fun z c hz => hpresW z c hz j), hVne, hWne, hbias⟩

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_native_vertical_pair_preserving_characters_power :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X σ L M : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (D : RationalFilteredNilmanifold L s d) (D' : RationalFilteredNilmanifold M s e)
      {w : σ → ℕ} (Q : D.Niltest w) (R : D'.Niltest w) (p : ℝ), 0 ≤ p →
      Q.ComplexityLE p → R.ComplexityLE p →
      (Q.normBound : ℝ) ≤ 1 → (R.normBound : ℝ) ≤ 1 →
      ∀ (B : Finset X), B.Nonempty → ∀ (sample : X → σ → ℤ) (U : X → ℂ),
      (∀ x ∈ B, ‖U x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ B, U x * Q.eval (sample x) * R.eval (sample x)‖ →
      ∃ (freq : L →ₗ[ℚ] ℚ) (freq' : M →ₗ[ℚ] ℚ) (V : D.Niltest w) (W : D'.Niltest w),
        V.ComplexityLE ((p + C) ^ C) ∧ V.orbit = Q.orbit ∧ V.normBound = Q.normBound ∧
        W.ComplexityLE ((p + C) ^ C) ∧ W.orbit = R.orbit ∧ W.normBound = R.normBound ∧
        (∀ i, rationalLogHeight (freq (D.basis i)) ≤ (p + C) ^ C) ∧
        (∀ i, rationalLogHeight (freq' (D'.basis i)) ≤ (p + C) ^ C) ∧
        (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          V.observable (z • x) = character ((realifyFunctional freq z.coord : ℝ) : CircleFourier.Circle) *
            V.observable x) ∧
        (∀ z, z ∈ D'.filtration.realification.subgroup s → ∀ x,
          W.observable (z • x) = character ((realifyFunctional freq' z.coord : ℝ) : CircleFourier.Circle) *
            W.observable x) ∧
        (∀ (z : D.RealGroup) (c : ℂ),
          (∀ x, Q.observable (z • x) = c * Q.observable x) →
            ∀ x, V.observable (z • x) = c * V.observable x) ∧
        (∀ (z : D'.RealGroup) (c : ℂ),
          (∀ x, R.observable (z • x) = c * R.observable x) →
            ∀ x, W.observable (z • x) = c * W.observable x) ∧
        (∃ x, V.observable x ≠ 0) ∧ (∃ x, W.observable x ≠ 0) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 x ∈ B, U x * V.eval (sample x) * W.eval (sample x)‖ := by
  obtain ⟨C, hC, hprecision⟩ := exists_vertical_pair_precision
  refine ⟨C, hC, ?_⟩
  intro X σ L M _ _ _ _ s d e _ _ _ _ _ _ _ _ D D' w Q R p hp hQ hR hQcap hRcap
    B hB sample U hU hcorr
  obtain ⟨q, r, rho, eta, hpq, hpr, hqC, hrC, hVq, hVr, hrho, heta, hrhoq, hetar, hsmall, hloss⟩ :=
    hprecision p hp
  obtain ⟨freq, freq', V, W, hVc, hVo, hVn, hWc, hWo, hWn, hVheight, hWheight,
      hvertV, hvertW, hpresV, hpresW, hVne, hWne, hbias⟩ :=
    exists_native_vertical_pair_preserving_characters_on_finset D D' Q R
      (hp.trans hpq) (hp.trans hpr) (Real.exp_pos _) hrho heta hrhoq hetar
      (hQ.mono hpq) (hR.mono hpr) hQcap hRcap hsmall B hB sample U hU hcorr
  exact ⟨freq, freq', V, W, hVc.mono hqC, hVo, hVn, hWc.mono hrC, hWo, hWn,
    fun i => (hVheight i).trans hVq, fun i => (hWheight i).trans hVr,
    hvertV, hvertW, hpresV, hpresW, hVne, hWne, hloss.trans hbias⟩

end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial CircleFourier
open scoped TensorProduct

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

 theorem central_character_eq_fourierChar (t : ℝ) :
    character (t : CircleFourier.Circle) = (Real.fourierChar t : ℂ) := by
  rw [character_coe_exp, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

theorem weightedTranslation_frequency_one_of_central
    {σ : Type*} [Fintype σ] (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
    (Γ : Subgroup (weightedFiltration w d hwd).realification.Group)
    (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
    (f : (weightedFiltration w d hwd).realification.Group ⧸ Γ → ℂ)
    (hvert : ∀ z ∈ (weightedFiltration w d hwd).realification.subgroup d, ∀ x,
      f (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * f x)
    (hne : ∃ x, f x ≠ 0)
    (hline : ∀ t x, f (centralRealLine w d hw hd hwd t • x) =
      (Real.fourierChar t : ℂ) * f x) :
    η (centralRationalElement w d hd 1) = 1 := by
  apply vertical_frequency_eq_one_of_real_line (weightedFiltration w d hwd) Γ
    η f hvert hne _ (centralRationalElement_mem_top w d hd hwd 1)
  intro t x
  have he : (⟨t ⊗ₜ[ℚ] centralRationalElement w d hd 1⟩ :
      (weightedFiltration w d hwd).realification.Group) = centralRealLine w d hw hd hwd t := by
    apply NilpotentLieBCHGroup.ext
    exact (centralRealLine_coord w d hw hd hwd t).symm
  rw [he, central_character_eq_fourierChar]
  exact hline t x

theorem weightedTranslation_selected_frequency_one
    (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ)
    (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
    (f : (weightedTranslationNilmanifold w d hw hwd).Space → ℂ)
    (hvert : ∀ z ∈ (weightedFiltration w d hwd).realification.subgroup d, ∀ x,
      f (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * f x)
    (hne : ∃ x, f x ≠ 0)
    (hpres : ∀ (z : (weightedFiltration w d hwd).realification.Group) (c : ℂ),
      (∀ x, weightedTranslationBufferedObservable w d hw hwd Ψ D₀ (z • x) =
        c * weightedTranslationBufferedObservable w d hw hwd Ψ D₀ x) →
      ∀ x, f (z • x) = c * f x) :
    η (centralRationalElement w d hd 1) = 1 := by
  apply vertical_frequency_eq_one_of_real_line
    (weightedFiltration w d hwd) (weightedTranslationNilmanifold w d hw hwd).realLattice
    η f hvert hne _ (centralRationalElement_mem_top w d hd hwd 1)
  intro t x
  have he : (⟨t ⊗ₜ[ℚ] centralRationalElement w d hd 1⟩ :
      (weightedFiltration w d hwd).realification.Group) = centralRealLine w d hw hd hwd t := by
    apply NilpotentLieBCHGroup.ext
    exact (centralRealLine_coord w d hw hd hwd t).symm
  rw [he, central_character_eq_fourierChar]
  apply hpres
  intro y
  rw [weightedTranslationBufferedObservable_central w d hw hd hwd]
  exact mul_comm _ _

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial CircleFourier

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]
    (M : ℕ) (hM : 0 < M)

theorem weightedTranslationTwistedObservable_central
    (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ) (t : ℝ)
    (x : (weightedTranslationResidueNilmanifold w d hw hwd M hM).Space) :
    weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T
      (centralRealLine w d hw hd hwd t • x) =
      weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T x *
        (Real.fourierChar t : ℂ) := by
  induction x using Quotient.inductionOn with
  | h g =>
    change weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T
      (QuotientGroup.mk (centralRealLine w d hw hd hwd t * g)) = _
    rw [(centralRealLine_commute w d hw hd hwd t g).eq]
    simp only [weightedTranslationTwistedObservable_mk, map_mul, centralRealLine_map]
    exact twistedBufferedTranslationPhase_central M Ψ D₀ T _ t

theorem weightedTranslation_twisted_selected_frequency_one
    (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
    (f : (weightedTranslationResidueNilmanifold w d hw hwd M hM).Space → ℂ)
    (hvert : ∀ z ∈ (weightedFiltration w d hwd).realification.subgroup d, ∀ x,
      f (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * f x)
    (hne : ∃ x, f x ≠ 0)
    (hpres : ∀ (z : (weightedFiltration w d hwd).realification.Group) (c : ℂ),
      (∀ x, weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T (z • x) =
        c * weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T x) →
      ∀ x, f (z • x) = c * f x) :
    η (centralRationalElement w d hd 1) = 1 := by
  apply weightedTranslation_frequency_one_of_central w d hw hd hwd
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).realLattice η f hvert hne
  intro t x
  apply hpres
  intro y
  rw [weightedTranslationTwistedObservable_central w d hw hd hwd M hM]
  exact mul_comm _ _

end Erdos3.PolynomialTranslationLie

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeDegreeRankFamily
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeDegreeRankFamily (s r : ℕ) (A : Type*) (p : ℝ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L s dim
  rank : model.DegreeRankStructure r
  complexity : rank.ComplexityLE p
  orbit : A → model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)
  normalized : ∀ a, model.filtration.realification.polynomialOrbitEval (fun _ => 1) 0 (orbit a) = 1
  outputDim : ℕ
  output_pos : 0 < outputDim
  output_bound : (outputDim : ℝ) ≤ Real.exp p
  vertical : model.UnitVerticalObservable (rank.realSubgroup s r) (Fin outputDim) p

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

namespace NativeDegreeRankFamily

variable {s r : ℕ} {A : Type*} {p q : ℝ} (W : NativeDegreeRankFamily s r A p)

noncomputable def eval (i : Fin W.outputDim) (a : A) (n : ℤ) : ℂ :=
  W.vertical.observable i (QuotientGroup.mk
    (W.model.filtration.realification.polynomialOrbitEval (fun _ => 1) (fun _ => n) (W.orbit a)))

noncomputable def evalCyclic (N : ℕ) [NeZero N] (i : Fin W.outputDim) (a : A) (n : ZMod N) : ℂ :=
  W.eval i a (n.val : ℤ)

theorem norm_eval (i : Fin W.outputDim) (a : A) (n : ℤ) : ‖W.eval i a n‖ ≤ 1 := W.vertical.norm i _

theorem orbit_rank_normalized (a : A) :
    W.rank.filtration.realification.associatedDegree.polynomialOrbitEval (fun _ : Unit => 1) 0
      (W.rank.orbitEquiv (fun _ : Unit => 1) (W.orbit a)) = 1 := by
  rw [W.rank.orbitEquiv_eval]
  exact W.normalized a

noncomputable def mono (hpq : p ≤ q) : NativeDegreeRankFamily s r A q :=
  { W with
    complexity := W.complexity.mono W.rank hpq
    output_bound := W.output_bound.trans (Real.exp_le_exp.mpr hpq)
    vertical := W.vertical.mono hpq }

end NativeDegreeRankFamily

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeResidualMultiplier
namespace OAI

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped BigOperators

variable {σ J K : Type*} [Fintype J] [Fintype K] {s : ℕ} {p : ℝ}
  {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ}
  (E : NativeIntegerVectorEquivalence s p chi eta)

abbrev ExpansionIndex := Σ j : J, Σ k : K, Fin (E.selectedExpansion j k).count

theorem expansionIndex_card_bound {a b : ℝ}
    (hJ : (Fintype.card J : ℝ) ≤ Real.exp a)
    (hK : (Fintype.card K : ℝ) ≤ Real.exp b) :
    (Fintype.card E.ExpansionIndex : ℝ) ≤ Real.exp (a + b + p) := by
  classical
  simp only [ExpansionIndex, Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
  calc
    (∑ j : J, ∑ k : K, ((E.selectedExpansion j k).count : ℝ)) ≤
        ∑ _j : J, ∑ _k : K, Real.exp p :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
        (E.selectedExpansion j k).count_bound
    _ = (Fintype.card J : ℝ) * ((Fintype.card K : ℝ) * Real.exp p) := by simp
    _ ≤ Real.exp a * (Real.exp b * Real.exp p) :=
      mul_le_mul hJ (mul_le_mul_of_nonneg_right hK (Real.exp_nonneg _))
        (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (a + b + p) := by rw [← mul_assoc, ← Real.exp_add, ← Real.exp_add]

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3

def correlationInput {A : Type*} (h n : A) : Fin 2 → A := Fin.cases h (fun _ => n)

def mixedCorrelationDegree (s : ℕ) : Fin 2 → ℕ := correlationInput 1 s

noncomputable def nativeCorrelationResidual {s r N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (mixed : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
    (family : NativeDegreeRankFamily s r (ZMod N) p) (h : ZMod N)
    (ij : Fin mixed.outputDim × Fin family.outputDim) (x : ZMod N) : ℂ :=
  multiplicativeDerivative f h x * star (mixed.evalCyclic N ij.1 (correlationInput h x)) *
    star (family.evalCyclic N ij.2 h x)

structure NativeCorrelationStructure (s r N : ℕ) [NeZero N] (p : ℝ) (f : ZMod N → ℂ) where
  shifts : Finset (ZMod N)
  nonempty : shifts.Nonempty
  density : Real.exp (-p) * Fintype.card (ZMod N) ≤ (shifts.card : ℝ)
  mixed : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p
  family : NativeDegreeRankFamily s r (ZMod N) p
  correlation : ∀ h ∈ shifts, Nonempty (NativeVectorCorrelation (s - 1) N p
    (nativeCorrelationResidual f mixed family h))

namespace NativeCorrelationStructure

variable {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

noncomputable def mono (hpq : p ≤ q) : NativeCorrelationStructure s r N q f where
  shifts := W.shifts
  nonempty := W.nonempty
  density := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq))
    (Nat.cast_nonneg _)).trans W.density
  mixed := W.mixed.mono hpq
  family := W.family.mono hpq
  correlation h hh := by
    obtain ⟨V⟩ := W.correlation h hh
    exact ⟨V.mono hpq⟩

end NativeCorrelationStructure

end Erdos3

end

section

namespace Erdos3.NativeCorrelationStructure

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

noncomputable def selectedWitness (h : W.shifts) :
    NativeVectorCorrelation (s - 1) N p (nativeCorrelationResidual f W.mixed W.family h) :=
  Classical.choice (W.correlation h h.property)

noncomputable def selectedProduct (h : W.shifts) (x : ZMod N) : ℂ :=
  W.mixed.evalCyclic N (W.selectedWitness h).coordinate.1 (correlationInput h.val x) *
    W.family.evalCyclic N (W.selectedWitness h).coordinate.2 h.val x *
    (W.selectedWitness h).test.evalCyclic N (fun _ => x)

theorem selectedProduct_correlation (h : W.shifts) :
    Real.exp (-p) ≤ ‖𝔼 x, multiplicativeDerivative f h.val x * star (W.selectedProduct h x)‖ := by
  simpa only [selectedProduct, nativeCorrelationResidual, star_mul, mul_assoc, mul_left_comm, mul_comm]
    using (W.selectedWitness h).correlation

end Erdos3.NativeCorrelationStructure

end

section

namespace Erdos3

noncomputable def nativeMixedResidual {s N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (mixed : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
    (h : ZMod N) (i : Fin mixed.outputDim) (x : ZMod N) : ℂ :=
  multiplicativeDerivative f h x * star (mixed.evalCyclic N i (correlationInput h x))

structure NativeMixedCorrelation (s N : ℕ) [NeZero N] (p : ℝ) (f : ZMod N → ℂ) where
  shifts : Finset (ZMod N)
  nonempty : shifts.Nonempty
  density : Real.exp (-p) * Fintype.card (ZMod N) ≤ (shifts.card : ℝ)
  mixed : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p
  correlation : ∀ h ∈ shifts, Nonempty (NativeVectorCorrelation (s - 1) N p
    (nativeMixedResidual f mixed h))

namespace NativeMixedCorrelation

variable {s N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  (W : NativeMixedCorrelation s N p f)

noncomputable def mono (hpq : p ≤ q) : NativeMixedCorrelation s N q f where
  shifts := W.shifts
  nonempty := W.nonempty
  density := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq))
    (Nat.cast_nonneg _)).trans W.density
  mixed := W.mixed.mono hpq
  correlation h hh := by
    obtain ⟨V⟩ := W.correlation h hh
    exact ⟨V.mono hpq⟩

end NativeMixedCorrelation

end Erdos3

end

section

namespace Erdos3.NativeCorrelationStructure

open scoped BigOperators

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

end Erdos3.NativeCorrelationStructure

end

section

namespace Erdos3.NativeCorrelationStructure

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

noncomputable def normalizedLower (b : ℝ) (h x : ZMod N) : ℂ :=
  if hh : h ∈ W.shifts then
    ((W.selectedWitness ⟨h, hh⟩).test.expNormalize b).evalCyclic N (fun _ => x)
  else 0

theorem normalizedLower_of_mem (b : ℝ) (h : ZMod N) (hh : h ∈ W.shifts) (x : ZMod N) :
    W.normalizedLower b h x =
      ((W.selectedWitness ⟨h, hh⟩).test.expNormalize b).evalCyclic N (fun _ => x) := by
  simp only [normalizedLower, dif_pos hh]

theorem normalizedLower_norm {b : ℝ} (hpb : p ≤ b) (h x : ZMod N) :
    ‖W.normalizedLower b h x‖ ≤ 1 := by
  by_cases hh : h ∈ W.shifts
  · rw [W.normalizedLower_of_mem b h hh]
    exact (((W.selectedWitness ⟨h, hh⟩).test.expNormalize b).norm_evalCyclic_le N _).trans
      ((W.selectedWitness ⟨h, hh⟩).test.expNormalize_norm
        ((W.selectedWitness ⟨h, hh⟩).complexity.mono hpb))
  · simp only [normalizedLower, dif_neg hh, norm_zero, zero_le_one]

end Erdos3.NativeCorrelationStructure

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

namespace RationalFilteredNilmanifold.Niltest

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {N : ℕ} [NeZero N]

end RationalFilteredNilmanifold.Niltest

namespace NativeIntegerVectorEquivalence

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

end NativeIntegerVectorEquivalence
end Erdos3

end

section

namespace Erdos3

namespace NativeMultidegreeNilcharacter

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3.NativeMixedCorrelation

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (M : NativeMixedCorrelation s N p f)

noncomputable def residualWitness (h : {h // h ∈ M.shifts}) :
    NativeVectorCorrelation (s - 1) N p (nativeMixedResidual f M.mixed h.val) :=
  Classical.choice (M.correlation h.val h.property)

noncomputable def normalizedResidualRow (h n : ZMod N) : ℂ :=
  if hh : h ∈ M.shifts then
    multiplicativeDerivative f h n *
      star (((M.residualWitness ⟨h, hh⟩).test.expNormalize p).evalCyclic N (fun _ => n))
  else 0

theorem normalizedResidualRow_norm (hf : ∀ n, ‖f n‖ ≤ 1) (h n : ZMod N) :
    ‖M.normalizedResidualRow h n‖ ≤ 1 := by
  classical
  by_cases hh : h ∈ M.shifts
  · rw [normalizedResidualRow, dif_pos hh, norm_mul, norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _)
      (multiplicativeDerivative_norm_le_one f hf h n)).trans
    apply (((M.residualWitness ⟨h, hh⟩).test.expNormalize p).norm_eval_le _).trans
    exact_mod_cast (M.residualWitness ⟨h, hh⟩).test.expNormalize_norm
      (M.residualWitness ⟨h, hh⟩).complexity
  · simp only [normalizedResidualRow, dif_neg hh, norm_zero, zero_le_one]

theorem normalizedResidualRow_correlation (h : ZMod N) (hh : h ∈ M.shifts) :
    Real.exp (-(2 * p)) ≤ ‖𝔼 n : ZMod N, M.normalizedResidualRow h n *
      star (M.mixed.evalCyclic N (M.residualWitness ⟨h, hh⟩).coordinate (correlationInput h n))‖ := by
  classical
  let V := M.residualWitness ⟨h, hh⟩
  have heval (n : ZMod N) : (V.test.expNormalize p).evalCyclic N (fun _ => n) =
      (Real.exp (-p) : ℂ) * V.test.evalCyclic N (fun _ => n) := rfl
  have hmean : (𝔼 n : ZMod N, M.normalizedResidualRow h n *
      star (M.mixed.evalCyclic N V.coordinate (correlationInput h n))) =
      (Real.exp (-p) : ℂ) * (𝔼 n : ZMod N,
        nativeMixedResidual f M.mixed h V.coordinate n * star (V.test.evalCyclic N (fun _ => n))) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro n _
    rw [normalizedResidualRow, dif_pos hh]
    change (multiplicativeDerivative f h n * star ((V.test.expNormalize p).evalCyclic N (fun _ => n))) *
      star (M.mixed.evalCyclic N V.coordinate (correlationInput h n)) = _
    rw [heval, star_mul]
    simp only [nativeMixedResidual, Complex.star_def, Complex.conj_ofReal]
    ring
  change Real.exp (-(2 * p)) ≤ ‖𝔼 n : ZMod N, M.normalizedResidualRow h n *
    star (M.mixed.evalCyclic N V.coordinate (correlationInput h n))‖
  rw [hmean, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ = Real.exp (-p) * Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left V.correlation (Real.exp_nonneg _)

theorem exists_fixed_normalized_residual_coordinate :
    ∃ out : Fin M.mixed.outputDim, ∃ H : Finset (ZMod N), H ⊆ M.shifts ∧ H.Nonempty ∧
      Real.exp (-(2 * p)) * N ≤ (H.card : ℝ) ∧
      ∀ h ∈ H, Real.exp (-(2 * p)) ≤ ‖𝔼 n : ZMod N, M.normalizedResidualRow h n *
        star (M.mixed.evalCyclic N out (correlationInput h n))‖ := by
  classical
  let rel := fun (h : ZMod N) (_ : Unit) (out : Fin M.mixed.outputDim) =>
    Real.exp (-(2 * p)) ≤ ‖𝔼 n : ZMod N, M.normalizedResidualRow h n *
      star (M.mixed.evalCyclic N out (correlationInput h n))‖
  have hc : ∀ h ∈ M.shifts, ∀ z : Unit, ∃ out, rel h z out := by
    intro h hh _
    exact ⟨(M.residualWitness ⟨h, hh⟩).coordinate, M.normalizedResidualRow_correlation h hh⟩
  have hcount : (Fintype.card (Fin M.mixed.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using M.mixed.output_bound
  obtain ⟨out, H, hsub, hH, hsize, hcorr⟩ :=
    exists_large_fixed_choices M.shifts M.nonempty rel hc hcount
  have hsize' : Real.exp (-p) * (M.shifts.card : ℝ) ≤ (H.card : ℝ) := by
    simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hsize
  have hdensity : Real.exp (-p) * N ≤ (M.shifts.card : ℝ) := by
    simpa only [ZMod.card] using M.density
  refine ⟨out (), H, hsub, hH, ?_, fun h hh => hcorr h hh ()⟩
  calc
    _ = Real.exp (-p) * (Real.exp (-p) * N) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-p) * (M.shifts.card : ℝ) :=
      mul_le_mul_of_nonneg_left hdensity (Real.exp_nonneg _)
    _ ≤ _ := hsize'

end Erdos3.NativeMixedCorrelation

end

section

namespace Erdos3.NativeMixedCorrelation

open scoped TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (M : NativeMixedCorrelation s N p f)

noncomputable def residualMultiplier (h : ZMod N) (x : Unit → ℤ) : ℂ :=
  if hh : h ∈ M.shifts then ((M.residualWitness ⟨h, hh⟩).test.expNormalize p).eval x else 0

theorem residualMultiplier_norm (h : ZMod N) (x : Unit → ℤ) :
    ‖M.residualMultiplier h x‖ ≤ 1 := by
  classical
  by_cases hh : h ∈ M.shifts
  · rw [residualMultiplier, dif_pos hh]
    apply (((M.residualWitness ⟨h, hh⟩).test.expNormalize p).norm_eval_le x).trans
    exact_mod_cast (M.residualWitness ⟨h, hh⟩).test.expNormalize_norm
      (M.residualWitness ⟨h, hh⟩).complexity
  · simp only [residualMultiplier, dif_neg hh, norm_zero, zero_le_one]

theorem normalizedResidualRow_factor (h n : ZMod N) :
    M.normalizedResidualRow h n =
      multiplicativeDerivative f h n * star (M.residualMultiplier h (fun _ => (n.val : ℤ))) := by
  classical
  by_cases hh : h ∈ M.shifts
  · simp only [normalizedResidualRow, residualMultiplier, dif_pos hh]
    rfl
  · simp only [normalizedResidualRow, residualMultiplier, dif_neg hh, star_zero, mul_zero]

theorem residualMultiplier_expansion (h : ZMod N) :
    Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) p (M.residualMultiplier h)) := by
  classical
  by_cases hh : h ∈ M.shifts
  · let V := M.residualWitness ⟨h, hh⟩
    refine ⟨NativeIntegerExpansion.ofTest (V.test.expNormalize p)
      (V.test.expNormalize_complexity V.complexity) ?_⟩
    intro x
    simp only [residualMultiplier, dif_pos hh]
    rfl
  · obtain ⟨h₀, hh₀⟩ := M.nonempty
    let V := M.residualWitness ⟨h₀, hh₀⟩
    refine ⟨NativeIntegerExpansion.ofTest (V.test.scaleComplex 0)
      (V.test.scaleComplex_complexity (by simp) V.complexity) ?_⟩
    intro x
    simp only [residualMultiplier, dif_neg hh,
      RationalFilteredNilmanifold.Niltest.scaleComplex_eval, zero_mul]

end Erdos3.NativeMixedCorrelation

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativePolynomialOrbitConstruction
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

structure NativePolynomialOrbitFactors {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} (D : RationalFilteredNilmanifold L s d)
    (g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (eta : L →ₗ[ℚ] ℚ) (A : σ → ℝ) (p : ℝ) where
  basis : Basis (Fin (finrank ℚ L)) ℚ L
  weight : Fin (finrank ℚ L) → ℕ
  adapted : ∀ k, D.filtration.layer k = Submodule.span ℚ (basis '' {i | k ≤ weight i})
  basis_height : ∀ i j, rationalLogHeight (D.basis.repr (basis i) j) ≤ p
  subalgebra : LieSubalgebra ℚ D.filtration.AssociatedGraded
  generator : Fin (finrank ℚ L) → D.filtration.AssociatedGraded
  spanning : Submodule.span ℚ (Set.range generator) = subalgebra.toSubmodule
  graded : BasisGradedSubmodule (D.filtration.associatedGradedBasis basis weight adapted)
    weight subalgebra.toSubmodule
  generator_height : ∀ i j, rationalLogHeight
    ((D.filtration.associatedGradedBasis basis weight adapted).repr (generator i) j) ≤ p
  kills_top : ∀ z ∈ D.filtration.realGradedRefiltrationLayer subalgebra s,
    realifyFunctional eta z = 0
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_bound : (denominator : ℝ) ≤ Real.exp p
  latticeConstant : D.RealGroup
  latticeConstant_mem : latticeConstant ∈ D.realLattice
  slow : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group
  middle : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group
  rational : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group
  product : slow * middle * rational *
    D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) latticeConstant = g
  slow_bound : ∀ α i, |(basis.baseChange ℝ).repr
    (coefficients (slow.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
      Real.exp p / monomialScale A α
  rational_grid : (fun z : (σ →₀ ℕ) × Fin (finrank ℚ L) => (basis.baseChange ℝ).repr
    (coefficients (rational.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈
      realDenominatorGrid denominator
  middle_zero : coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0
  rational_zero : coefficients (rational.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0
  middle_coefficients : ∀ α, coefficients
    (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
      D.filtration.realGradedRefiltrationLayer subalgebra (Finsupp.weight (fun _ => 1) α)

namespace NativePolynomialOrbitFactors

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}
  {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
  {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p q : ℝ}
  (R : NativePolynomialOrbitFactors D g eta A p)

noncomputable def mono (hpq : p ≤ q) (hA : ∀ i, 0 < A i) :
    NativePolynomialOrbitFactors D g eta A q :=
  { R with
    basis_height := fun i j => (R.basis_height i j).trans hpq
    generator_height := fun i j => (R.generator_height i j).trans hpq
    denominator_bound := R.denominator_bound.trans (Real.exp_le_exp.mpr hpq)
    slow_bound := fun α i => (R.slow_bound α i).trans
      (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hpq) (monomialScale_pos A hA α).le) }

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem eval_niltest (T : D.Niltest (fun _ : σ => 1))
    (hT : g = ⟨⟨T.orbit.log, T.orbit.property⟩⟩) (x : σ → ℤ) :
    T.eval x = T.observable (QuotientGroup.mk
      (D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1) (fun i => (x i : ℝ)) R.slow *
        D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1) (fun i => (x i : ℝ)) R.middle *
        D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1) (fun i => (x i : ℝ)) R.rational)) :=
  Niltest.eval_of_lattice_factorization D (fun _ : σ => 1) T R.slow R.middle R.rational
    R.latticeConstant R.latticeConstant_mem (R.product.trans hT) x

end NativePolynomialOrbitFactors

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

theorem exists_native_polynomial_orbit_factors (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] (D : RationalFilteredNilmanifold L s d)
      (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ)
      (hF : ∀ k, D.filtration.layer k = Submodule.span ℚ (b '' {i | k ≤ w i}))
      {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p) →
      ∀ (g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
        (eta : L →ₗ[ℚ] ℚ) (A : σ → ℝ),
      (∀ i, Real.exp ((p + C) ^ C) ≤ A i) →
      D.filtration.ControlledSymbolFactorization b w hF eta A
        (D.filtration.realPolynomialSymbolHom b w hF (fun _ => 1) g) p →
      Nonempty (NativePolynomialOrbitFactors D g eta A ((p + C) ^ C)) := by
  obtain ⟨a, _, hnormalize⟩ := exists_lattice_normalized_refiltered_factorization s
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + 4) ^ 11 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ d _ _ _ D b w hF p hp hD hσ hb g eta A hA hfactor
  let r := (p + 4) ^ 11 + p + 2
  have hgeom : 0 ≤ (p + 4) ^ 11 := by positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpr : p ≤ r := by dsimp [r]; linarith
  have h2r : 2 ≤ r := by dsimp [r]; linarith
  have hgr : (p + 4) ^ 11 ≤ r := by dsimp [r]; linarith
  have hcost : r + (r + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, R, r, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (r + a) ^ a := by positivity
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hfinal : (r + a) ^ a ≤ (p + C) ^ C := by linarith
  have hApos (i : σ) : 0 < A i := (Real.exp_pos _).trans_le (hA i)
  obtain ⟨m₀, hm₀, hin, hout, hE⟩ := D.exists_prescribed_adapted_model
    b w hF hp hD (fun i j => (hb i j).trans (by linarith))
  let E := D.filtration.ofAdaptedBasis b w hF D.lattice m₀ hm₀ hin hout
  have hfactor' : ∀ _j : Unit,
      E.filtration.ControlledSymbolFactorization E.basis w hF eta A
        (E.filtration.realPolynomialSymbolHom E.basis w hF (fun _ => 1) g) r := by
    intro _
    exact NilpotentLieFiltration.ControlledSymbolFactorization.mono
      D.filtration b w hF hfactor hpr hApos
  obtain ⟨U, v, m, κ, slow, middle, rat, hv, hU, hheight, hfreq, hm, hmp, hκ,
      hproduct, hslow, hrat, hmid0, hrat0, hcoeff, _hvalues⟩ :=
    hnormalize E w hF (fun _ : Unit => eta) r hr (hE.mono E hgr)
      (hσ.trans hpr) (by norm_num; linarith) A
      (fun i => (Real.exp_le_exp.mpr hfinal).trans (hA i)) g hfactor'
  exact ⟨{
    basis := b
    weight := w
    adapted := hF
    basis_height := fun i j => (hb i j).trans hpC
    subalgebra := U
    generator := v
    spanning := hv
    graded := hU
    generator_height := fun i j => (hheight i j).trans hfinal
    kills_top := hfreq ()
    denominator := m
    denominator_pos := hm
    denominator_bound := hmp.trans (Real.exp_le_exp.mpr hfinal)
    latticeConstant := κ
    latticeConstant_mem := hκ
    slow := slow
    middle := middle
    rational := rat
    product := hproduct
    slow_bound := fun α i => (hslow α i).trans
      (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hfinal) (monomialScale_pos A hApos α).le)
    rational_grid := hrat
    middle_zero := hmid0
    rational_zero := hrat0
    middle_coefficients := hcoeff }⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOrbitOuterControl
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold

theorem exists_native_orbit_coefficient_control :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
      {D : RationalFilteredNilmanifold L s d}
      {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
      {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
      (R : NativePolynomialOrbitFactors D g eta A p),
      0 ≤ p → D.GeometryComplexityLE p → (∀ i, 0 < A i) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        D.filtration.PolynomialRationalGrid D.basis (fun _ : σ => 1) m R.rational ∧
        D.filtration.PolynomialSlowBound D.basis (fun _ : σ => 1) A
          (Real.exp ((p + C) ^ C)) R.slow := by
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + 2) ^ 3 + X + (X + 3) ^ 2)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ s d D g eta A p R hp hD hA
  have hdim : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ p := by
    rw [Fintype.card_fin, finrank_eq_card_basis D.basis, Fintype.card_fin]
    exact hD.1
  have hdimD : (Fintype.card (Fin d) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hD.1
  let m := matrixDenominator (fun i j => D.basis.repr (R.basis j) i) * R.denominator
  have hmb : (m : ℝ) ≤ Real.exp ((p + 2) ^ 3 + p) :=
    NilpotentLieFiltration.original_coordinate_denominator_bound R.basis D.basis hp hdim hdimD
      R.basis_height R.denominator R.denominator_bound
  have hcost : (p + 2) ^ 3 + p + (p + 3) ^ 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hden : (p + 2) ^ 3 + p ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (sq_nonneg _)).trans hcost
  have hslow : (p + 3) ^ 2 ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity)).trans hcost
  have hs := D.filtration.polynomialSlowBound_change_basis_exp R.basis D.basis
    (fun _ : σ => 1) A hA hp hdim R.basis_height R.slow R.slow_bound
  exact ⟨m, Nat.mul_pos (matrixDenominator_pos _) R.denominator_pos,
    hmb.trans (Real.exp_le_exp.mpr hden),
    D.filtration.polynomialRationalGrid_change_basis R.basis D.basis
      (fun _ : σ => 1) R.denominator R.rational R.rational_grid,
    D.filtration.polynomialSlowBound_mono D.basis (fun _ : σ => 1) A hA
      (Real.exp_le_exp.mpr hslow) R.slow hs⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold

namespace NativePolynomialOrbitFactors

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}
  {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
  {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
  (R : NativePolynomialOrbitFactors D g eta A p)

noncomputable def slowValue (x : σ → ℤ) : D.RealGroup :=
  D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1) (fun i => (x i : ℝ)) R.slow

noncomputable def rationalValue (x : σ → ℤ) : D.RealGroup :=
  D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1) (fun i => (x i : ℝ)) R.rational

def HasOuterValueControl (b : ℝ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp b ∧
    (∀ x : σ → ℤ, (D.basis.baseChange ℝ).equivFun (R.rationalValue x).coord ∈
      realDenominatorGrid m) ∧
    ∀ x : σ → ℤ, (∀ i, |(x i : ℝ)| ≤ A i) → ∀ i,
      |(D.basis.baseChange ℝ).repr (R.slowValue x).coord i| ≤ Real.exp b

theorem hasOuterValueControl_mono {a b : ℝ} (h : R.HasOuterValueControl a) (hab : a ≤ b) :
    R.HasOuterValueControl b := by
  obtain ⟨m, hm, hmb, hrat, hslow⟩ := h
  exact ⟨m, hm, hmb.trans (Real.exp_le_exp.mpr hab), hrat,
    fun x hx i => (hslow x hx i).trans (Real.exp_le_exp.mpr hab)⟩

end NativePolynomialOrbitFactors

theorem exists_native_orbit_outer_control (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      {D : RationalFilteredNilmanifold L s d}
      {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
      {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
      (R : NativePolynomialOrbitFactors D g eta A p),
      0 ≤ p → D.GeometryComplexityLE p → (∀ i, 0 < A i) → Fintype.card σ ≤ k →
      R.HasOuterValueControl ((p + C) ^ C) := by
  obtain ⟨a, _, hcoeff⟩ := exists_native_orbit_coefficient_control
  let K := (s + 1) * (k + 1) ^ s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + Polynomial.C K)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ d D g eta A p R hp hD hA hk
  obtain ⟨m, hm, hmb, hrat, hslow⟩ := hcoeff R hp hD hA
  have htotal : (p + a) ^ a + (K : ℝ) ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (p + a) ^ a ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (Nat.cast_nonneg K)).trans htotal
  refine ⟨m, hm, hmb.trans (Real.exp_le_exp.mpr hcost), ?_, ?_⟩
  · intro x
    exact D.filtration.polynomialRationalGrid_value D.basis (fun _ : σ => 1) m R.rational hrat x
  · intro x hx i
    have hs := D.filtration.polynomialSlowBound_value D.basis (fun _ : σ => 1)
      (fun _ => Nat.zero_lt_one) A hA (Real.exp_nonneg _) R.slow hslow
      (fun j => (x j : ℝ)) hx i
    have hcard : (Fintype.card σ : ℝ) ≤ k := by exact_mod_cast hk
    have hK : ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s ≤ K := by
      dsimp [K]
      push_cast
      gcongr
    have hKexp : (K : ℝ) ≤ Real.exp K := by linarith [Real.add_one_le_exp (K : ℝ)]
    apply hs.trans
    calc
      _ ≤ (K : ℝ) * Real.exp ((p + a) ^ a) :=
        mul_le_mul_of_nonneg_right hK (Real.exp_nonneg _)
      _ ≤ Real.exp K * Real.exp ((p + a) ^ a) :=
        mul_le_mul_of_nonneg_right hKexp (Real.exp_nonneg _)
      _ = Real.exp ((K : ℝ) + (p + a) ^ a) := (Real.exp_add _ _).symm
      _ ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr (by linarith)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOrbitFreezing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem complex_expect_error_le {X : Type*} (A : Finset X) (f g : X → ℂ)
    {η : ℝ} (hη : 0 ≤ η) (herr : ∀ x ∈ A, ‖f x - g x‖ ≤ η) :
    ‖(𝔼 x ∈ A, f x) - (𝔼 x ∈ A, g x)‖ ≤ η := by
  rw [← Finset.expect_sub_distrib]
  by_cases hA : A.Nonempty
  · exact (RCLike.norm_expect_le (K := ℂ)).trans
      ((Finset.expect_le_expect herr).trans_eq (Finset.expect_const hA η))
  · have he := Finset.not_nonempty_iff_eq_empty.mp hA
    simpa only [he, Finset.expect_empty, norm_zero] using hη

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem polynomialRationalGrid_uniform_cosets {σ L : Type*} [Fintype σ]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (q : ℕ) (hq : 0 < q)
    (g : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (hg : D.filtration.PolynomialRationalGrid D.basis w q g) (x y : σ → ℤ)
    (hxy : ∀ j, (uniformPolynomialBCHPeriod (σ := σ) D.basis s s D.grid q : ℤ) ∣ x j - y j) :
    let f := fun z : σ → ℤ => D.filtration.adaptedPolynomialRealValueHom w (fun j => (z j : ℝ)) g
    ((QuotientGroup.mk (f x) : D.Space) = QuotientGroup.mk (f y)) ∧
    ((QuotientGroup.mk (f x)⁻¹ : D.Space) = QuotientGroup.mk (f y)⁻¹) := by
  obtain ⟨P, hdegree, hden, hval⟩ :=
    D.filtration.polynomialRationalGrid_exists_coordinates D.basis w hw q hq g hg
  dsimp only
  rw [← hval (fun j => (x j : ℝ)), ← hval (fun j => (y j : ℝ))]
  exact realPolynomialBCHMap_uniform_cosets D.basis D.filtration.lowerCentralSeries_eq_bot
    D.lattice s D.grid q P hdegree hden D.inner_grid x y hxy

theorem exists_native_rational_period (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : (D.filtration.realification.adaptedPolynomialFiltration w).Group,
          D.filtration.PolynomialRationalGrid D.basis w q g →
          let f := fun z : σ → ℤ => D.filtration.adaptedPolynomialRealValueHom w (fun j => (z j : ℝ)) g
          ∀ x y : σ → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
            ((QuotientGroup.mk (f x) : D.Space) = QuotientGroup.mk (f y)) ∧
            ((QuotientGroup.mk (f x)⁻¹ : D.Space) = QuotientGroup.mk (f y)⁻¹) := by
  obtain ⟨a, _, hperiod⟩ := exists_uniformPolynomialBCHPeriod_exp_bound s s
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + 1 + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ d D w hw p hp hD hσ q hq hqp
  let M := uniformPolynomialBCHPeriod (σ := σ) D.basis s s D.grid q
  have hpp : p ≤ p + 1 := le_add_of_nonneg_right zero_le_one
  have hb := hperiod (σ := σ) D.basis D.grid ⌈Real.exp p⌉₊ q (p + 1)
    (by linarith) (by simpa only [Fintype.card_fin] using hD.1.trans hpp) (hσ.trans hpp)
    (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr hpp))
    (hqp.trans (Real.exp_le_exp.mpr hpp))
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
  have hMb : (M : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    apply hb.trans (Real.exp_le_exp.mpr _)
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨M, uniformPolynomialBCHPeriod_pos D.basis s s D.grid q D.grid_pos hq, hMb,
    fun g hg x y hxy => D.polynomialRationalGrid_uniform_cosets w hw q hq g hg x y hxy⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

theorem polynomialOrbitCoordinates_realValue {σ L : Type*}
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ} (F : NilpotentLieFiltration L s)
    (w : σ → ℕ) (g : F.realification.PolynomialOrbit w) (x : σ → ℤ) :
    F.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ))
        (F.realification.polynomialOrbitCoordinates w g) =
      F.realification.polynomialOrbitEval w x g := by
  apply NilpotentLieBCHGroup.ext
  change eval₂ (fun i => (x i : ℝ)) g.log = eval (fun i => (x i : ℚ)) g.log
  simpa only [map_intCast] using
    (eval₂_algebraMap (S := ℝ) (fun i => (x i : ℚ)) g.log)

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold

theorem exists_native_orbit_rational_period (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : D.filtration.realification.PolynomialOrbit w,
          CoefficientGrid (D.basis.baseChange ℝ) q g.log →
          ∀ x y : σ → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
            ((QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g) : D.Space) =
              QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w y g)) ∧
            ((QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g)⁻¹ : D.Space) =
              QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w y g)⁻¹) := by
  obtain ⟨C, hC, hperiod⟩ := exists_native_rational_period s
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ d D w hw p hp hD hσ q hq hqp
  obtain ⟨M, hM, hMp, hsolve⟩ := hperiod D w hw p hp hD hσ q hq hqp
  refine ⟨M, hM, hMp, ?_⟩
  intro g hg x y hxy
  have hgrid := (D.filtration.polynomialRationalGrid_iff_formal D.basis w q
    (D.filtration.realification.polynomialOrbitCoordinates w g)).mpr hg
  have h := hsolve (D.filtration.realification.polynomialOrbitCoordinates w g) hgrid x y hxy
  simpa only [D.filtration.polynomialOrbitCoordinates_realValue] using h

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_orbit_local_control (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      {D : RationalFilteredNilmanifold L s d}
      {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
      {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
      (R : NativePolynomialOrbitFactors D g eta A p),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p → (∀ i, 0 < A i) →
      ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (∀ x y : σ → ℤ, (∀ i, (P : ℤ) ∣ x i - y i) →
          ((QuotientGroup.mk (R.rationalValue x) : D.Space) = QuotientGroup.mk (R.rationalValue y)) ∧
          ((QuotientGroup.mk (R.rationalValue x)⁻¹ : D.Space) = QuotientGroup.mk (R.rationalValue y)⁻¹)) ∧
        (letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
          (D.basis.baseChange ℝ)
         ∀ (x y : σ → ℤ) (δ : ℝ), 0 ≤ δ →
           (∀ i, |(x i : ℝ)| ≤ A i) → (∀ i, |(y i : ℝ)| ≤ A i) →
           (∀ i, |(x i : ℝ) - (y i : ℝ)| ≤ A i * δ) →
           dist (R.slowValue x) (R.slowValue y) ≤ Real.exp ((p + C) ^ C) * δ) := by
  obtain ⟨a, _, hcoeff⟩ := exists_native_orbit_coefficient_control
  obtain ⟨b, _, hperiod⟩ := exists_native_rational_period s
  obtain ⟨c, _, hmetric⟩ := exists_polynomialSlowBound_dist_exp s 1
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + Polynomial.C a) ^ a + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Q + Polynomial.C b) ^ b + (Q + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D g eta A p R hp hD hσ hA
  obtain ⟨m, hm, hmb, hgrid, hslow⟩ := hcoeff R hp hD hA
  let q := p + (p + a) ^ a + 2
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have haq : (p + a) ^ a ≤ q := by dsimp [q]; linarith
  have hsum : (q + b) ^ b + (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hbC : (q + b) ^ b ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hcC : (q + c) ^ c ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity)).trans hsum
  obtain ⟨P, hP, hPb, hcosets⟩ := hperiod D (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    q hq (hD.mono D hpq) (hσ.trans hpq) m hm (hmb.trans (Real.exp_le_exp.mpr haq))
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hbC), hcosets R.rational hgrid, ?_⟩
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  intro x y δ hδ hx hy hxy
  have hs := D.filtration.polynomialSlowBound_mono D.basis (fun _ : σ => 1) A hA
    (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith : (p + a) ^ a ≤ (q + 2) ^ 1))
    R.slow hslow
  have hd := hmetric D (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) q hq (hD.mono D hpq)
    (hσ.trans hpq) A hA R.slow hs (fun i => (x i : ℝ)) (fun i => (y i : ℝ)) δ hδ hx hy hxy
  exact hd.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcC) hδ)

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_orbit_factor_freezing (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p →
      ∀ (Φ : D.Space → ℂ) (K : ℝ≥0), (∀ x, ‖Φ x‖ ≤ 1) →
      (letI := D.metricSpace; LipschitzWith K Φ) → (K : ℝ) ≤ Real.exp p →
      ∀ ε b γ g : D.filtration.realification.PolynomialOrbit w,
        ε * b * γ = g → ∀ T : σ → ℝ, (∀ i, 0 < T i) →
        CoefficientBound (D.basis.baseChange ℝ) T (Real.exp ((p + 2) ^ a)) ε.log →
        ∀ (x y : σ → ℤ) (δ : ℝ), 0 ≤ δ →
        (∀ i, |(x i : ℝ)| ≤ T i) → (∀ i, |(y i : ℝ)| ≤ T i) →
        (∀ i, |(x i : ℝ) - y i| ≤ T i * δ) →
        (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x γ) : D.Space) =
          QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w y γ) →
        ‖Φ (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g)) -
          Φ (QuotientGroup.mk
            (D.filtration.realification.polynomialOrbitEval w y ε *
             D.filtration.realification.polynomialOrbitEval w x b *
             D.filtration.realification.polynomialOrbitEval w y γ))‖ ≤
          Real.exp ((p + C) ^ C) * δ := by
  obtain ⟨c, _, hmove⟩ := exists_polynomialSlowBound_dist_exp s a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Polynomial.X + (Polynomial.X + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D w hw p hp hD hσ Φ K hΦ hLip hK ε b γ g hprod T hT hε x y δ hδ hx hy hxy hγ
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let S : D.Niltest w := {
    orbit := g
    observable := Φ
    normBound := 1
    lipBound := K
    norm_le := hΦ
    lipschitz := hLip }
  have hslow := (D.filtration.polynomialSlowBound_iff_formal D.basis w T _
    (D.filtration.realification.polynomialOrbitCoordinates w ε)).mpr hε
  have hdist := hmove D w hw p hp hD hσ T hT
    (D.filtration.realification.polynomialOrbitCoordinates w ε) hslow
    (fun i => (x i : ℝ)) (fun i => (y i : ℝ)) δ hδ hx hy hxy
  simp only [D.filtration.polynomialOrbitCoordinates_realValue] at hdist
  have hfreeze := S.observable_freeze_factors
    (D.filtration.realification.polynomialOrbitEval w x ε)
    (D.filtration.realification.polynomialOrbitEval w y ε)
    (D.filtration.realification.polynomialOrbitEval w x b)
    (D.filtration.realification.polynomialOrbitEval w x γ)
    (D.filtration.realification.polynomialOrbitEval w y γ) hγ
  have hg : D.filtration.realification.polynomialOrbitEval w x g =
      D.filtration.realification.polynomialOrbitEval w x ε *
      D.filtration.realification.polynomialOrbitEval w x b *
      D.filtration.realification.polynomialOrbitEval w x γ := by
    rw [← hprod, map_mul, map_mul]
  rw [hg]
  apply hfreeze.trans
  have hcost : p + (p + c) ^ c ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  calc
    _ ≤ Real.exp p * (Real.exp ((p + c) ^ c) * δ) :=
      mul_le_mul hK hdist dist_nonneg (Real.exp_pos p).le
    _ = Real.exp (p + (p + c) ^ c) * δ := by rw [← mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcost) hδ

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientJetScalar
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

def CoefficientAxisRow (K : Type*) {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ} :
    LayerSamplerAxis I n → Type _
  | ⟨j, .inl _⟩ => BoundedCoefficientExponent K (j.val+1) → ℝ
  | ⟨j, .inr _⟩ => BoundedCoefficientExponent K (j.val+1) → ℤ

instance coefficientAxisRowMeasurable (K : Type*) {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
    (a : LayerSamplerAxis I n) : MeasurableSpace (CoefficientAxisRow K a) :=
  match a with
  | ⟨j, .inl _⟩ => inferInstanceAs (MeasurableSpace (BoundedCoefficientExponent K (j.val+1) → ℝ))
  | ⟨j, .inr _⟩ => inferInstanceAs (MeasurableSpace (BoundedCoefficientExponent K (j.val+1) → ℤ))

abbrev CoefficientAxisArrays (K : Type*) {m : ℕ} (I : Fin m → Type*) (n : Fin m → ℕ) :=
  ∀ a : LayerSamplerAxis I n, CoefficientAxisRow K a

def coefficientAxisEquiv (K : Type*) {m : ℕ} (I : Fin m → Type*) (n : Fin m → ℕ) :
    CoefficientSamplerArrays (K := K) I n ≃ᵐ CoefficientAxisArrays K I n :=
  (MeasurableEquiv.piCongrRight (fun j =>
    (MeasurableEquiv.sumPiEquivProdPi (fun a : I j ⊕ Fin (n j) => CoefficientAxisRow K ⟨j, a⟩)).symm)).trans
      (MeasurableEquiv.piCurry (fun j (a : I j ⊕ Fin (n j)) => CoefficientAxisRow K ⟨j, a⟩)).symm

variable {K : Type*} {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val+1) → ℝ)
variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val+1) → PMF ℤ)

noncomputable def coefficientAxisLaw [Fintype K] :
    ∀ a : LayerSamplerAxis I n, Measure (CoefficientAxisRow K a)
  | ⟨j, .inl i⟩ => Measure.pi (fun d => affineCoefficientMeasure (c j i d) (w j i d))
  | ⟨j, .inr i⟩ => Measure.pi (fun d => (p j i d).toMeasure)

def coefficientAxisSplitEquiv (K : Type*) {m : ℕ} (I : Fin m → Type*) (n : Fin m → ℕ)
    (P : LayerSamplerAxis I n → Prop) [DecidablePred P] :
    CoefficientSamplerArrays (K := K) I n ≃ᵐ
      (∀ a : {a // P a}, CoefficientAxisRow K a.val) ×
        (∀ a : {a // ¬P a}, CoefficientAxisRow K a.val) :=
  (coefficientAxisEquiv K I n).trans (MeasurableEquiv.piEquivPiSubtypeProd (CoefficientAxisRow K) P)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}

def CoefficientJetAxisRow (O : Fin m → Type*) : LayerSamplerAxis I n → Type _
  | ⟨j, .inl _⟩ => O j → ℝ
  | ⟨j, .inr _⟩ => O j → ℤ

instance coefficientJetAxisRowMeasurable (O : Fin m → Type*) (a : LayerSamplerAxis I n) :
    MeasurableSpace (CoefficientJetAxisRow O a) :=
  match a with
  | ⟨j, .inl _⟩ => inferInstanceAs (MeasurableSpace (O j → ℝ))
  | ⟨j, .inr _⟩ => inferInstanceAs (MeasurableSpace (O j → ℤ))

noncomputable def coefficientJetAxisReference (O : Fin m → Type*) [∀ j, Fintype (O j)] :
    ∀ a : LayerSamplerAxis I n, Measure (CoefficientJetAxisRow O a)
  | ⟨j, .inl _⟩ => (volume : Measure (O j → ℝ))
  | ⟨j, .inr _⟩ => (Measure.count : Measure (O j → ℤ))

instance coefficientJetAxisReference_sigmaFinite (O : Fin m → Type*) [∀ j, Fintype (O j)]
    (a : LayerSamplerAxis I n) : SigmaFinite (coefficientJetAxisReference O a) := by
  rcases a with ⟨j, a⟩
  cases a with
  | inl i =>
    change SigmaFinite (volume : Measure (O j → ℝ))
    infer_instance
  | inr i =>
    change SigmaFinite (Measure.count : Measure (O j → ℤ))
    infer_instance

noncomputable def coefficientJetAxisMap {K : Type*} [Fintype K] {O : Fin m → Type*}
    (A : ∀ j, Matrix (O j) (BoundedCoefficientExponent K (j.val+1)) ℤ) :
    ∀ a : LayerSamplerAxis I n, CoefficientAxisRow K a → CoefficientJetAxisRow O a
  | ⟨j, .inl _⟩, c => (A j).map (Int.cast : ℤ → ℝ) *ᵥ c
  | ⟨j, .inr _⟩, c => A j *ᵥ c

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory

variable {m : ℕ} {I O O' : Fin m → Type*} {n : Fin m → ℕ}
variable (e : ∀ j, O' j ≃ O j)

variable [∀ j, Fintype (O j)] [∀ j, Fintype (O' j)]

variable (P : LayerSamplerAxis I n → Prop)

variable [∀ j, Fintype (I j)] [DecidablePred P]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}

def CoefficientJetScalar : LayerSamplerAxis I n → Type
  | ⟨_, .inl _⟩ => ℝ
  | ⟨_, .inr _⟩ => ℤ

instance coefficientJetScalarMeasurable (a : LayerSamplerAxis I n) :
    MeasurableSpace (CoefficientJetScalar a) :=
  match a with
  | ⟨_, .inl _⟩ => inferInstanceAs (MeasurableSpace ℝ)
  | ⟨_, .inr _⟩ => inferInstanceAs (MeasurableSpace ℤ)

noncomputable def coefficientJetScalarReference :
    ∀ a : LayerSamplerAxis I n, Measure (CoefficientJetScalar a)
  | ⟨_, .inl _⟩ => (volume : Measure ℝ)
  | ⟨_, .inr _⟩ => (Measure.count : Measure ℤ)

instance coefficientJetScalarReference_sigmaFinite (a : LayerSamplerAxis I n) :
    SigmaFinite (coefficientJetScalarReference a) := by
  rcases a with ⟨j, i | i⟩
  · change SigmaFinite (volume : Measure ℝ)
    infer_instance
  · change SigmaFinite (Measure.count : Measure ℤ)
    infer_instance

def coefficientJetScalarEquiv (O : Fin m → Type*) (a : LayerSamplerAxis I n) :
    CoefficientJetAxisRow O a ≃ᵐ (O a.1 → CoefficientJetScalar a) :=
  match a with
  | ⟨_, .inl _⟩ => MeasurableEquiv.refl _
  | ⟨_, .inr _⟩ => MeasurableEquiv.refl _

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredMixedArrayImage
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J I : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

variable [∀ j, Fintype (O j)]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J I : Fin m → Type*} [∀ j, Fintype (O j)]
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

noncomputable def canonicalCoefficientJetArrays
    (x : CoefficientSamplerArrays (K := K) I n) :
    ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ) := fun j =>
  mixedArrayIntegerImage (boundedCoefficientJetMatrix root D (j.val + 1) (rows j)) (x j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix

variable {D : Type*} [Fintype D] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)

noncomputable def normalizedLatticeRepresentativeHom : (W × (Fin n → ℤ)) →+ W where
  toFun := normalizedLatticeRepresentative W b hb
  map_zero' := by simp [normalizedLatticeRepresentative]
  map_add' x y := by
    simp only [normalizedLatticeRepresentative, Prod.fst_add, Prod.snd_add,
      map_add, Submodule.coe_add]
    abel

namespace VectorPolynomial

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J I : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (I j)]
variable {ns : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bs : ∀ j, Basis (Fin (ns j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hbs : ∀ j, span ℤ (Set.range (bs j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

end VectorPolynomial

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.JetAxisCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (O I : Fin m → Type*) (n : Fin m → ℕ)

def coefficientJetAxisEquiv :
    (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ≃ᵐ
      (∀ a : LayerSamplerAxis I n, CoefficientJetAxisRow O a) :=
  (MeasurableEquiv.piCongrRight (fun j =>
    (MeasurableEquiv.sumPiEquivProdPi (fun a : I j ⊕ Fin (n j) => CoefficientJetAxisRow O ⟨j, a⟩)).symm)).trans
      (MeasurableEquiv.piCurry (fun j (a : I j ⊕ Fin (n j)) => CoefficientJetAxisRow O ⟨j, a⟩)).symm

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedCoveredChart
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped Classical

variable {D R : Type*} [Fintype D] [Fintype R] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (bW : Basis R ℤ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup)
variable (d : ℕ) [NeZero d]

noncomputable def normalizedCoveredChart (p : (W × (Fin n → ℤ)) × (R → ZMod d)) :
    W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup :=
  normalizedCoverLift W b hb d p.1 +
    (coverKernelBasisEquiv (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
      bW d (Nat.pos_of_ne_zero (NeZero.ne d)) p.2).val

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LayeredCoverSiteExtension
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable (q : ℕ) [NeZero q]

noncomputable def circleQuarterCover (a : ZMod q) (x : ℝ) : UnitAddCircle :=
  ZMod.toAddCircle a + ((x / q : ℝ) : UnitAddCircle)

noncomputable def quarterCoverPoint {D : Type*} (a : D → ZMod q) (x : D → ℝ) :
    D → UnitAddCircle := fun i => circleQuarterCover q (a i) (x i)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix NNReal Classical

variable {D I : Type*} [Fintype D] [DecidableEq D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))
variable (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (q : ℕ) [NeZero q]

omit [DecidableEq D] in
theorem exists_normalized_representative_offset (u : W) (x : W × (Fin n → ℤ))
    (hu : (QuotientAddGroup.mk u : W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) =
      normalizedLatticeQuotient W b hb x) :
    ∃ w : I → ℤ, normalizedLatticeRepresentative W b hb x + (bW.equivFun.symm w).val = u := by
  have hmem : u - normalizedLatticeRepresentative W b hb x ∈
      (latticeSection (standardEuclideanLattice D) W).toAddSubgroup :=
    QuotientAddGroup.eq_iff_sub_mem.mp (hu.trans (normalizedLatticeRepresentative_mk W b hb x).symm)
  let c : latticeSection (standardEuclideanLattice D) W := ⟨u - normalizedLatticeRepresentative W b hb x, hmem⟩
  refine ⟨bW.equivFun c, ?_⟩
  rw [LinearEquiv.symm_apply_apply]
  change _ + (u - _) = u
  abel

end Erdos3

end

section

namespace Erdos3

open Module Submodule

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped NNReal Classical

variable {M : Type*} [Fintype M] {D E : M → Type*}
variable [∀ j, Fintype (D j)] [∀ j, DecidableEq (D j)] [∀ j, Fintype (E j)]
variable {n : M → ℕ}
variable (W : ∀ j, Submodule ℝ (EuclideanSpace ℝ (D j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (D j)) (W j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (W j)ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (W j))
variable (q : ℕ) [NeZero q]

local notation "ambient" => (Σ j : M, D j)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ConstantCenterUniformLifts
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {X Y R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

noncomputable def subtractConstant (c : V) (p : VectorPolynomial X R V) :
    VectorPolynomial X R V := p - monomial 0 c

theorem coefficients_subtractConstant (c : V) (p : VectorPolynomial X R V) (d : X →₀ ℕ) :
    coefficients (subtractConstant c p) d = coefficients p d - if d = 0 then c else 0 := by
  classical
  simp [subtractConstant, Finsupp.single_apply, eq_comm]

theorem eval_subtractConstant (c : V) (p : VectorPolynomial X R V) (x : X → R) :
    eval x (subtractConstant c p) = eval x p - c := by
  simp [subtractConstant]

theorem substitute_subtractConstant (f : X → MvPolynomial Y R) (c : V)
    (p : VectorPolynomial X R V) :
    substitute f (subtractConstant c p) = subtractConstant c (substitute f p) := by
  simp [subtractConstant, monomial]

theorem DegreeLE.subtractConstant {w : X → ℕ} {h : ℕ} {p : VectorPolynomial X R V}
    (hp : DegreeLE w h p) (c : V) : DegreeLE w h (subtractConstant c p) := by
  intro d hd
  have hd0 : d ≠ 0 := by
    intro he
    subst d
    simp at hd
  rw [coefficients_subtractConstant, hp d hd, if_neg hd0, sub_zero]

theorem coefficients_subtractConstant_mem (U : Submodule R V) (c : U)
    (p : VectorPolynomial X R V) (hp : ∀ d, coefficients p d ∈ U) (d : X →₀ ℕ) :
    coefficients (subtractConstant c.val p) d ∈ U := by
  classical
  rw [coefficients_subtractConstant]
  split_ifs
  · exact U.sub_mem (hp d) c.property
  · simpa using hp d

theorem homogeneousPart_subtractConstant {h : ℕ} (hh : 0 < h) (c : V)
    (p : VectorPolynomial X R V) :
    homogeneousPart h (subtractConstant c p) = homogeneousPart h p := by
  classical
  apply coefficients.injective
  ext d
  by_cases hd : d.degree = h
  · have hd0 : d ≠ 0 := by
      intro he
      subst d
      have : h = 0 := by simpa using hd.symm
      omega
    simp only [coefficients_homogeneousPart, hd, ite_true, coefficients_subtractConstant,
      hd0, ite_false, sub_zero]
  · simp only [coefficients_homogeneousPart, hd, ite_false]

theorem hasLayerSamplingRank_subtractConstant_iff {I J : Type*} [Fintype J]
    {h : ℕ} (hh : 0 < h) (T : I → ℝ) (R : ℝ) (U : Submodule ℝ (J → ℝ))
    (c : J → ℝ) (p : VectorPolynomial I ℝ (J → ℝ)) :
    HasLayerSamplingRank h T R U (subtractConstant c p) ↔ HasLayerSamplingRank h T R U p := by
  rw [← hasLayerSamplingRank_homogeneousPart_iff h T R U (subtractConstant c p),
    homogeneousPart_subtractConstant hh, hasLayerSamplingRank_homogeneousPart_iff]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G X : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (L₀ : ℕ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

theorem affineSampleCoefficientArray_subtractConstant {K X : Type*} [Fintype K]
    {m : ℕ} {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (c : ∀ j, U j) (frame : Option K → X → ℝ) :
    affineSampleCoefficientArray U (fun j => subtractConstant (c j).val (p j))
      (fun j => coefficients_subtractConstant_mem (U j) (c j) (p j) (hm j)) frame =
      centeredAffineCoefficientArray U p hm c frame := by
  funext s
  apply Subtype.ext
  simp only [centeredAffineCoefficientArray, Pi.sub_apply, Submodule.coe_sub,
    affineSampleCoefficientArray_val, substitute_subtractConstant, coefficients_subtractConstant]
  by_cases hs : s.2.val = 0
  · simp [constantCoefficientArray, hs]
  · simp [constantCoefficientArray, hs]

theorem affineSampleCoefficientTorus_subtractConstant {K X : Type*} [Fintype K]
    {m : ℕ} {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (c : ∀ j, U j) (frame : Option K → X → ℝ) :
    affineSampleCoefficientTorus U (fun j => subtractConstant (c j).val (p j))
      (fun j => coefficients_subtractConstant_mem (U j) (c j) (p j) (hm j)) frame =
      centeredAffineCoefficientTorus U p hm c frame := by
  exact congrArg (QuotientAddGroup.mk' (coefficientIntegerLattice U))
    (affineSampleCoefficientArray_subtractConstant U p hm c frame)

variable {m : ℕ} {G X : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (L₀ : ℕ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G X : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (L₀ : ℕ)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedKernelEuclideanDensity
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open Polynomial

theorem exists_bounded_residual_cover_budget (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ P : ℝ, 0 ≤ P →
      geometricSiteBudget m q P + ((m : ℝ) + 2) * (geometricSiteBudget m q P + 2) ^ 36 ≤
        (P + A) ^ A := by
  let G : Polynomial ℕ := C (m + 1) * (X + 1) ^ (m + 1) + C (2 ^ q)
  obtain ⟨A, hA, h⟩ := exists_natPolynomial_eval_budget (G + C (m + 2) * (G + 2) ^ 36)
  refine ⟨A, hA, ?_⟩
  intro P hP
  simpa [G, geometricSiteBudget, Polynomial.eval₂_pow, Nat.cast_add] using h P hP

end Erdos3.VectorPolynomial

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

theorem exists_fixed_kernel_bounded_section (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K₀ : Type*} [Fintype K₀]
    (root₀ : K₀ → ℤ) (difference₀ : Fin q → K₀ → ℤ)
    (a : ℤ) (_ha : a ≠ 0)
    (_hperiod : integerScalarLattice (Fin q) a ≤ (Matrix.of difference₀).mulVecLin.range)
    {P : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card K₀ : ℝ) ≤ P)
    (_hsite : ∀ (s : Finset (Fin q)) k,
      |((affineSite root₀ difference₀ s (some k) : ℤ) : ℝ)| ≤ Real.exp P),
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {K : Type*} [Fintype K] (root : K → ℤ) (difference : Fin q → K → ℤ)
    (e : K₀ → K) (_hroot : ∀ k, root (e k) = root₀ k)
    (_hdifference : ∀ i k, difference i (e k) = difference₀ i k),
    ∃ T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) (Finset (Fin q)) ℤ,
      (∀ j s, (∑ i, |(T j i s : ℝ)|) ≤ Real.exp ((P + A) ^ A)) ∧
      ∀ (j : Fin m) {W : Type*} [AddCommGroup W] [Module ℝ W]
        (x : BoundedCoefficientExponent K (j.val + 1) → W),
        let E := boundedSiteMatrix (j.val + 1) (fun s k => affineSite root difference s (some k))
        matrixModuleAction (fun s i => (E s i : ℝ))
          (matrixModuleAction (fun i s => (T j i s : ℝ))
            (matrixModuleAction (fun s i => (E s i : ℝ)) x)) =
          (d : ℝ) • matrixModuleAction (fun s i => (E s i : ℝ)) x := by
  obtain ⟨A, hA, hbudget⟩ := exists_bounded_residual_cover_budget m q
  refine ⟨A, hA, ?_⟩
  intro K₀ _ root₀ difference₀ a ha hperiod P hP hK hsite
  let site₀ := fun s k => affineSite root₀ difference₀ s (some k)
  let E₀ := fun j : Fin m => boundedSiteMatrix (j.val + 1) site₀
  obtain ⟨d, T₀, hd, hT₀, hbound⟩ := exists_bounded_common_site_residual E₀
    (fun _ => exponentialSiteHeight m P) (fun _ => exponentialSiteHeight_pos m P)
    (fun j => boundedSiteMatrix_height_of_exp m (Nat.succ_le_of_lt j.isLt) site₀ hsite)
  let G := geometricSiteBudget m q P
  have hG : 0 ≤ G := geometricSiteBudget_nonneg m q hP
  have hcard (j : Fin m) : (Fintype.card (BoundedCoefficientExponent K₀ (j.val + 1)) : ℝ) ≤ G :=
    boundedCoefficientExponent_card_le_geometricSiteBudget m q (Nat.succ_le_of_lt j.isLt) hP hK
  obtain ⟨hdb, hTb⟩ := hbound hG hcard (cubeSites_card_le_geometricSiteBudget m q hP)
    (fun _ => (exponentialSiteHeight_le m hP).trans
      (Real.exp_le_exp.mpr (degree_mul_le_geometricSiteBudget m q hP)))
  have hcost : G + ((m : ℝ) + 2) * (G + 2) ^ 36 ≤ (P + A) ^ A := hbudget P hP
  have hpow : 0 ≤ (G + 2) ^ 36 := pow_nonneg (by linarith) _
  refine ⟨d, hd, hdb.trans (Real.exp_le_exp.mpr ?_), ?_⟩
  · simp only [Fintype.card_fin]
    nlinarith
  · intro K _ root difference e hroot hdifference
    let site := fun s k => affineSite root difference s (some k)
    have hs : (fun s k => site s (e k)) = site₀ := by
      funext s k
      simp only [site, site₀, affineSite, hroot, hdifference]
    refine ⟨fun j => extendIntegerSiteSection (boundedExponentMap e (j.val + 1)) (T₀ j), ?_, ?_⟩
    · intro j s
      apply (extendIntegerSiteSection_column_sum_bound _ (T₀ j) (hTb j) s).trans
      simp only [Fintype.card_fin]
      calc
        _ ≤ G * Real.exp (((m : ℝ) + 2) * (G + 2) ^ 36) :=
          mul_le_mul_of_nonneg_right (hcard j) (Real.exp_pos _).le
        _ ≤ Real.exp G * Real.exp (((m : ℝ) + 2) * (G + 2) ^ 36) :=
          mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp G]) (Real.exp_pos _).le
        _ = Real.exp (G + ((m : ℝ) + 2) * (G + 2) ^ 36) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr hcost
    · intro j W _ _ x
      have hc : (boundedSiteMatrix (j.val + 1) site).submatrix id (boundedExponentMap e (j.val + 1)) = E₀ j := by
        rw [boundedSiteMatrix_mapDomain, hs]
      obtain ⟨R, hR⟩ := boundedSiteMatrix_fixed_kernel_factor root₀ (Matrix.of difference₀)
        a ha hperiod (j.val + 1) root (Matrix.of difference)
      exact integerSiteResidual_extend_columns (E₀ j) (boundedSiteMatrix (j.val + 1) site)
        (boundedExponentMap e (j.val + 1)) hc R hR (T₀ j) d (hT₀ j) x

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped BigOperators Classical

theorem exists_fixed_kernel_bounded_section_multiple (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K₀ : Type*} [Fintype K₀]
    (root₀ : K₀ → ℤ) (difference₀ : Fin q → K₀ → ℤ)
    (a : ℤ) (_ha : a ≠ 0)
    (_hperiod : integerScalarLattice (Fin q) a ≤ (Matrix.of difference₀).mulVecLin.range)
    {P : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card K₀ : ℝ) ≤ P)
    (_hsite : ∀ (s : Finset (Fin q)) k,
      |((affineSite root₀ difference₀ s (some k) : ℤ) : ℝ)| ≤ Real.exp P),
    ∀ (period : ℕ), 0 < period → (period : ℝ) ≤ Real.exp P →
    ∃ d : ℕ, period ∣ d ∧ 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {K : Type*} [Fintype K] (root : K → ℤ) (difference : Fin q → K → ℤ)
    (e : K₀ → K) (_hroot : ∀ k, root (e k) = root₀ k)
    (_hdifference : ∀ i k, difference i (e k) = difference₀ i k),
    ∃ T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) (Finset (Fin q)) ℤ,
      (∀ j s, (∑ i, |(T j i s : ℝ)|) ≤ Real.exp ((P + A) ^ A)) ∧
      ∀ (j : Fin m) {W : Type*} [AddCommGroup W] [Module ℝ W]
        (x : BoundedCoefficientExponent K (j.val + 1) → W),
        let E := boundedSiteMatrix (j.val + 1) (fun s k => affineSite root difference s (some k))
        matrixModuleAction (fun s i => (E s i : ℝ))
          (matrixModuleAction (fun i s => (T j i s : ℝ))
            (matrixModuleAction (fun s i => (E s i : ℝ)) x)) =
          (d : ℝ) • matrixModuleAction (fun s i => (E s i : ℝ)) x := by
  obtain ⟨A₀, _, hsection⟩ := exists_fixed_kernel_bounded_section m q
  obtain ⟨A, hA, hpoly⟩ := exists_natPolynomial_eval_budget
    (Polynomial.X + (Polynomial.X + Polynomial.C A₀) ^ A₀)
  have hbudget (P : ℝ) (hP : 0 ≤ P) : P + (P + A₀) ^ A₀ ≤ (P + A) ^ A := by
    simpa [Polynomial.eval₂_pow] using hpoly P hP
  refine ⟨A, hA, ?_⟩
  intro K₀ _ root₀ difference₀ a ha hperiod P hP hK hsite period hp hpP
  obtain ⟨d, hd, hdb, hsection⟩ := hsection root₀ difference₀ a ha hperiod hP hK hsite
  have hbound {x : ℝ} (hx : x ≤ Real.exp ((P + A₀) ^ A₀)) :
      period * x ≤ Real.exp ((P + A) ^ A) := by
    calc
      _ ≤ (period : ℝ) * Real.exp ((P + A₀) ^ A₀) :=
        mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _)
      _ ≤ Real.exp P * Real.exp ((P + A₀) ^ A₀) :=
        mul_le_mul_of_nonneg_right hpP (Real.exp_nonneg _)
      _ ≤ _ := by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (hbudget P hP)
  refine ⟨period * d, dvd_mul_right period d, Nat.mul_pos hp hd, ?_, ?_⟩
  · simpa only [Nat.cast_mul] using hbound hdb
  · intro K _ root difference e hroot hdifference
    obtain ⟨T, hTb, hT⟩ := hsection root difference e hroot hdifference
    refine ⟨fun j i s => (period : ℤ) * T j i s, ?_, ?_⟩
    · intro j s
      simp only [Int.cast_mul, Int.cast_natCast, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg period : (0 : ℝ) ≤ period), ← Finset.mul_sum]
      exact hbound (hTb j s)
    · intro j W _ _ x
      dsimp only
      rw [matrixModuleAction_int_smul, map_smul, hT j x, smul_smul, Nat.cast_mul]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped Classical

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EuclideanGraphResidual
namespace OAI

section

namespace Erdos3

variable {σ κ : Type*} [Fintype σ] [Fintype κ]

noncomputable def euclideanDerivativeShiftMap (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) :
    EuclideanSpace ℝ (σ ⊕ κ) →ₗ[ℝ] (σ → ℝ) :=
  (coordinateScaleEquiv T hT).toLinearMap.comp
    ((LinearMap.fst ℝ (σ → ℝ) (κ → ℝ)).comp productEuclideanEquiv.symm.toLinearMap)

omit [Fintype σ] [Fintype κ] in
theorem euclideanDerivativeShiftMap_apply (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (v : EuclideanSpace ℝ (σ ⊕ κ)) (i : σ) :
    euclideanDerivativeShiftMap T hT v i = T i * v (Sum.inl i) := rfl

omit [Fintype σ] [Fintype κ] in
theorem euclideanDerivativeShiftMap_eq_zero_iff (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (v : EuclideanSpace ℝ (σ ⊕ κ)) :
    euclideanDerivativeShiftMap T hT v = 0 ↔ ∀ i : σ, v (Sum.inl i) = 0 := by
  simp only [funext_iff, euclideanDerivativeShiftMap_apply, Pi.zero_apply,
    mul_eq_zero, hT, false_or]

variable (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
  (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (l : ℕ) (hl : 0 < l)

theorem euclideanDerivativeShiftMap_integer (v : EuclideanSpace ℝ (σ ⊕ κ))
    (hv : v ∈ euclideanDerivativeLattice T hT scale hscale Y A l hl) :
    euclideanDerivativeShiftMap T hT v ∈ realIntegerGrid := by
  have hv' := (euclideanDerivativeLattice_mem_iff T hT scale hscale Y A l hl v).mp hv
  obtain ⟨h, z, hz⟩ := (derivativeLattice_mem_iff T hT scale hscale Y A l hl _).mp hv'
  refine ⟨h, ?_⟩
  funext i
  change (h i : ℝ) = T i * (productEuclideanEquiv.symm v).1 i
  rw [hz, derivativeLatticeEquiv_apply]
  exact (mul_div_cancel₀ (h i : ℝ) (hT i)).symm

theorem euclideanDerivative_vertical_lattice_full (R : ℝ) :
    let Λ := euclideanDerivativeLattice T hT scale hscale Y A l hl
    let Z := shortVectorSpan Λ R
    IsZLattice ℝ (latticeKernel (shortVectorLattice Λ R)
      ((euclideanDerivativeShiftMap T hT).comp Z.subtype)) := by
  apply latticeKernel_full
  intro x hx
  exact euclideanDerivativeShiftMap_integer T hT scale hscale Y A l hl x.val hx

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem euclidean_graph_residual_mem_kernel
    {σ κ : Type*} [Fintype σ] [Fintype κ]
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (G : (σ → ℝ) →ₗ[ℝ] Z) (hG : ∀ y i, (G y).val (Sum.inl i) = y i) (x : Z) :
    x - G (fun i => x.val (Sum.inl i)) ∈
      LinearMap.ker ((euclideanDerivativeShiftMap T hT).comp Z.subtype) := by
  change euclideanDerivativeShiftMap T hT
    ((x - G (fun i => x.val (Sum.inl i))).val) = 0
  apply (euclideanDerivativeShiftMap_eq_zero_iff T hT _).mpr
  intro i
  change x.val (Sum.inl i) - (G (fun j => x.val (Sum.inl j))).val (Sum.inl i) = 0
  rw [hG, sub_self]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DerivativeVerticalCoordinates
namespace OAI

section

namespace Erdos3

noncomputable def euclideanVerticalMap {σ κ : Type*}
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) :
    (κ → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (σ ⊕ κ) :=
  productEuclideanEquiv.toLinearMap.comp ((LinearMap.inr ℝ (σ → ℝ) (κ → ℝ)).comp
    ((coordinateScaleEquiv scale hscale).toLinearMap.comp A.toLinearMap))

@[simp] theorem euclideanVerticalMap_apply_inl {σ κ : Type*}
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (x : κ → ℝ) (i : σ) :
    euclideanVerticalMap (σ := σ) scale hscale A x (Sum.inl i) = 0 := rfl

@[simp] theorem euclideanVerticalMap_apply_inr {σ κ : Type*}
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (x : κ → ℝ) (j : κ) :
    euclideanVerticalMap (σ := σ) scale hscale A x (Sum.inr j) = scale j * A x j := rfl

theorem euclideanDerivative_vertical_grid_coordinates
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ]
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (v : EuclideanSpace ℝ (σ ⊕ κ))
    (hv : v ∈ euclideanDerivativeLattice T hT scale hscale Y A l hl)
    (hzero : euclideanDerivativeShiftMap T hT v = 0) :
    ∃ r : κ → ℝ, r ∈ realDenominatorGrid l ∧ v = euclideanVerticalMap scale hscale A r := by
  have hv' := (euclideanDerivativeLattice_mem_iff T hT scale hscale Y A l hl v).mp hv
  rw [← SetLike.mem_coe, derivativeLattice_carrier] at hv'
  obtain ⟨h, r, hr, he⟩ := hv'
  have hh : h = 0 := by
    funext i
    have hi := congrFun hzero i
    change T i * (productEuclideanEquiv.symm v).1 i = 0 at hi
    rw [he] at hi
    change T i * ((h i : ℝ) / T i) = 0 at hi
    rw [mul_div_cancel₀ _ (hT i)] at hi
    exact_mod_cast hi
  subst h
  refine ⟨-r, realDenominatorGrid_neg l hr, ?_⟩
  apply productEuclideanEquiv.symm.injective
  rw [he]
  change derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) 0 r =
    (0, fun j => scale j * A (-r) j)
  simp only [derivativeGridPoint, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe,
    Pi.zero_apply, Int.cast_zero]
  change ((fun i : σ => (0 : ℝ) / T i),
    fun j => scale j * (Y (0 : σ → ℝ) - A r) j) = (0, fun j => scale j * A (-r) j)
  simp only [map_zero, zero_sub, map_neg, Pi.neg_apply, zero_div]
  rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.DerivativeLatticeDivision
namespace OAI

section

namespace Erdos3

theorem realDenominatorGrid_div_nat {ι : Type*} (l I : ℕ) (hI : 0 < I)
    (x : ι → ℝ) (hx : x ∈ realDenominatorGrid l) :
    ((I : ℝ)⁻¹ • x) ∈ realDenominatorGrid (l * I) := by
  have hIr : (I : ℝ) ≠ 0 := by exact_mod_cast hI.ne'
  obtain ⟨z, hz⟩ := hx
  refine ⟨z, ?_⟩
  funext i
  have hi := congrFun hz i
  change (z i : ℝ) = (l : ℝ) * x i at hi
  change (z i : ℝ) = ((l * I : ℕ) : ℝ) * ((I : ℝ)⁻¹ * x i)
  rw [hi, Nat.cast_mul]
  field_simp

theorem divided_derivative_lattice_coordinates
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ]
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hs : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (I : ℕ) (hI : 0 < I) (y : σ → ℝ)
    (v : EuclideanSpace ℝ (σ ⊕ κ))
    (hv : v ∈ euclideanDerivativeLattice T hT scale hs Y A l hl)
    (hshift : euclideanDerivativeShiftMap T hT v = (I : ℝ) • y) :
    ∃ r : κ → ℝ, r ∈ realDenominatorGrid (l * I) ∧
      ∀ j, ((I : ℝ)⁻¹ • v) (Sum.inr j) = scale j * (Y y j - A r j) := by
  have hIr : (I : ℝ) ≠ 0 := by exact_mod_cast hI.ne'
  have hv' := (euclideanDerivativeLattice_mem_iff T hT scale hs Y A l hl v).mp hv
  rw [← SetLike.mem_coe, derivativeLattice_carrier] at hv'
  obtain ⟨h, r, hr, he⟩ := hv'
  have hleft (i) : v (Sum.inl i) = (h i : ℝ) / T i :=
    congrArg (fun x : (σ → ℝ) × (κ → ℝ) => x.1 i) he
  have hright (j) : v (Sum.inr j) =
      scale j * (Y (fun i => (h i : ℝ)) j - A r j) := by
    have hc := congrArg (fun x : (σ → ℝ) × (κ → ℝ) => x.2 j) he
    change (productEuclideanEquiv.symm v).2 j = _
    simpa only [derivativeGridPoint, LinearMap.toMatrix'_mulVec,
      LinearEquiv.coe_coe, Pi.sub_apply] using hc
  have hh : (fun i => (h i : ℝ)) = (I : ℝ) • y := by
    funext i
    have hi := congrFun hshift i
    change T i * v (Sum.inl i) = (I : ℝ) * y i at hi
    rw [hleft, mul_div_cancel₀ _ (hT i)] at hi
    exact hi
  refine ⟨(I : ℝ)⁻¹ • r, realDenominatorGrid_div_nat l I hI r hr, ?_⟩
  intro j
  change (I : ℝ)⁻¹ * v (Sum.inr j) = _
  rw [hright, hh, map_smul, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

theorem divided_derivative_horizontal_coordinates
    {σ κ : Type*} [Fintype σ] [Fintype κ]
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (I : ℕ) (hI : 0 < I)
    (y : σ → ℝ) (v : EuclideanSpace ℝ (σ ⊕ κ))
    (hshift : euclideanDerivativeShiftMap T hT v = (I : ℝ) • y) :
    ∀ i, ((I : ℝ)⁻¹ • v) (Sum.inl i) = y i / T i := by
  have hIr : (I : ℝ) ≠ 0 := by exact_mod_cast hI.ne'
  intro i
  have hi := congrFun hshift i
  change T i * v (Sum.inl i) = (I : ℝ) * y i at hi
  have hv : v (Sum.inl i) = ((I : ℝ) * y i) / T i :=
    (eq_div_iff (hT i)).mpr (by simpa only [mul_comm] using hi)
  change (I : ℝ)⁻¹ * v (Sum.inl i) = _
  rw [hv]
  field_simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateMinorCovolume
namespace OAI

section

namespace Erdos3

open RealInnerProductSpace

theorem exterior_norm_eq_sqrt_gram {r : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (v : Fin r → E) :
    ‖exteriorPower.ιMulti ℝ r v‖ = Real.sqrt (Matrix.gram ℝ v).det := by
  have hs : ‖exteriorPower.ιMulti ℝ r v‖ ^ 2 = (Matrix.gram ℝ v).det := by
    rw [← real_inner_self_eq_norm_sq]
    exact exteriorPower.inner_ιMulti_self v
  rw [← hs, Real.sqrt_sq (norm_nonneg _)]

theorem abs_coordinate_det_le_sqrt_gram {r : ℕ} {ι : Type*} [Fintype ι]
    (v : Fin r → EuclideanSpace ℝ ι) (p : Fin r → ι) (hp : Function.Injective p) :
    |(Matrix.of (fun i j => v i (p j))).det| ≤ Real.sqrt (Matrix.gram ℝ v).det := by
  classical
  let e : Fin r → EuclideanSpace ℝ ι := fun i => EuclideanSpace.single (p i) 1
  let u := exteriorPower.ιMulti ℝ r e
  let w := exteriorPower.ιMulti ℝ r v
  have he : Orthonormal ℝ e := EuclideanSpace.orthonormal_single.comp p hp
  have hgram : Matrix.gram ℝ e = 1 := Matrix.gram_eq_one_iff_orthonormal.mpr he
  have hu : ‖u‖ = 1 := by
    have hs : ‖u‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      change inner ℝ (exteriorPower.ιMulti ℝ r e) (exteriorPower.ιMulti ℝ r e) = 1
      rw [exteriorPower.inner_ιMulti_self, hgram, Matrix.det_one]
    nlinarith [norm_nonneg u]
  have hi : inner ℝ u w = (Matrix.of (fun i j => v i (p j))).det := by
    change inner ℝ (exteriorPower.ιMulti ℝ r e) (exteriorPower.ιMulti ℝ r v) = _
    rw [exteriorPower.inner_ιMulti_ιMulti]
    congr 1
    ext i j
    simp [e, EuclideanSpace.inner_single_left]
  have h := abs_real_inner_le_norm u w
  rw [hi, hu, one_mul] at h
  exact h.trans_eq (exterior_norm_eq_sqrt_gram v)

theorem abs_isometric_lattice_basis_det_le_covolume {r : ℕ} {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin r) ℤ Λ) (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (p : Fin r → ι) (hp : Function.Injective p) :
    |(Matrix.of (fun i j => f (b i).val (p j))).det| ≤ ZLattice.covolume Λ := by
  have hs : ZLattice.covolume Λ ^ 2 =
      (Matrix.gram ℝ (fun i : Fin r => f (b i).val)).det := by
    rw [lattice_covolume_sq_eq_gram Λ b]
    congr 1
    ext i j
    simp only [Matrix.gram_apply, Module.Basis.ofZLatticeBasis_apply, LinearIsometry.inner_map_map]
  have h := abs_coordinate_det_le_sqrt_gram (fun i : Fin r => f (b i).val) p hp
  rw [← hs, Real.sqrt_sq (ZLattice.covolume_pos Λ MeasureTheory.volume).le] at h
  exact h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.EuclideanLatticeGraph
namespace OAI

section

namespace Erdos3

theorem euclidean_shift_subspace_surjective
    {σ κ : Type*} [Fintype σ] [Fintype κ]
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (hproj : Z.map ((LinearMap.fst ℝ (σ → ℝ) (κ → ℝ)).comp
      productEuclideanEquiv.symm.toLinearMap) = ⊤) :
    Function.Surjective ((euclideanDerivativeShiftMap T hT).comp Z.subtype) := by
  have hmap : Z.map (euclideanDerivativeShiftMap T hT) = ⊤ := by
    change Z.map ((coordinateScaleEquiv T hT).toLinearMap.comp
      ((LinearMap.fst ℝ (σ → ℝ) (κ → ℝ)).comp productEuclideanEquiv.symm.toLinearMap)) = ⊤
    rw [Submodule.map_comp, hproj, Submodule.map_top]
    exact (coordinateScaleEquiv T hT).range
  intro x
  have hx : x ∈ Z.map (euclideanDerivativeShiftMap T hT) := by rw [hmap]; trivial
  obtain ⟨v, hv, he⟩ := hx
  exact ⟨⟨v, hv⟩, he⟩

theorem exists_euclidean_lattice_graph_identity
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ]
    (Z : Submodule ℝ (EuclideanSpace ℝ (σ ⊕ κ)))
    (Λ : Submodule ℤ Z) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (hinteger : ∀ x ∈ Λ,
      euclideanDerivativeShiftMap T (fun i => (hT i).ne') x.val ∈ realIntegerGrid)
    (hsurj : Function.Surjective
      ((euclideanDerivativeShiftMap T (fun i => (hT i).ne')).comp Z.subtype)) :
    let π : Z →ₗ[ℝ] (σ → ℝ) :=
      (euclideanDerivativeShiftMap T (fun i => (hT i).ne')).comp Z.subtype
    ∃ G : (σ → ℝ) →ₗ[ℝ] Z,
      (∀ y i, (G y).val (Sum.inl i) = y i) ∧
      (∀ x : Z, G (fun i => x.val (Sum.inl i)) = x - (LinearMap.ker π).starProjection x) ∧
      ZLattice.covolume Λ = ZLattice.covolume (latticeKernel Λ π)
        (MeasureTheory.volume (α := LinearMap.ker π)) *
        (((latticeImage Λ π).toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup : ℝ) /
          ∏ i, T i) *
        Real.sqrt (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i))).det := by
  let π := (euclideanDerivativeShiftMap T (fun i => (hT i).ne')).comp Z.subtype
  obtain ⟨G, hright, hsection, hcov⟩ :=
    exists_scaled_lattice_covolume_identity Λ π hinteger hsurj T hT
  refine ⟨G, ?_, ?_, hcov⟩
  · intro y i
    have he := congrFun (hright y) i
    change T i * (G y).val (Sum.inl i) = T i * y i at he
    exact mul_left_cancel₀ (hT i).ne' he
  · intro x
    have he : (fun i => π x i / T i) = fun i => x.val (Sum.inl i) := by
      funext i
      exact mul_div_cancel_left₀ _ (hT i).ne'
    simpa only [he] using hsection x

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeMinorNormBound
namespace OAI

section

namespace Erdos3

theorem lattice_projection_all_minors_bound {ι κ E : Type*} [Fintype ι] {k : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin k) ℤ Λ) (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (e : κ → ι) (he : Function.Injective e)
    (H : Matrix κ (Fin k) ℝ) (hH : ∀ i j, H i j = f (b j).val (e i)) :
    ∀ q : Fin k → κ, |(H.submatrix q id).det| ≤ ZLattice.covolume Λ := by
  intro q
  by_cases hq : Function.Injective q
  · have h := abs_isometric_lattice_basis_det_le_covolume Λ b f (e ∘ q) (he.comp hq)
    have hm : Matrix.of (fun i j => f (b i).val ((e ∘ q) j)) =
        (H.submatrix q id).transpose := by
      ext i j
      exact (hH (q j) i).symm
    simpa only [hm, Matrix.det_transpose] using h
  · have hd : (H.submatrix q id).det = 0 := by
      by_contra hd
      exact hq (nonzero_row_minor_injective H q hd)
    rw [hd, abs_zero]
    exact (ZLattice.covolume_pos Λ MeasureTheory.volume).le

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem lattice_norm_le_selected_coordinates {ι E : Type*} [Fintype ι] {k : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin k) ℤ Λ) (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (p : Fin k → ι)
    (hp : (Matrix.of (fun i j => f (b j).val (p i))).det ≠ 0)
    (C D : ℝ) (hD : 0 < D) (hC : ZLattice.covolume Λ ≤ C)
    (hlower : 1 / D ≤ |(Matrix.of (fun i j => f (b j).val (p i))).det|)
    (x : E) :
    ‖x‖ ≤ (Fintype.card ι : ℝ) * k * (C * D) * ‖fun j => f x (p j)‖ := by
  let bR := b.ofZLatticeBasis ℝ Λ
  let g := (EuclideanSpace.equiv ι ℝ).toLinearMap.comp f.toLinearMap
  let F := Matrix.of (fun i j => g (bR j) i)
  have hF (i j) : F i j = f (b j).val i := by
    simp only [F, Matrix.of_apply, bR, Module.Basis.ofZLatticeBasis_apply]
    rfl
  have hminor : ∀ q : Fin k → ι, |(F.submatrix q id).det| ≤ C := by
    intro q
    exact (lattice_projection_all_minors_bound Λ b f id Function.injective_id F hF q).trans hC
  have hp' : (F.submatrix p id).det ≠ 0 := by
    have he : F.submatrix p id = Matrix.of (fun i j => f (b j).val (p i)) := by
      ext i j
      exact hF (p i) j
    rwa [he]
  have hlower' : 1 / D ≤ |(F.submatrix p id).det| := by
    have he : F.submatrix p id = Matrix.of (fun i j => f (b j).val (p i)) := by
      ext i j
      exact hF (p i) j
    rwa [he]
  have hC0 : 0 ≤ C := (ZLattice.covolume_pos Λ MeasureTheory.volume).le.trans hC
  have hbound := euclidean_matrix_mulVec_norm_le (F * (F.submatrix p id)⁻¹)
    (C * D) (mul_nonneg hC0 hD.le)
    (row_normalization_abs_le F p hp' C D hD hminor hlower') (fun j => f x (p j))
  have hreconstruct :
      (F * (F.submatrix p id)⁻¹) *ᵥ (fun j => f x (p j)) = g x :=
    basis_image_reconstruct_from_minor bR g p hp' x
  have he : (EuclideanSpace.equiv ι ℝ).symm
      ((F * (F.submatrix p id)⁻¹) *ᵥ (fun j => f x (p j))) = f x := by
    rw [hreconstruct]
    exact (EuclideanSpace.equiv ι ℝ).symm_apply_apply (f x)
  rw [he, f.norm_map] at hbound
  exact hbound

theorem lattice_norm_le_projection_of_grid_minor
    {ι κ E : Type*} [Fintype ι] [Fintype κ] {k : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin k) ℤ Λ) (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (e : κ → ι) (l : ℕ) (hl : 0 < l) (B : Matrix κ (Fin k) ℝ)
    (hB : ∀ i j, B i j = f (b j).val (e i))
    (hgrid : ∀ j, B.col j ∈ realDenominatorGrid l)
    (p : Fin k → κ) (hp : (B.submatrix p id).det ≠ 0)
    (C : ℝ) (hC : ZLattice.covolume Λ ≤ C) (x : E) :
    ‖x‖ ≤ (Fintype.card ι : ℝ) * k * (C * (l : ℝ) ^ k) *
      ‖fun i => f x (e i)‖ := by
  let M := B.submatrix p id
  have hm : Matrix.of (fun i j => f (b j).val ((e ∘ p) i)) = M := by
    ext i j
    exact (hB (p i) j).symm
  have hMgrid (j) : (fun i => M i j) ∈ realDenominatorGrid l := by
    obtain ⟨z, hz⟩ := hgrid j
    refine ⟨fun i => z (p i), ?_⟩
    funext i
    exact congrFun hz (p i)
  have hMlower : 1 / (l : ℝ) ^ k ≤ |M.det| := by
    simpa only [Fintype.card_fin] using one_div_pow_le_abs_grid_det M l hl hMgrid hp
  have hp' : (Matrix.of (fun i j => f (b j).val ((e ∘ p) i))).det ≠ 0 := by rwa [hm]
  have hlower : 1 / (l : ℝ) ^ k ≤
      |(Matrix.of (fun i j => f (b j).val ((e ∘ p) i))).det| := by rwa [hm]
  have hn := lattice_norm_le_selected_coordinates Λ b f (e ∘ p) hp' C ((l : ℝ) ^ k)
    (pow_pos (by exact_mod_cast hl) _) hC hlower x
  have hr : ‖fun j => f x ((e ∘ p) j)‖ ≤ ‖fun i => f x (e i)‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    exact norm_le_pi_norm (fun i => f x (e i)) (p j)
  have hC0 : 0 ≤ C := (ZLattice.covolume_pos Λ MeasureTheory.volume).le.trans hC
  exact hn.trans (mul_le_mul_of_nonneg_left hr (by positivity))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable (rows : ∀ j, O j → Finset α)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable (rows : ∀ j, O j → Finset α)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

structure AllocatedComparisonDimensions (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] (D : ℝ) : Prop where
  nonneg : 0 ≤ D
  degree : (m : ℝ) ≤ D
  kernel_variables : (Fintype.card G : ℝ) ≤ D
  cube : (Fintype.card α : ℝ) ≤ D
  axes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D
  tuples : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ D
  parameters : (Fintype.card (JointBlockParameter B (layerSamplerDegree I n) α) : ℝ) ≤ D
  outputs : (Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) : ℝ) ≤ D
  rows : ∀ j, (Fintype.card (O j) : ℝ) ≤ D
  coefficients : ∀ j : Fin m,
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ D
  profile : (probabilityProfileLipschitz : ℝ) ≤ D

variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)] {D : ℝ}

theorem AllocatedComparisonDimensions.layer_degree
    (h : AllocatedComparisonDimensions (G := G) B α O D) (j : Fin m) :
    ((j.val+1 : ℕ) : ℝ) ≤ D :=
  (Nat.cast_le.mpr (Nat.succ_le_of_lt j.isLt)).trans h.degree

section Envelopes

variable {A : Type*} [Semiring A]

def allocatedKernelEnvelope (m : ℕ) (D p : A) : A :=
  p+(m*2^(m+1) : ℕ)*p+D*(m+1)+m*kernelInverseEnvelope D p

def allocatedDensityEnvelope (m : ℕ) (D p : A) : A :=
  1+m*kernelOutputEnvelope D (4*(p+8))+p+m*(D+3*D*D+D*(D+1))

def allocatedSupportEnvelope (m : ℕ) (D p : A) : A :=
  allocatedDensityEnvelope m D p+p+m*(D+D*(D+1))

def allocatedFrontEnvelope (m : ℕ) (D p e : A) : A :=
  let C := allocatedKernelEnvelope m D p+D+(D+D+(D+1)*(4*(p+8)))
  2*D^2+(2*D+4)*C+(D+2*D)*(C+4)+4+e+1

end Envelopes

theorem allocatedDensityEnvelope_nonneg (m : ℕ) {D p : ℝ} (hD : 0 ≤ D) (hp : 0 ≤ p) :
    0 ≤ allocatedDensityEnvelope m D p := by
  have ho := kernelOutputEnvelope_nonneg hD (show 0 ≤ 4*(p+8) by positivity)
  unfold allocatedDensityEnvelope
  positivity

theorem allocatedSupportEnvelope_nonneg (m : ℕ) {D p : ℝ} (hD : 0 ≤ D) (hp : 0 ≤ p) :
    0 ≤ allocatedSupportEnvelope m D p := by
  have hd := allocatedDensityEnvelope_nonneg m hD hp
  unfold allocatedSupportEnvelope
  positivity

variable (h : AllocatedComparisonDimensions (G := G) B α O D) {p e : ℝ} (hp : 0 ≤ p)

include h hp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def comparisonProfileBound : ℕ := ⌈(probabilityProfileLipschitz : ℝ)⌉₊+1

noncomputable def allocatedComparisonDimension {A : Type*} [Semiring A] (m : ℕ) (p : A) : A :=
  (m+1 : ℕ)+p+((m+1 : ℕ)*(p+1)^(m+1)+1)+(2^(m+1) : ℕ)+
    (m+2 : ℕ)*p+(2*m : ℕ)*p+(2*m : ℕ)*p*(2^(m+1) : ℕ)+comparisonProfileBound

theorem allocatedComparisonDimension_bounds (m : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    let D := allocatedComparisonDimension m p
    0 ≤ D ∧ ((m+1 : ℕ) : ℝ) ≤ D ∧ p ≤ D ∧ ((2^(m+1) : ℕ) : ℝ) ≤ D ∧
      geometricSiteBudget m 0 p ≤ D ∧ ((m+2 : ℕ) : ℝ)*p ≤ D ∧
      ((2*m : ℕ) : ℝ)*p ≤ D ∧ ((2*m : ℕ) : ℝ)*p*(2^(m+1) : ℕ) ≤ D ∧
      (comparisonProfileBound : ℝ) ≤ D := by
  have hC : 0 ≤ ((m+1 : ℕ) : ℝ)*(p+1)^(m+1)+1 := by positivity
  have hpa : 0 ≤ ((m+2 : ℕ) : ℝ)*p := by positivity
  have ha : 0 ≤ ((2*m : ℕ) : ℝ)*p := by positivity
  have ho : 0 ≤ ((2*m : ℕ) : ℝ)*p*(2^(m+1) : ℕ) := by positivity
  have hm : (0 : ℝ) ≤ (m+1 : ℕ) := Nat.cast_nonneg _
  have hq : (0 : ℝ) ≤ (2^(m+1) : ℕ) := Nat.cast_nonneg _
  have hf : (0 : ℝ) ≤ comparisonProfileBound := Nat.cast_nonneg _
  dsimp only [allocatedComparisonDimension]
  simp only [geometricSiteBudget, pow_zero]
  push_cast at *
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedPrincipalIndex_card_le_variables :
    Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) ≤
      Fintype.card (LayerSamplerVariables G I n B) := by
  change _ ≤ Fintype.card (G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n))
  rw [Fintype.card_sum]
  omega

theorem allocatedKernelVariables_card_le_variables :
    Fintype.card G ≤ Fintype.card (LayerSamplerVariables G I n B) := by
  change _ ≤ Fintype.card (G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n))
  rw [Fintype.card_sum]
  omega

theorem allocatedJointParameter_card (α : Type*) [Fintype α] :
    Fintype.card (JointBlockParameter B (layerSamplerDegree I n) α) =
      Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n))*(Fintype.card α+1) := by
  simp only [JointBlockParameter, BlockParameter, PrincipalTupleIndex, Fintype.card_sigma,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_option]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem allocatedAxes_card_le {p : ℝ}
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p) :
    (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ ((2*m : ℕ) : ℝ)*p := by
  calc
    _ = ∑ j : Fin m, ((Fintype.card (I j) : ℝ)+(n j : ℝ)) := by
      simp only [LayerSamplerAxis, Fintype.card_sigma, Fintype.card_sum, Fintype.card_fin,
        Nat.cast_sum, Nat.cast_add]
    _ ≤ ∑ _ : Fin m, (p+p) := Finset.sum_le_sum (fun j _ => add_le_add (hI j) (hn j))
    _ = _ := by simp; ring

theorem allocatedComparisonDimensions_of_primitive
    {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset α) (hq : Fintype.card α ≤ m+1)
    (hinj : ∀ j, Function.Injective (rows j)) {p : ℝ} (hp : 0 ≤ p)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p) :
    AllocatedComparisonDimensions (G := G) B α O (allocatedComparisonDimension m p) := by
  obtain ⟨hD, hm, hpD, hqD, hCD, hpaD, haD, hoD, hfD⟩ := allocatedComparisonDimension_bounds m hp
  have hqreal : (Fintype.card α : ℝ) ≤ (m+1 : ℕ) := Nat.cast_le.mpr hq
  have hrow (j : Fin m) : Fintype.card (O j) ≤ 2^(m+1) := by
    have hc := Fintype.card_le_of_injective (rows j) (hinj j)
    rw [Fintype.card_finset] at hc
    exact hc.trans (Nat.pow_le_pow_right (by omega) hq)
  have htuple : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (allocatedPrincipalIndex_card_le_variables (G := G) B)).trans hK
  have haxes := allocatedAxes_card_le (I := I) (n := n) hI hn
  refine ⟨hD, (Nat.cast_le.mpr (Nat.le_succ m)).trans hm,
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans (hK.trans hpD),
    hqreal.trans hm, haxes.trans haD, htuple.trans hpD, ?_, ?_,
    fun j => (Nat.cast_le.mpr (hrow j)).trans hqD, ?_, ?_⟩
  · rw [allocatedJointParameter_card, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    apply le_trans _ hpaD
    calc
      _ ≤ p*((m+1 : ℕ)+1) :=
        mul_le_mul htuple (by linarith) (by positivity) hp
      _ = _ := by push_cast; ring
  · apply le_trans _ hoD
    calc
      _ = ∑ a : LayerSamplerAxis I n, (Fintype.card (O a.1) : ℝ) := by
        simp only [Fintype.card_sigma, Nat.cast_sum]
      _ ≤ ∑ _ : LayerSamplerAxis I n, ((2^(m+1) : ℕ) : ℝ) :=
        Finset.sum_le_sum (fun a _ => Nat.cast_le.mpr (hrow a.1))
      _ = (Fintype.card (LayerSamplerAxis I n) : ℝ)*(2^(m+1) : ℕ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right haxes (Nat.cast_nonneg _)
  · intro j
    exact (boundedCoefficientExponent_card_le_geometricSiteBudget m 0
      (Nat.succ_le_of_lt j.isLt) hp hK).trans hCD
  · apply le_trans _ hfD
    exact (Nat.le_ceil _).trans (by unfold comparisonProfileBound; push_cast; linarith)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators

def allocatedWitnessScaleLog (P Qw : ℝ) : ℝ :=
  allocatedScaleLog P + P ^ 2 * Qw

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, IsEmpty (I j)]
variable {n : Fin m → ℕ} [∀ j, IsEmpty (Fin (n j))]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

include U b o

theorem allocatedAmbientDimension_eq (j : Fin m) :
    Fintype.card (I j) + n j = Fintype.card (J j) := by
  have h := (euclideanSubspace (U j)).finrank_add_finrank_orthogonal
  rw [finrank_eq_card_basis (o j).toBasis, finrank_eq_card_basis (b j), finrank_euclideanSpace] at h
  simpa only [Fintype.card_fin] using h

theorem allocatedAmbientDimension_le_axes (j : Fin m) :
    Fintype.card (J j) ≤ Fintype.card (LayerSamplerAxis I n) := by
  rw [← allocatedAmbientDimension_eq U b o j]
  have h := Finset.single_le_sum (f := fun i : Fin m => Fintype.card (I i ⊕ Fin (n i)))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  simpa only [LayerSamplerAxis, Fintype.card_sigma, Fintype.card_sum, Fintype.card_fin] using h

theorem allocatedLatticeDimension_eq
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (j : Fin m) : Fintype.card (Q j) = Fintype.card (I j) := by
  have h := standardLatticeCoordinates_card (euclideanSubspace (U j)) (bW j) (b j) (hb j)
  rw [Fintype.card_sum, Fintype.card_fin, ← allocatedAmbientDimension_eq U b o j] at h
  omega

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.NiltestConjugateFrequency
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem realifyFunctional_neg {V : Type*} [AddCommGroup V] [Module ℚ V]
    (eta : V →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] V) :
    realifyFunctional (-eta) x = -realifyFunctional eta x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp only [realifyFunctional_tmul, LinearMap.neg_apply, Rat.cast_neg, mul_neg]
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem conjugate_vertical (T : D.Niltest w) (eta : L →ₗ[ℚ] ℚ)
    (hvert : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
      T.observable (z • x) = CircleFourier.character
        ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * T.observable x)
    (z : D.RealGroup) (hz : z ∈ D.filtration.realification.subgroup s) (x : D.Space) :
    T.conjugate.observable (z • x) = CircleFourier.character
      ((realifyFunctional (-eta) z.coord : ℝ) : CircleFourier.Circle) * T.conjugate.observable x := by
  change star (T.observable (z • x)) = _ * star (T.observable x)
  rw [hvert z hz x, star_mul, realifyFunctional_neg, AddCircle.coe_neg, CircleFourier.character_neg]
  exact mul_comm _ _

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestOrbitOne
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def oneOnOrbit (T : D.Niltest w) : D.Niltest w where
  orbit := T.orbit
  observable := fun _ => 1
  normBound := 1
  lipBound := 0
  norm_le _ := by simp
  lipschitz := by
    let := D.metricSpace
    exact LipschitzWith.const 1

theorem oneOnOrbit_eval (T : D.Niltest w) (x : σ → ℤ) : T.oneOnOrbit.eval x = 1 := rfl

theorem oneOnOrbit_complexity (T : D.Niltest w) {p : ℝ} (hp : 2 ≤ p)
    (hD : D.GeometryComplexityLE p) : T.oneOnOrbit.ComplexityLE p := by
  refine ⟨hD, ?_⟩
  change Real.log (2 + 1 + 0) ≤ p
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  norm_num at h ⊢
  linarith

theorem oneOnOrbit_vertical (T : D.Niltest w) (z : D.RealGroup) (x : D.Space) :
    T.oneOnOrbit.observable (z • x) =
      CircleFourier.character ((realifyFunctional (0 : L →ₗ[ℚ] ℚ) z.coord : ℝ) : CircleFourier.Circle) *
        T.oneOnOrbit.observable x := by
  simp only [oneOnOrbit, realifyFunctional_zero, AddCircle.coe_zero,
    CircleFourier.character_zero, mul_one]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

end


