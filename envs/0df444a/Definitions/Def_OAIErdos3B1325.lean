-- Prove2me | Definitions.Def_OAIErdos3B1325
-- name    : OAIErdos3B1325
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T17:43:12.197996+00:00
-- url     : https://prove2.me/theorems/4697e168-1396-430f-b70c-348102f28113
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1326 of 1330
-- statement:
--   Definitions bundle 1326 of 1330 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1324`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1326 available.
--
--   Modules: `OAI.Erdos3.BooleanCubeKernel.integerSelfSiteTest`, `OAI.Erdos3.BooleanCubeKernel.integerSelfSiteTest_norm_le`, `OAI.Erdos3.BooleanCubeKernel.physical_twisted_cube_mean`, `OAI.Erdos3.BooleanCubeKernel.physical_twisted_cube_product`, `OAI.Erdos3.BooleanCubeKernel.vertexFinsetEquiv`, `OAI.Erdos3.BooleanCubeKernel.vertexFinsetEquiv_card`, `OAI.Erdos3.CyclicTranslatedNiltestShiftBound`, `OAI.Erdos3.HasCommonMixedTargetInterval`, `OAI.Erdos3.HasCommonMixedTargetInterval.positive`, `OAI.Erdos3.HasCyclicMixedTargetCorrelation`, `OAI.Erdos3.HasCyclicMixedTargetCorrelation.mixed_sum`, `OAI.Erdos3.HasCyclicMixedTargetCorrelation.mono`, `OAI.Erdos3.HasMixedTargetIntervals`, `OAI.Erdos3.HasMixedTargetIntervals.common`, `OAI.Erdos3.HasPositiveMixedTargetInterval`, `OAI.Erdos3.HasPositiveMixedTargetInterval.cyclic`, `OAI.Erdos3.HasSumTargetIntervals`, `OAI.Erdos3.HasSumTargetIntervals.mono`, `OAI.Erdos3.HasWeightedTargetCubeIntervals.to_sum`, `OAI.Erdos3.NativeCharacterCrossRowDetection`, `OAI.Erdos3.NativeCrossRowDetection`, `OAI.Erdos3.NativeMixedCorrelation.exists_mixedResidualRowFactor_expansion`, `OAI.Erdos3.NativeMixedCorrelation.mixedPrimitiveRow`, `OAI.Erdos3.NativeMixedCorrelation.mixedPrimitiveRow_cross_residual`, `OAI.Erdos3.NativeMixedCorrelation.mixedPrimitiveRow_eq`, `OAI.Erdos3.NativeMixedCorrelation.mixedResidualRowFactor`, `OAI.Erdos3.NativeMixedCorrelation.mixedResidualRowFactor_norm`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedPrimitiveFactor`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedPrimitiveFactor_cross`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedPrimitiveFactor_norm`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixed_original_row_correlation_bound`, `OAI.Erdos3.NativeResidualCrossRowDetection`, `OAI.Erdos3.PositiveGridEstimate`, `OAI.Erdos3.PositiveGridShifts`, `OAI.Erdos3.PositiveGridVertex`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_gowers_of_residual_cross_rows`, `OAI.Erdos3.VectorPolynomial.AllocatedFixedScaleCenteredOneSiteStatement`, `OAI.Erdos3.VectorPolynomial.AllocatedFixedScaleJointMarginalStatement`, `OAI.Erdos3.VectorPolynomial.allocatedCenteredJointDensity`, `OAI.Erdos3.VectorPolynomial.allocatedCenteredJointDensity_eq_affine`, `OAI.Erdos3.VectorPolynomial.allocatedCenteredJointDensity_measurable_center`, `OAI.Erdos3.VectorPolynomial.allocatedCenteredJointDensity_nonneg`, `OAI.Erdos3.VectorPolynomial.allocatedFixedScale_center_mixture_compare`, `OAI.Erdos3.VectorPolynomial.allocatedJointBaseDensity`, `OAI.Erdos3.VectorPolynomial.allocatedJointBaseDensity_nonneg`, `OAI.Erdos3.VectorPolynomial.allocatedJointBaseDensity_subtractConstant_affine`, `OAI.Erdos3.VectorPolynomial.allocatedJointBaseDensity_subtractConstant_centered`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalPathLaw`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalPathLaw_subtractConstant_eq_centered`, `OAI.Erdos3.VectorPolynomial.allocatedSlicedCubeSource`, `OAI.Erdos3.VectorPolynomial.exists_allocated_fixedScale_centered_oneSite_comparison`, `OAI.Erdos3.VectorPolynomial.exists_allocated_fixedScale_joint_marginal`, `OAI.Erdos3.VectorPolynomial.exists_allocated_fixed_scale_centered_normalization`, `OAI.Erdos3.VectorPolynomial.exists_allocated_narrow_normalization`, `OAI.Erdos3.VectorPolynomial.exists_allocated_narrow_oneSite_domination`, `OAI.Erdos3.booleanWeight_true`, `OAI.Erdos3.complexMaskCoefficient`, `OAI.Erdos3.complexMaskComponent`, `OAI.Erdos3.complexMaskSign`, `OAI.Erdos3.complexPositiveMask`, `OAI.Erdos3.conjugationPower_twice`, `OAI.Erdos3.cubeShift_congr_selected`, `OAI.Erdos3.cubeShift_true`, `OAI.Erdos3.exists_absorb_fixed_target_cube_errors`, `OAI.Erdos3.exists_absorb_pair_missing_coordinate_errors`, `OAI.Erdos3.exists_characters_of_stepOne_rows`, `OAI.Erdos3.exists_cyclicNativeInverse_step`, `OAI.Erdos3.exists_cyclic_target_pair_factors`, `OAI.Erdos3.exists_false_of_ne_true`, `OAI.Erdos3.exists_fullCube_proper_factors`, `OAI.Erdos3.exists_full_mixed_cube_proper_factors`, `OAI.Erdos3.exists_gowers_of_bounded_native_residual_cross_family`, `OAI.Erdos3.exists_gowers_of_native_cross_family`, `OAI.Erdos3.exists_gowers_of_native_residual_cross_family`, `OAI.Erdos3.exists_mixedCube_proper_factors`, `OAI.Erdos3.exists_mixed_interval_cutoff_weights`, `OAI.Erdos3.exists_mixed_primitive_correlation_large_modulus`, `OAI.Erdos3.exists_mixed_primitive_gowers`, `OAI.Erdos3.exists_mixed_primitive_rows`, `OAI.Erdos3.exists_mixed_residual_cross_rows`, `OAI.Erdos3.exists_mixed_sum_pair_factors`, `OAI.Erdos3.exists_native_character_cross_row_detection`, `OAI.Erdos3.exists_native_character_cross_row_step`, `OAI.Erdos3.exists_native_cross_row_detection`, `OAI.Erdos3.exists_native_cross_row_detection_one`, `OAI.Erdos3.exists_native_cyclic_small_modulus_correlation`, `OAI.Erdos3.exists_native_residual_cross_row_detection`, `OAI.Erdos3.exists_native_residual_cross_row_detection_zero`, `OAI.Erdos3.exists_native_residual_cross_row_step`, `OAI.Erdos3.exists_normalized_cube_weights`, `OAI.Erdos3.exists_retained_cyclic_sum`, `OAI.Erdos3.exists_retained_mixed_cyclic_comparison`, `OAI.Erdos3.exists_retained_mixed_original_integration`, `OAI.Erdos3.exists_retained_mixed_pair_factors`, `OAI.Erdos3.exists_retained_mixed_sampled_exchange`, `OAI.Erdos3.exists_retained_sum_target_intervals`, `OAI.Erdos3.exists_separated_sum_intervals`, `OAI.Erdos3.exp_le_gowers_of_mean_derivative`, `OAI.Erdos3.fullCubeSignal`, `OAI.Erdos3.fullCubeSignal_profile`, `OAI.Erdos3.fullCube_input_independent`, `OAI.Erdos3.mean_derivative_gowers_power_le`, `OAI.Erdos3.mixedCubeInput_independent`, `OAI.Erdos3.mixedCubeInput_true`, `OAI.Erdos3.mixedInterval_zeroExtension_average`, `OAI.Erdos3.mixedProfileEquiv`, `OAI.Erdos3.mixedProfileEquiv_point`, `OAI.Erdos3.mixedProfileFromCoordinates`, `OAI.Erdos3.mixedProfileFromCoordinates_independent`, `OAI.Erdos3.mixedProfileFromCoordinates_point`, `OAI.Erdos3.mixedProfile_average`, `OAI.Erdos3.mixedProfile_card`, `OAI.Erdos3.mixedRowCoordinateCount`, `OAI.Erdos3.mixedRowIndex_card`, `OAI.Erdos3.narrowPhysicalSiteMap`, `OAI.Erdos3.narrowPhysicalSiteMap_cast`, `OAI.Erdos3.narrowTrimmedSpatial_site_width`, `OAI.Erdos3.norm_fourierCoeff_le_gowers_two`, `OAI.Erdos3.normalizedAxisProduct`, `OAI.Erdos3.positiveGridFiber`, `OAI.Erdos3.positiveGridMean`, `OAI.Erdos3.positiveGridProduct`, `OAI.Erdos3.positiveGridVolume`, `OAI.Erdos3.selectedJointDensityMass_measurable`, `OAI.Erdos3.selectedJointFiniteLaw_realTest_integrable`, `OAI.Erdos3.selectedJointFiniteLaw_realTest_measurable`, `OAI.Erdos3.selectedJointFiniteLaw_weight_measurable`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B054
import Definitions.Def_OAIErdos3B1326

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeResidualCrossInduction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_fourierCoeff_le_gowers_two {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (χ : AddChar G ℂ) : ‖finiteFourierCoeff f χ‖ ≤ gowersNorm 2 f := by
  classical
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (gowersNorm_nonneg 1 f)
    (by norm_num : (4 : ℕ) ≠ 0)).mp
  rw [gowersNorm_two_fourier]
  exact Finset.single_le_sum (fun ψ _ => pow_nonneg (norm_nonneg _) 4) (Finset.mem_univ χ)

theorem mean_derivative_gowers_power_le {G : Type*} [AddCommGroup G] [Fintype G]
    (s : ℕ) (f : G → ℂ) :
    (𝔼 k, gowersNorm (s + 1) (multiplicativeDerivative f k)) ^ (2 ^ (s + 1)) ≤
      gowersNorm (s + 2) f ^ (2 ^ (s + 2)) := by
  rw [gowersNorm_derivative]
  exact expect_pow_two_pow_le (s + 1) _ (fun k => gowersNorm_nonneg s _)

theorem exp_le_gowers_of_mean_derivative {G : Type*} [AddCommGroup G] [Fintype G]
    (s : ℕ) (f : G → ℂ) {p : ℝ} (hp : 0 ≤ p)
    (hcorr : Real.exp (-p) ≤ 𝔼 k, gowersNorm (s + 1) (multiplicativeDerivative f k)) :
    Real.exp (-p) ≤ gowersNorm (s + 2) f := by
  have hexp : Real.exp (-p) ^ (2 ^ (s + 2)) ≤ Real.exp (-p) ^ (2 ^ (s + 1)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    rw [show s + 2 = (s + 1) + 1 by omega, pow_succ]
    push_cast
    nlinarith [mul_nonneg hp (show (0 : ℝ) ≤ 2 ^ (s + 1) by positivity)]
  have hpower := hexp.trans ((pow_le_pow_left₀ (Real.exp_nonneg _) hcorr _).trans
    (mean_derivative_gowers_power_le s f))
  exact (pow_le_pow_iff_left₀ (Real.exp_nonneg _) (gowersNorm_nonneg (s + 1) f)
    (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))).mp hpower

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

def NativeCrossRowDetection (s C : ℕ) : Prop :=
  ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {d : ℕ} (D : RationalFilteredNilmanifold L s d)
    (T : D.Niltest (fun _ : Fin 2 => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
    ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
    ∀ f g : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → (∀ n, ‖g n‖ ≤ 1) →
    Real.exp (-p) ≤ (𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
      (f n * star (g (n + h))) * star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
    Real.exp (-((p + C) ^ C)) ≤ gowersNorm (s + 1) g

def NativeCharacterCrossRowDetection (s C : ℕ) : Prop :=
  ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {d : ℕ} (D : RationalFilteredNilmanifold L s d)
    (T : D.Niltest (fun _ : Fin 2 => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
    ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
    ∀ (f g : ZMod N → ℂ) (χ : ZMod N → AddChar (ZMod N) ℂ),
    (∀ n, ‖f n‖ ≤ 1) → (∀ n, ‖g n‖ ≤ 1) →
    Real.exp (-p) ≤ (𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
      characterCrossRow f g χ h n * star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
    Real.exp (-((p + C) ^ C)) ≤ gowersNorm (s + 1) g

theorem exists_native_cross_row_detection_one :
    ∃ C : ℕ, 2 ≤ C ∧ NativeCrossRowDetection 1 C := by
  obtain ⟨C, hC, hfourier⟩ := exists_fourier_of_stepOne_cross_correlation
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D T p hp hT N _ _hN f g hf hg hcorr
  obtain ⟨χ, hχ⟩ := hfourier D hp T hT f g hf hg hcorr
  exact hχ.trans (norm_fourierCoeff_le_gowers_two g χ)

attribute [local instance] NativeMeanRowCorrelation.lie NativeMeanRowCorrelation.algebra NativeMeanRowCorrelation.topology NativeMeanRowCorrelation.topologicalAdd NativeMeanRowCorrelation.continuousSMul NativeMeanRowCorrelation.hausdorff

theorem exists_gowers_of_native_cross_family {s A : ℕ} (hdetect : NativeCrossRowDetection s A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type*} [Fintype I] [Nonempty I] {N : ℕ} [NeZero N]
      {p : ℝ}, 0 ≤ p → Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ (a b : I → ZMod N → ℂ) (K : I → (Fin 2 → ℤ) → ℂ),
      (∀ i n, ‖a i n‖ ≤ 1) → (∀ i n, ‖b i n‖ ≤ 1) →
      (∀ i, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s p (K i))) →
      Real.exp (-p) ≤ (𝔼 i, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
        (a i n * star (b i (n + h))) * star (K i ![(h.val : ℤ), (n.val : ℤ)])‖) →
      Real.exp (-((p + C) ^ C)) ≤ 𝔼 i, gowersNorm (s + 1) (b i) := by
  let X : Polynomial ℕ := Polynomial.X
  let T := 3 * X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (T + (T + X + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro I _ _ N _ p hp hN a b K ha hb hK hcorr
  classical
  let c (i : I) := 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
    (a i n * star (b i (n + h))) * star (K i ![(h.val : ℤ), (n.val : ℤ)])‖
  let z (i : I) := Real.exp (-(2 * p)) * c i
  let t := 3 * p + 2
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hc0 (i : I) : 0 ≤ c i := Finset.expect_nonneg (fun _ _ => norm_nonneg _)
  have hcap (i : I) : c i ≤ Real.exp (2 * p) := by
    apply Finset.expect_le Finset.univ_nonempty
    intro h _
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le Finset.univ_nonempty
    intro n _
    rw [norm_mul, norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
      ((Classical.choice (hK i)).norm_eval_le _)
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ha i n)).trans (hb i (n + h))
  have hzcap (i : I) : z i ≤ 1 := by
    calc
      _ ≤ Real.exp (-(2 * p)) * Real.exp (2 * p) :=
        mul_le_mul_of_nonneg_left (hcap i) (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hzmean : Real.exp (-(3 * p)) ≤ 𝔼 i, z i := by
    change Real.exp (-(3 * p)) ≤ 𝔼 i, Real.exp (-(2 * p)) * c i
    rw [← Finset.mul_expect]
    have heq : Real.exp (-(3 * p)) = Real.exp (-(2 * p)) * Real.exp (-p) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hcorr (Real.exp_nonneg _)
  obtain ⟨S, hS, hlarge⟩ := exists_dense_level_set z (Real.exp_nonneg (-(3 * p))) hzcap hzmean
  have hhalf : Real.exp (-t) ≤ Real.exp (-(3 * p)) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    calc
      _ ≤ Real.exp (-t) * Real.exp 2 := mul_le_mul_of_nonneg_left
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [t]; ring
  have hzle (i : I) : z i ≤ c i := mul_le_of_le_one_left (hc0 i)
    (Real.exp_le_one_iff.mpr (by linarith))
  have hcost : t + (t + p + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  have hN' : Real.exp ((t + p + A) ^ A) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans hN
  have hnorm (i : I) (hi : i ∈ S) :
      Real.exp (-((t + p + A) ^ A)) ≤ gowersNorm (s + 1) (b i) := by
    have hc : Real.exp (-t) ≤ c i := hhalf.trans ((hlarge i hi).trans (hzle i))
    obtain ⟨V⟩ := NativeMeanRowCorrelation.exists_of_expansion
      (Classical.choice (hK i)) ht hc
    exact hdetect V.model V.test (by linarith : 0 ≤ t + p) V.complexity hN'
      (a i) (b i) (ha i) (hb i) V.correlation
  have hmass := dense_set_mean_lower_bound S (fun i => gowersNorm (s + 1) (b i))
    (fun i => gowersNorm_nonneg s (b i)) (Real.exp_nonneg (-((t + p + A) ^ A)))
    ((mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg _)).trans hS) hnorm
  apply (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans
  have heq : Real.exp (-(t + (t + p + A) ^ A)) =
      Real.exp (-t) * Real.exp (-((t + p + A) ^ A)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rwa [heq]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_characters_of_stepOne_rows :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {H : Type*} [Fintype H] [Nonempty H] {N : ℕ} [NeZero N] {p : ℝ},
      0 ≤ p → ∀ (F : H → ZMod N → ℂ) (g : H → (Unit → ℤ) → ℂ),
      (∀ h n, ‖F h n‖ ≤ Real.exp p) →
      (∀ h (n : ZMod N), ‖g h (fun _ => (n.val : ℤ))‖ ≤ 1) →
      (∀ h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 1 p (g h))) →
      Real.exp (-p) ≤ (𝔼 h, ‖𝔼 n : ZMod N, F h n * star (g h (fun _ => (n.val : ℤ)))‖) →
      ∃ χ : H → AddChar (ZMod N) ℂ,
        Real.exp (-((p + C) ^ C)) ≤ 𝔼 h, ‖finiteFourierCoeff (F h) (χ h)‖ := by
  obtain ⟨A, _, hfourier⟩ := exists_fourier_of_stepOne_expansion
  let X : Polynomial ℕ := Polynomial.X
  let T := 2 * X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro H _ _ N _ p hp F g hF hg hE hcorr
  classical
  let F' : H → ZMod N → ℂ := fun h n => (Real.exp (-p) : ℂ) * F h n
  let t := 2 * p + 2
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hF' (h : H) (n : ZMod N) : ‖F' h n‖ ≤ 1 := by
    simp only [F', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-p) * Real.exp p := mul_le_mul_of_nonneg_left (hF h n) (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hscale (h : H) :
      ‖𝔼 n : ZMod N, F' h n * star (g h (fun _ => (n.val : ℤ)))‖ =
        Real.exp (-p) * ‖𝔼 n : ZMod N, F h n * star (g h (fun _ => (n.val : ℤ)))‖ := by
    have heq : (𝔼 n : ZMod N, F' h n * star (g h (fun _ => (n.val : ℤ)))) =
        (Real.exp (-p) : ℂ) * (𝔼 n : ZMod N, F h n * star (g h (fun _ => (n.val : ℤ)))) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro n _
      dsimp [F']
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hmean : Real.exp (-(2 * p)) ≤
      𝔼 h, ‖𝔼 n : ZMod N, F' h n * star (g h (fun _ => (n.val : ℤ)))‖ := by
    simp only [hscale, ← Finset.mul_expect]
    have heq : Real.exp (-(2 * p)) = Real.exp (-p) * Real.exp (-p) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hcorr (Real.exp_nonneg _)
  have hcap (h : H) : ‖𝔼 n : ZMod N, F' h n * star (g h (fun _ => (n.val : ℤ)))‖ ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le Finset.univ_nonempty
    intro n _
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hF' h n)).trans (hg h n)
  obtain ⟨S, hS, hlarge⟩ := exists_dense_level_set _ (Real.exp_nonneg (-(2 * p))) hcap hmean
  have hhalf : Real.exp (-t) ≤ Real.exp (-(2 * p)) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    calc
      _ ≤ Real.exp (-t) * Real.exp 2 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [t]; ring
  have hcharacter (h : H) (hh : h ∈ S) : ∃ χ : AddChar (ZMod N) ℂ,
      Real.exp (-((t + A) ^ A)) ≤ ‖finiteFourierCoeff (F' h) χ‖ :=
    hfourier ht ((Classical.choice (hE h)).mono hpt) (F' h) (hF' h) (hhalf.trans (hlarge h hh))
  let χ (h : H) : AddChar (ZMod N) ℂ := if hh : h ∈ S then Classical.choose (hcharacter h hh) else 1
  have hmass := dense_set_mean_lower_bound S (fun h => ‖finiteFourierCoeff (F' h) (χ h)‖)
    (fun _ => norm_nonneg _) (Real.exp_nonneg (-((t + A) ^ A)))
    ((mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg _)).trans hS)
    (fun h hh => by simpa only [χ, dif_pos hh] using Classical.choose_spec (hcharacter h hh))
  have hmono (h : H) : ‖finiteFourierCoeff (F' h) (χ h)‖ ≤ ‖finiteFourierCoeff (F h) (χ h)‖ := by
    have heq : finiteFourierCoeff (F' h) (χ h) = (Real.exp (-p) : ℂ) * finiteFourierCoeff (F h) (χ h) := by
      unfold finiteFourierCoeff
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro n _
      dsimp [F']
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hp))
  have hcost : t + (t + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨χ, (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans ?_⟩
  have heq : Real.exp (-(t + (t + A) ^ A)) = Real.exp (-t) * Real.exp (-((t + A) ^ A)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [heq]
  exact hmass.trans (Finset.expect_le_expect (fun h _ => hmono h))

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_native_character_cross_row_step {s A : ℕ} (hs : 1 ≤ s)
    (hdetect : NativeCrossRowDetection s A) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeCharacterCrossRowDetection (s + 1) C := by
  obtain ⟨B, _, hdifference⟩ := RationalFilteredNilmanifold.exists_differenced_rows_degree s hs
  obtain ⟨D, _, hfamily⟩ := exists_gowers_of_native_cross_family hdetect
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + (U + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d M T p hp hT N _ hN f g χ hf hg hcorr
  let u := (p + B) ^ B
  let v := (u + D) ^ D
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have htotal : u + v ≤ (p + C) ^ C := by
    simpa [X, U, u, v, Polynomial.eval₂_pow] using hbudget p hp
  have huC : u ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  obtain ⟨K, hK, hKcorr⟩ := hdifference M T hp hT
    ((Real.exp_le_exp.mpr huC).trans hN) (characterCrossRow f g χ)
    (characterCrossRow_norm f g χ hf hg) hcorr
  have hclean : Real.exp (-u) ≤ (𝔼 k : ZMod N, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
      (multiplicativeDerivative f k n * star (multiplicativeDerivative g k (n + h))) *
        star (K k ![(h.val : ℤ), (n.val : ℤ)])‖) := by
    simpa only [characterCrossRow_derivative_correlation_norm] using hKcorr
  have hmean := hfamily hu ((Real.exp_le_exp.mpr hvC).trans hN)
    (fun k => multiplicativeDerivative f k) (fun k => multiplicativeDerivative g k) K
    (multiplicativeDerivative_norm_le_one f hf) (multiplicativeDerivative_norm_le_one g hg)
    hK hclean
  exact (Real.exp_le_exp.mpr (neg_le_neg hvC)).trans
    (exp_le_gowers_of_mean_derivative s g hv hmean)

theorem exists_native_cross_row_detection (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeCrossRowDetection s C := by
  have hall : ∀ n : ℕ, ∃ C : ℕ, 2 ≤ C ∧ NativeCrossRowDetection (n + 1) C := by
    intro n
    induction n with
    | zero => exact exists_native_cross_row_detection_one
    | succ n ih =>
        obtain ⟨A, _, hdetect⟩ := ih
        obtain ⟨C, hC, hstep⟩ := exists_native_character_cross_row_step
          (by omega : 1 ≤ n + 1) hdetect
        refine ⟨C, hC, ?_⟩
        intro L _ _ _ _ _ _ d M T p hp hT N _ hN f g hf hg hcorr
        apply hstep M T hp hT hN f g (fun _ => 1) hf hg
        simpa [characterCrossRow] using hcorr
  cases s with
  | zero => omega
  | succ n => exact hall n

theorem exists_native_character_cross_row_detection (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeCharacterCrossRowDetection s C := by
  cases s with
  | zero => omega
  | succ n =>
      have hn : 1 ≤ n := by omega
      obtain ⟨A, _, hdetect⟩ := exists_native_cross_row_detection n hn
      exact exists_native_character_cross_row_step hn hdetect

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

def NativeResidualCrossRowDetection (s C : ℕ) : Prop :=
  ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {d : ℕ} (D : RationalFilteredNilmanifold L (s + 2) d)
    (T : D.Niltest (fun _ : Fin 2 => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
    ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
    ∀ (f g : ZMod N → ℂ) (R : ZMod N → (Unit → ℤ) → ℂ),
    (∀ n, ‖f n‖ ≤ 1) → (∀ n, ‖g n‖ ≤ 1) →
    (∀ h (n : ZMod N), ‖R h (fun _ => (n.val : ℤ))‖ ≤ 1) →
    (∀ h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) p (R h))) →
    Real.exp (-p) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
      ((f n * star (g (n + h))) * star (R h (fun _ => (n.val : ℤ)))) *
        star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
    Real.exp (-((p + C) ^ C)) ≤ gowersNorm (s + 3) g

theorem exists_native_residual_cross_row_detection_zero :
    ∃ C : ℕ, 2 ≤ C ∧ NativeResidualCrossRowDetection 0 C := by
  obtain ⟨A, _, hlinear⟩ := exists_characters_of_stepOne_rows
  obtain ⟨B, _, hdetect⟩ := exists_native_character_cross_row_detection 2 (by omega)
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D T p hp hT N _ hN f g R hf hg hR hRE hcorr
  let q := p + (p + A) ^ A
  have hpow : 0 ≤ (p + A) ^ A := by positivity
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hscore : (p + A) ^ A ≤ q := by dsimp [q]; linarith
  have hsum : q + (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hresult : (q + B) ^ B ≤ (p + C) ^ C := by linarith
  let F (h n : ZMod N) := (f n * star (g (n + h))) *
    star (T.eval ![(h.val : ℤ), (n.val : ℤ)])
  have hF (h n : ZMod N) : ‖F h n‖ ≤ Real.exp p := by
    have hcross : ‖f n * star (g (n + h))‖ ≤ 1 := by
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf n)).trans (hg (n + h))
    change ‖(f n * star (g (n + h))) * star (T.eval _)‖ ≤ _
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) hcross).trans (T.eval_budget hT _)
  have hFcorr : Real.exp (-p) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
      F h n * star (R h (fun _ => (n.val : ℤ)))‖) := by
    apply hcorr.trans_eq
    apply Finset.expect_congr rfl
    intro h _
    congr 1
    apply Finset.expect_congr rfl
    intro n _
    exact mul_right_comm _ _ _
  obtain ⟨χ, hχ⟩ := hlinear hp F R hF hR hRE hFcorr
  have hchars : Real.exp (-q) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
      characterCrossRow f g χ h n * star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) := by
    apply (Real.exp_le_exp.mpr (neg_le_neg hscore)).trans
    apply hχ.trans_eq
    apply Finset.expect_congr rfl
    intro h _
    congr 1
    unfold finiteFourierCoeff
    apply Finset.expect_congr rfl
    intro n _
    dsimp [F, characterCrossRow]
    ring
  exact (Real.exp_le_exp.mpr (neg_le_neg hresult)).trans
    (hdetect D T hq (hT.mono hpq) ((Real.exp_le_exp.mpr hresult).trans hN)
      f g χ hf hg hchars)

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeMeanRowCorrelation.lie NativeMeanRowCorrelation.algebra NativeMeanRowCorrelation.topology NativeMeanRowCorrelation.topologicalAdd NativeMeanRowCorrelation.continuousSMul NativeMeanRowCorrelation.hausdorff

theorem exists_gowers_of_bounded_native_residual_cross_family {s A : ℕ}
    (hdetect : NativeResidualCrossRowDetection s A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type*} [Fintype I] [Nonempty I] {N : ℕ} [NeZero N]
      {p : ℝ}, 0 ≤ p → Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ (a b : I → ZMod N → ℂ) (K : I → (Fin 2 → ℤ) → ℂ)
        (R : I → ZMod N → (Unit → ℤ) → ℂ),
      (∀ i n, ‖a i n‖ ≤ 1) → (∀ i n, ‖b i n‖ ≤ 1) →
      (∀ i h (n : ZMod N), ‖R i h (fun _ => (n.val : ℤ))‖ ≤ 1) →
      (∀ i, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) p (K i))) →
      (∀ i h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) p (R i h))) →
      Real.exp (-p) ≤ (𝔼 i, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
        ((a i n * star (b i (n + h))) * star (R i h (fun _ => (n.val : ℤ)))) *
          star (K i ![(h.val : ℤ), (n.val : ℤ)])‖) →
      Real.exp (-((p + C) ^ C)) ≤ 𝔼 i, gowersNorm (s + 3) (b i) := by
  let X : Polynomial ℕ := Polynomial.X
  let T := 3 * X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (T + (T + X + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro I _ _ N _ p hp hN a b K R ha hb hR hK hRE hcorr
  classical
  let c (i : I) := 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
    ((a i n * star (b i (n + h))) * star (R i h (fun _ => (n.val : ℤ)))) *
      star (K i ![(h.val : ℤ), (n.val : ℤ)])‖
  let z (i : I) := Real.exp (-(2 * p)) * c i
  let t := 3 * p + 2
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hc0 (i : I) : 0 ≤ c i := Finset.expect_nonneg (fun _ _ => norm_nonneg _)
  have hunit (i : I) (h n : ZMod N) :
      ‖(a i n * star (b i (n + h))) * star (R i h (fun _ => (n.val : ℤ)))‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hR i h n)
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ha i n)).trans (hb i (n + h))
  have hcap (i : I) : c i ≤ Real.exp (2 * p) := by
    apply Finset.expect_le Finset.univ_nonempty
    intro h _
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le Finset.univ_nonempty
    intro n _
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hunit i h n)).trans
      ((Classical.choice (hK i)).norm_eval_le _)
  have hzcap (i : I) : z i ≤ 1 := by
    calc
      _ ≤ Real.exp (-(2 * p)) * Real.exp (2 * p) :=
        mul_le_mul_of_nonneg_left (hcap i) (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hzmean : Real.exp (-(3 * p)) ≤ 𝔼 i, z i := by
    change Real.exp (-(3 * p)) ≤ 𝔼 i, Real.exp (-(2 * p)) * c i
    rw [← Finset.mul_expect]
    have heq : Real.exp (-(3 * p)) = Real.exp (-(2 * p)) * Real.exp (-p) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hcorr (Real.exp_nonneg _)
  obtain ⟨S, hS, hlarge⟩ := exists_dense_level_set z (Real.exp_nonneg (-(3 * p))) hzcap hzmean
  have hhalf : Real.exp (-t) ≤ Real.exp (-(3 * p)) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    calc
      _ ≤ Real.exp (-t) * Real.exp 2 := mul_le_mul_of_nonneg_left
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [t]; ring
  have hzle (i : I) : z i ≤ c i := mul_le_of_le_one_left (hc0 i)
    (Real.exp_le_one_iff.mpr (by linarith))
  have hcost : t + (t + p + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  have hN' : Real.exp ((t + p + A) ^ A) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans hN
  have hnorm (i : I) (hi : i ∈ S) :
      Real.exp (-((t + p + A) ^ A)) ≤ gowersNorm (s + 3) (b i) := by
    have hc : Real.exp (-t) ≤ c i := hhalf.trans ((hlarge i hi).trans (hzle i))
    obtain ⟨V⟩ := NativeMeanRowCorrelation.exists_of_expansion
      (Classical.choice (hK i)) ht hc
    exact hdetect V.model V.test (by linarith : 0 ≤ t + p) V.complexity hN'
      (a i) (b i) (R i) (ha i) (hb i) (hR i)
      (fun h => ⟨(Classical.choice (hRE i h)).mono (by linarith)⟩) V.correlation
  have hmass := dense_set_mean_lower_bound S (fun i => gowersNorm (s + 3) (b i))
    (fun i => gowersNorm_nonneg (s + 2) (b i)) (Real.exp_nonneg (-((t + p + A) ^ A)))
    ((mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg _)).trans hS) hnorm
  apply (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans
  have heq : Real.exp (-(t + (t + p + A) ^ A)) =
      Real.exp (-t) * Real.exp (-((t + p + A) ^ A)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rwa [heq]

theorem exists_gowers_of_native_residual_cross_family {s A : ℕ}
    (hdetect : NativeResidualCrossRowDetection s A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type*} [Fintype I] [Nonempty I] {N : ℕ} [NeZero N]
      {p : ℝ}, 0 ≤ p → Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ (a b : I → ZMod N → ℂ) (K : I → (Fin 2 → ℤ) → ℂ)
        (R : I → ZMod N → (Unit → ℤ) → ℂ),
      (∀ i n, ‖a i n‖ ≤ 1) → (∀ i n, ‖b i n‖ ≤ 1) →
      (∀ i, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) p (K i))) →
      (∀ i h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) p (R i h))) →
      Real.exp (-p) ≤ (𝔼 i, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
        ((a i n * star (b i (n + h))) * star (R i h (fun _ => (n.val : ℤ)))) *
          star (K i ![(h.val : ℤ), (n.val : ℤ)])‖) →
      Real.exp (-((p + C) ^ C)) ≤ 𝔼 i, gowersNorm (s + 3) (b i) := by
  obtain ⟨B, _, hfamily⟩ := exists_gowers_of_bounded_native_residual_cross_family hdetect
  let X : Polynomial ℕ := Polynomial.X
  let Q := 3 * X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro I _ _ N _ p hp hN a b K R ha hb hK hRE hcorr
  classical
  let q := 3 * p + 2
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hsum : q + (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hresult : (q + B) ^ B ≤ (p + C) ^ C := by linarith
  let R₀ : I → ZMod N → (Unit → ℤ) → ℂ := fun i h x =>
    (Real.exp (-(2 * p)) : ℂ) * R i h x
  have hR₀ (i : I) (h n : ZMod N) : ‖R₀ i h (fun _ => (n.val : ℤ))‖ ≤ 1 := by
    simp only [R₀, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-(2 * p)) * Real.exp (2 * p) :=
        mul_le_mul_of_nonneg_left ((Classical.choice (hRE i h)).norm_eval_le _)
          (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hR₀E (i : I) (h : ZMod N) :
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) q (R₀ i h)) := by
    apply Nonempty.intro
    apply NativeIntegerExpansion.mono _ hpq
    apply (Classical.choice (hRE i h)).scaleNormLeOne
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      (Real.exp_le_one_iff.mpr (by linarith : -(2 * p) ≤ 0))
  have hscale (i : I) (h : ZMod N) :
      ‖𝔼 n : ZMod N, ((a i n * star (b i (n + h))) *
        star (R₀ i h (fun _ => (n.val : ℤ)))) * star (K i ![(h.val : ℤ), (n.val : ℤ)])‖ =
      Real.exp (-(2 * p)) * ‖𝔼 n : ZMod N, ((a i n * star (b i (n + h))) *
        star (R i h (fun _ => (n.val : ℤ)))) * star (K i ![(h.val : ℤ), (n.val : ℤ)])‖ := by
    have heq : (𝔼 n : ZMod N, ((a i n * star (b i (n + h))) *
        star (R₀ i h (fun _ => (n.val : ℤ)))) * star (K i ![(h.val : ℤ), (n.val : ℤ)])) =
      (Real.exp (-(2 * p)) : ℂ) * (𝔼 n : ZMod N, ((a i n * star (b i (n + h))) *
        star (R i h (fun _ => (n.val : ℤ)))) * star (K i ![(h.val : ℤ), (n.val : ℤ)])) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro n _
      simp only [R₀, star_mul]
      rw [show star ((Real.exp (-(2 * p))) : ℂ) = (Real.exp (-(2 * p)) : ℂ) from
        Complex.conj_ofReal _]
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hscaled : Real.exp (-q) ≤ (𝔼 i, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
      ((a i n * star (b i (n + h))) * star (R₀ i h (fun _ => (n.val : ℤ)))) *
        star (K i ![(h.val : ℤ), (n.val : ℤ)])‖) := by
    simp only [hscale, ← Finset.mul_expect]
    apply (Real.exp_le_exp.mpr (show -q ≤ -(3 * p) by dsimp [q]; linarith)).trans
    have heq : Real.exp (-(3 * p)) = Real.exp (-(2 * p)) * Real.exp (-p) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hcorr (Real.exp_nonneg _)
  exact (Real.exp_le_exp.mpr (neg_le_neg hresult)).trans
    (hfamily hq ((Real.exp_le_exp.mpr hresult).trans hN) a b K R₀ ha hb hR₀
      (fun i => ⟨(Classical.choice (hK i)).mono hpq⟩) hR₀E hscaled)

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_native_residual_cross_row_step {s A : ℕ}
    (hdetect : NativeResidualCrossRowDetection s A) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeResidualCrossRowDetection (s + 1) C := by
  obtain ⟨B, _, hdifference⟩ := RationalFilteredNilmanifold.exists_residual_row_differences_degree s
  obtain ⟨D, _, hfamily⟩ := exists_gowers_of_native_residual_cross_family hdetect
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + (U + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d M T p hp hT N _ hN f g R hf hg hR hRE hcorr
  let u := (p + B) ^ B
  let v := (u + D) ^ D
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hsum : u + v ≤ (p + C) ^ C := by
    simpa [X, U, u, v, Polynomial.eval₂_pow] using hbudget p hp
  have huC : u ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  obtain ⟨K, J, hK, hJ, hdiff⟩ := hdifference M T hp hT
    ((Real.exp_le_exp.mpr huC).trans hN) (fun h n => f n * star (g (n + h))) R
    (by
      intro h n
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf n)).trans (hg (n + h))) hR hRE hcorr
  have hderiv (h k n : ZMod N) :
      multiplicativeDerivative (fun n => f n * star (g (n + h))) k n =
        multiplicativeDerivative f k n * star (multiplicativeDerivative g k (n + h)) := by
    simp only [multiplicativeDerivative, star_mul, star_star]
    rw [add_right_comm n k h]
    ring
  have hclean : Real.exp (-u) ≤ (𝔼 k, 𝔼 h, ‖𝔼 n : ZMod N,
      ((multiplicativeDerivative f k n * star (multiplicativeDerivative g k (n + h))) *
        star (J k h (fun _ => (n.val : ℤ)))) *
        star (K k ![(h.val : ℤ), (n.val : ℤ)])‖) := by
    simpa only [hderiv, mul_comm, mul_left_comm, mul_assoc] using hdiff
  have hmean := hfamily hu ((Real.exp_le_exp.mpr hvC).trans hN)
    (multiplicativeDerivative f) (multiplicativeDerivative g) K J
    (multiplicativeDerivative_norm_le_one f hf) (multiplicativeDerivative_norm_le_one g hg)
    hK hJ hclean
  exact (Real.exp_le_exp.mpr (neg_le_neg hvC)).trans
    (exp_le_gowers_of_mean_derivative (s + 2) g hv hmean)

theorem exists_native_residual_cross_row_detection (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeResidualCrossRowDetection s C := by
  induction s with
  | zero => exact exists_native_residual_cross_row_detection_zero
  | succ s ih =>
      obtain ⟨A, _, hdetect⟩ := ih
      exact exists_native_residual_cross_row_step hdetect

theorem RationalFilteredNilmanifold.exists_gowers_of_residual_cross_rows (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d)
      (T : D.Niltest (fun _ : Fin 2 => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ (f g : ZMod N → ℂ) (R : ZMod N → (Unit → ℤ) → ℂ),
      (∀ n, ‖f n‖ ≤ 1) → (∀ n, ‖g n‖ ≤ 1) →
      (∀ h (n : ZMod N), ‖R h (fun _ => (n.val : ℤ))‖ ≤ 1) →
      (∀ h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) p (R h))) →
      Real.exp (-p) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
        ((f n * star (g (n + h))) * star (R h (fun _ => (n.val : ℤ)))) *
          star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
      Real.exp (-((p + C) ^ C)) ≤ gowersNorm (s + 1) g := by
  cases s with
  | zero => omega
  | succ s =>
      cases s with
      | zero => omega
      | succ s => exact exists_native_residual_cross_row_detection s

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CubeSignalCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def fullCubeSignal {G : Type*} [AddCommGroup G] {d : ℕ}
    (f : G → ℂ) (x : Fin (d + 3) → G) : ℂ :=
  cubeProduct f (List.ofFn (fun j => x ((1 : Fin (d + 3)).succAbove j))) (x 1)

theorem booleanWeight_true (d : ℕ) : booleanWeight (fun _ : Fin d => true) = d := by
  simp [booleanWeight]

theorem cubeShift_true {G : Type*} [AddCommGroup G] {d : ℕ} (k : Fin d → G) :
    cubeShift k (fun _ => true) = ∑ i, k i := by simp [cubeShift]

theorem exists_false_of_ne_true {d : ℕ} {ω : Fin d → Bool}
    (h : ω ≠ fun _ => true) : ∃ j, ω j = false := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp h
  refine ⟨j, ?_⟩
  cases he : ω j <;> simp_all

theorem cubeShift_congr_selected {G : Type*} [AddCommGroup G] {d : ℕ}
    (k l : Fin d → G) (ω : Fin d → Bool) (h : ∀ i, ω i = true → k i = l i) :
    cubeShift k ω = cubeShift l ω := by
  unfold cubeShift
  apply Finset.sum_congr rfl
  intro i _
  cases hi : ω i with
  | false => simp only [Bool.false_eq_true, ite_false]
  | true => simp only [ite_true]; exact h i hi

theorem fullCube_input_independent {G : Type*} [AddCommGroup G] {d : ℕ}
    (ω : Fin (d + 2) → Bool) (j : Fin (d + 2)) (hj : ω j = false)
    (x y : Fin (d + 3) → G)
    (hxy : ∀ k, k ≠ (1 : Fin (d + 3)).succAbove j → x k = y k) :
    x 1 + cubeShift (fun k => x ((1 : Fin (d + 3)).succAbove k)) ω =
      y 1 + cubeShift (fun k => y ((1 : Fin (d + 3)).succAbove k)) ω := by
  rw [hxy 1 (Fin.ne_succAbove 1 j)]
  congr 1
  apply cubeShift_congr_selected
  intro k hk
  apply hxy
  intro heq
  have hkj : k = j := Fin.succAbove_right_injective heq
  subst k
  simp only [hj, Bool.false_eq_true] at hk

theorem mixedCubeInput_independent {d : ℕ} (ω : Fin d → Bool) (j : Fin d) (hj : ω j = false)
    (x y : Fin (d + 2) → ℤ) (hxy : ∀ k, k ≠ j.succ.succ → x k = y k) :
    mixedCubeInput ω x = mixedCubeInput ω y := by
  have hzero : (0 : Fin (d + 2)) ≠ j.succ.succ := (Fin.succ_ne_zero j.succ).symm
  have hone : (1 : Fin (d + 2)) ≠ j.succ.succ := by
    intro heq
    have h : (0 : Fin (d + 1)) = j.succ := Fin.succ_inj.mp heq
    exact (Fin.succ_ne_zero j).symm h
  unfold mixedCubeInput
  rw [hxy 0 hzero, hxy 1 hone]
  congr 2
  apply cubeShift_congr_selected
  intro k hk
  apply hxy
  intro heq
  have hkj : k = j := Fin.succ_inj.mp (Fin.succ_inj.mp heq)
  subst k
  simp only [hj, Bool.false_eq_true] at hk

theorem mixedCubeInput_true {d : ℕ} (x : Fin (d + 2) → ℤ) :
    mixedCubeInput (fun _ => true) x = correlationInput (x 0) (∑ j : Fin (d + 1), x j.succ) := by
  unfold mixedCubeInput
  rw [cubeShift_true]
  exact congrArg (correlationInput (x 0)) (Fin.sum_univ_succ (fun j : Fin (d + 1) => x j.succ)).symm

theorem fullCubeSignal_profile {d N : ℕ} [NeZero N] (f : ZMod N → ℂ)
    (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ℤ) :
    fullCubeSignal (fun z : ℤ => f (z : ZMod N)) (mixedDifferencePoint t n) =
      cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N) := by
  have htuple : (fun j => ((mixedDifferencePoint t n ((1 : Fin (d + 3)).succAbove j) : ℤ) : ZMod N)) =
      Fin.cons (t.1 0) (mixedDifferenceShifts t) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [mixedDifferencePoint]
    · simp [Fin.one_succAbove_succ, mixedDifferencePoint]
  have hbase : mixedDifferencePoint t n 1 = n := rfl
  have hlist : List.ofFn t.1 = t.1 0 :: List.ofFn (Fin.tail t.1) := by
    rw [List.ofFn_succ]
    rfl
  unfold fullCubeSignal
  have hmap := cubeProduct_comp_addHom (Int.castAddHom (ZMod N)) f
    (List.ofFn (fun j => mixedDifferencePoint t n ((1 : Fin (d + 3)).succAbove j)))
    (mixedDifferencePoint t n 1)
  simp only [Int.coe_castAddHom] at hmap
  rw [hmap, List.map_ofFn]
  change cubeProduct f
    (List.ofFn (fun j => ((mixedDifferencePoint t n ((1 : Fin (d + 3)).succAbove j) : ℤ) : ZMod N)))
    ((mixedDifferencePoint t n 1 : ℤ) : ZMod N) = _
  rw [htuple, hbase, List.ofFn_cons, mixedDifferenceShifts, List.ofFn_cons, hlist]
  exact cubeProduct_swap_head f (t.1 0) t.2 _ _

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSeparatedSumIntervals
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_absorb_pair_missing_coordinate_errors (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} {D : RationalFilteredNilmanifold L s d}
      {E : RationalFilteredNilmanifold M s e} {p : ℝ}
      (T : D.Niltest (fun _ : Fin (s + 1) => 1))
      (U : E.Niltest (fun _ : Fin (s + 1) => 1)), T.ComplexityLE p → U.ComplexityLE p →
      ∀ {G X : Type*} (H : Finset G), H.Nonempty →
      ∀ (S : G → Finset X), (∀ h ∈ H, (S h).Nonempty) →
      ∀ (sample : G → X → Fin (s + 1) → ℤ) (f : G → X → ℂ),
      (∀ h ∈ H, ∀ x ∈ S h, ‖f h x‖ ≤ 1) →
      (∀ h ∈ H, Real.exp (-p) ≤
        ‖𝔼 x ∈ S h, f h x * star (T.eval (sample h x)) * star (U.eval (sample h x))‖) →
      ∃ A : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ,
        (∀ i x, ‖A i x‖ ≤ 1) ∧
        (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
        ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (H.card : ℝ) ≤ (H'.card : ℝ) ∧
          ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 x ∈ S h, f h x * ∏ i, A i (sample h x)‖ := by
  obtain ⟨a, _, habsorb⟩ := exists_absorb_missing_coordinate_error s
  let X : Polynomial ℕ := Polynomial.X
  let Q := (2 * X + Polynomial.C a) ^ a
  let R := (X + Q + 2 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + R)
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E p T U hT hU G Ω H hH S hS sample f hf hcorr
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hT.1.1
  let q := (2 * p + a) ^ a
  let t := p + q + 2
  let r := (t + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hqt : q ≤ t := by dsimp [t]; linarith
  have htotal : q + r ≤ (p + C) ^ C := by
    simpa [X, Q, R, q, t, r, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C := by linarith
  let V := U.expNormalize p
  have hV : V.ComplexityLE p := U.expNormalize_complexity hU
  have hVnorm (x : Fin (s + 1) → ℤ) : ‖V.eval x‖ ≤ 1 :=
    (V.norm_eval_le x).trans (U.expNormalize_norm hU)
  let g (h : G) (x : Ω) := f h x * star (V.eval (sample h x))
  have hg : ∀ h ∈ H, ∀ x ∈ S h, ‖g h x‖ ≤ 1 := by
    intro h hh x hx
    dsimp only [g]
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf h hh x hx)).trans (hVnorm _)
  have hgcorr : ∀ h ∈ H, Real.exp (-(2 * p)) ≤
      ‖𝔼 x ∈ S h, g h x * star (T.eval (sample h x))‖ := by
    intro h hh
    have heq : (𝔼 x ∈ S h, g h x * star (T.eval (sample h x))) =
        (Real.exp (-p) : ℂ) *
          (𝔼 x ∈ S h, f h x * star (T.eval (sample h x)) * star (U.eval (sample h x))) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      simp only [g, V, RationalFilteredNilmanifold.Niltest.expNormalize_eval,
        star_mul, Complex.star_def, Complex.conj_ofReal]
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    calc
      _ = Real.exp (-p) * Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcorr h hh) (Real.exp_nonneg _)
  obtain ⟨A, hA, hAind, H₁, hsub₁, hH₁, hsize₁, hcorr₁⟩ :=
    habsorb T (hT.mono (by linarith : p ≤ 2 * p)) H hH S hS sample g hg hgcorr
  let g₁ (h : G) (x : Ω) := f h x * ∏ i, A i (sample h x)
  have hg₁ : ∀ h ∈ H₁, ∀ x ∈ S h, ‖g₁ h x‖ ≤ 1 := by
    intro h hh x hx
    dsimp only [g₁]
    rw [norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) (hf h (hsub₁ hh) x hx)).trans
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hA i _)
  have hgcorr₁ : ∀ h ∈ H₁, Real.exp (-t) ≤
      ‖𝔼 x ∈ S h, g₁ h x * star (V.eval (sample h x))‖ := by
    intro h hh
    have heq : (𝔼 x ∈ S h, g h x * ∏ i, A i (sample h x)) =
        (𝔼 x ∈ S h, g₁ h x * star (V.eval (sample h x))) := by
      apply Finset.expect_congr rfl
      intro x _
      exact mul_right_comm _ _ _
    rw [← heq]
    exact (Real.exp_le_exp.mpr (neg_le_neg hqt)).trans (hcorr₁ h hh)
  obtain ⟨B, hB, hBind, H₂, hsub₂, hH₂, hsize₂, hcorr₂⟩ :=
    habsorb V (hV.mono hpt) H₁ hH₁ S (fun h hh => hS h (hsub₁ hh)) sample g₁ hg₁ hgcorr₁
  refine ⟨(fun i x => A i x * B i x), ?_, ?_, H₂, hsub₂.trans hsub₁, hH₂, ?_, ?_⟩
  · intro i x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hA i x)).trans (hB i x)
  · intro i x y hxy
    change A i x * B i x = A i y * B i y
    rw [hAind i x y hxy, hBind i x y hxy]
  · calc
      _ ≤ Real.exp (-(q + r)) * (H.card : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg htotal)) (Nat.cast_nonneg _)
      _ = Real.exp (-r) * (Real.exp (-q) * (H.card : ℝ)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-r) * (H₁.card : ℝ) := mul_le_mul_of_nonneg_left hsize₁ (Real.exp_nonneg _)
      _ ≤ _ := hsize₂
  · intro h hh
    simpa only [g₁, Finset.prod_mul_distrib, mul_assoc] using
      (Real.exp_le_exp.mpr (neg_le_neg hrC)).trans (hcorr₂ h hh)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_fullCube_proper_factors {G : Type*} [AddCommGroup G] {d : ℕ}
    (f : G → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1) :
    ∃ A : Fin (d + 3) → (Fin (d + 3) → G) → ℂ,
      (∀ i x, ‖A i x‖ ≤ 1) ∧
      (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
      ∀ x, fullCubeSignal f x = conjugationPower (d + 2) (f (∑ i, x i)) * ∏ i, A i x := by
  classical
  let S : Finset (Fin (d + 2) → Bool) := Finset.univ.erase (fun _ => true)
  let F (ω : S) (x : Fin (d + 3) → G) := conjugationPower (booleanWeight ω.val)
    (f (x 1 + cubeShift (fun j => x ((1 : Fin (d + 3)).succAbove j)) ω.val))
  have hF : ∀ ω x, ‖F ω x‖ ≤ 1 := by
    intro ω x
    exact (conjugationPower_norm _ _).trans_le (hf _)
  have hFi : ∀ ω, ∃ i, ∀ x y, (∀ k, k ≠ i → x k = y k) → F ω x = F ω y := by
    intro ω
    obtain ⟨j, hj⟩ := exists_false_of_ne_true (Finset.mem_erase.mp ω.property).1
    refine ⟨(1 : Fin (d + 3)).succAbove j, ?_⟩
    intro x y hxy
    exact congrArg (fun z => conjugationPower (booleanWeight ω.val) (f z))
      (fullCube_input_independent ω.val j hj x y hxy)
  obtain ⟨A, hA, hAi, hprod⟩ := exists_missing_coordinate_product_factors F hF hFi
  refine ⟨A, hA, hAi, ?_⟩
  intro x
  have hsum : x 1 + (∑ j : Fin (d + 2), x ((1 : Fin (d + 3)).succAbove j)) = ∑ i, x i :=
    (Fin.sum_univ_succAbove x 1).symm
  calc
    fullCubeSignal f x = conjugationPower (d + 2) (f (∑ i, x i)) *
        ∏ ω ∈ S, conjugationPower (booleanWeight ω)
          (f (x 1 + cubeShift (fun j => x ((1 : Fin (d + 3)).succAbove j)) ω)) := by
      unfold fullCubeSignal
      rw [cubeProduct_eq_boolean_product]
      rw [← Finset.mul_prod_erase Finset.univ
        (fun ω => conjugationPower (booleanWeight ω)
          (f (x 1 + cubeShift (fun j => x ((1 : Fin (d + 3)).succAbove j)) ω)))
        (Finset.mem_univ (fun _ : Fin (d + 2) => true))]
      rw [booleanWeight_true, cubeShift_true, hsum]
    _ = _ := by
      rw [hprod]
      congr 1
      exact (Finset.prod_coe_sort S (fun ω => conjugationPower (booleanWeight ω)
        (f (x 1 + cubeShift (fun j => x ((1 : Fin (d + 3)).succAbove j)) ω)))).symm

theorem exists_mixedCube_proper_factors {J : Type*} {d : ℕ}
    (η : J → (Fin 2 → ℤ) → ℂ) (hη : ∀ j x, ‖η j x‖ ≤ 1) (w : (Fin d → Bool) → J) :
    ∃ A : Fin (d + 2) → (Fin (d + 2) → ℤ) → ℂ,
      (∀ i x, ‖A i x‖ ≤ 1) ∧
      (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
      ∀ x, mixedCubeObservable η w x =
        conjugationPower d (η (w (fun _ => true)) (correlationInput (x 0) (∑ j : Fin (d + 1), x j.succ))) *
          ∏ i, A i x := by
  classical
  let S : Finset (Fin d → Bool) := Finset.univ.erase (fun _ => true)
  let F (ω : S) (x : Fin (d + 2) → ℤ) :=
    conjugationPower (booleanWeight ω.val) (η (w ω.val) (mixedCubeInput ω.val x))
  have hF : ∀ ω x, ‖F ω x‖ ≤ 1 := by
    intro ω x
    exact (conjugationPower_norm _ _).trans_le (hη _ _)
  have hFi : ∀ ω, ∃ i, ∀ x y, (∀ k, k ≠ i → x k = y k) → F ω x = F ω y := by
    intro ω
    obtain ⟨j, hj⟩ := exists_false_of_ne_true (Finset.mem_erase.mp ω.property).1
    refine ⟨j.succ.succ, ?_⟩
    intro x y hxy
    exact congrArg (fun z => conjugationPower (booleanWeight ω.val) (η (w ω.val) z))
      (mixedCubeInput_independent ω.val j hj x y hxy)
  obtain ⟨A, hA, hAi, hprod⟩ := exists_missing_coordinate_product_factors F hF hFi
  refine ⟨A, hA, hAi, ?_⟩
  intro x
  calc
    mixedCubeObservable η w x =
        conjugationPower d (η (w (fun _ => true)) (correlationInput (x 0) (∑ j : Fin (d + 1), x j.succ))) *
          ∏ ω ∈ S, conjugationPower (booleanWeight ω) (η (w ω) (mixedCubeInput ω x)) := by
      unfold mixedCubeObservable
      rw [← Finset.mul_prod_erase Finset.univ
        (fun ω => conjugationPower (booleanWeight ω) (η (w ω) (mixedCubeInput ω x)))
        (Finset.mem_univ (fun _ : Fin d => true))]
      rw [booleanWeight_true, mixedCubeInput_true]
    _ = _ := by
      rw [hprod]
      congr 1
      exact (Finset.prod_coe_sort S (fun ω => conjugationPower (booleanWeight ω)
        (η (w ω) (mixedCubeInput ω x)))).symm

theorem exists_full_mixed_cube_proper_factors {J : Type*} {d : ℕ}
    (f : ℤ → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1)
    (η : J → (Fin 2 → ℤ) → ℂ) (hη : ∀ j x, ‖η j x‖ ≤ 1) (w : (Fin (d + 1) → Bool) → J) :
    ∃ A : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ,
      (∀ i x, ‖A i x‖ ≤ 1) ∧
      (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
      ∀ x, fullCubeSignal f x * star (mixedCubeObservable η w x) =
        conjugationPower (d + 2) (f (∑ i, x i) *
          η (w (fun _ => true)) (correlationInput (x 0) (∑ j : Fin (d + 2), x j.succ))) *
            ∏ i, A i x := by
  obtain ⟨A, hA, hAi, hAfactor⟩ := exists_fullCube_proper_factors (d := d) f hf
  obtain ⟨B, hB, hBi, hBfactor⟩ := exists_mixedCube_proper_factors η hη w
  refine ⟨(fun i x => A i x * star (B i x)), ?_, ?_, ?_⟩
  · intro i x
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hA i x)).trans (hB i x)
  · intro i x y hxy
    change A i x * star (B i x) = A i y * star (B i y)
    rw [hAi i x y hxy, hBi i x y hxy]
  · intro x
    have hstep (z : ℂ) : conjugationPower (d + 2) z = star (conjugationPower (d + 1) z) := rfl
    rw [hAfactor, hBfactor]
    simp only [Finset.prod_mul_distrib, star_prod, map_mul, hstep, star_mul]
    ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_normalized_cube_weights {J : Type*} {d : ℕ}
    (f : ℤ → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1)
    (η : J → (Fin 2 → ℤ) → ℂ) (hη : ∀ j x, ‖η j x‖ ≤ 1) (w : (Fin (d + 1) → Bool) → J)
    (A : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ) (hA : ∀ i x, ‖A i x‖ ≤ 1)
    (hAi : ∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) :
    ∃ B : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ,
      (∀ i x, ‖B i x‖ ≤ 1) ∧
      (∀ i x y, (∀ k, k ≠ i → x k = y k) → B i x = B i y) ∧
      ∀ x, conjugationPower (d + 3)
          ((fullCubeSignal f x * star (mixedCubeObservable η w x)) * ∏ i, A i x) =
        star (f (∑ i, x i)) *
          star (η (w (fun _ => true)) (correlationInput (x 0) (∑ j : Fin (d + 2), x j.succ))) *
            ∏ i, B i x := by
  obtain ⟨P, hP, hPi, hfactor⟩ := exists_full_mixed_cube_proper_factors f hf η hη w
  refine ⟨(fun i x => conjugationPower (d + 3) (P i x * A i x)), ?_, ?_, ?_⟩
  · intro i x
    change ‖conjugationPower (d + 3) (P i x * A i x)‖ ≤ 1
    rw [conjugationPower_norm, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hP i x)).trans (hA i x)
  · intro i x y hxy
    change conjugationPower (d + 3) (P i x * A i x) = conjugationPower (d + 3) (P i y * A i y)
    rw [hPi i x y hxy, hAi i x y hxy]
  · intro x
    rw [hfactor]
    have hprod : (conjugationPower (d + 2) (f (∑ i, x i) *
        η (w (fun _ => true)) (correlationInput (x 0) (∑ j : Fin (d + 2), x j.succ))) * ∏ i, P i x) *
          (∏ i, A i x) =
        conjugationPower (d + 2) (f (∑ i, x i) *
          η (w (fun _ => true)) (correlationInput (x 0) (∑ j : Fin (d + 2), x j.succ))) *
            ∏ i, P i x * A i x := by
      rw [Finset.prod_mul_distrib]
      ring
    rw [hprod, map_mul, conjugationPower_next_self, map_prod, star_mul]
    ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_absorb_fixed_target_cube_errors (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {J : Type*} [Fintype J] {N : ℕ} [NeZero N] {p q : ℝ}, 0 ≤ q →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      ∀ (M : NativeMixedCorrelation (d + 2) N p f) (η : J → (Fin 2 → ℤ) → ℂ),
      (∀ j x, ‖η j x‖ ≤ 1) → HasFixedTargetCubeIntervals f M η q →
      HasWeightedTargetCubeIntervals f M η ((q + C) ^ C) := by
  obtain ⟨a, _, habsorb⟩ := exists_absorb_pair_missing_coordinate_errors (d + 2)
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + P)
  refine ⟨C, hC, ?_⟩
  intro J _ N _ p q hq f hf M η hη H
  classical
  let r := (q + a) ^ a
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : q + r ≤ (q + C) ^ C := by
    simpa [X, P, r, Polynomial.eval₂_pow] using hbudget q hq
  have hqC : q ≤ (q + C) ^ C := by linarith
  have hrC : r ≤ (q + C) ^ C := by linarith
  obtain ⟨r₀, u, hr₀, hr₀q, hu, huq, E, F, i, b, v, l, w, z, Q, hQ, hdense, hcorr⟩ := H
  let T := ((E b).selectedExpansion (fun _ => i) v).test l
  let U := (F.selectedExpansion v w).test z
  have hT : T.ComplexityLE q := (((E b).selectedExpansion (fun _ => i) v).complexity l).mono hr₀q
  have hU : U.ComplexityLE q := ((F.selectedExpansion v w).complexity z).mono huq
  have hdata (t : Q) := hcorr t.val t.property
  choose hshift start len hlen hend hshort hvol hcor using hdata
  let I (t : Q) := Finset.Ico (start t : ℤ) (start t + len t)
  let sample (t : Q) := mixedDifferencePoint t.val
  let signal (t : Q) (n : ℤ) := cubeProduct f (t.val.2 :: List.ofFn t.val.1) (n : ZMod N) *
    star (mixedCubeObservable η w (sample t n))
  let : Nonempty Q := hQ.to_subtype
  have hI (t : Q) : (I t).Nonempty := Finset.nonempty_Ico.mpr (by
    have hh := hlen t
    change (start t : ℤ) < start t + len t
    omega)
  have hsignal (t : Q) (n : ℤ) : ‖signal t n‖ ≤ 1 := by
    dsimp only [signal]
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (cubeProduct_norm_le_one f hf _ _)).trans
      (mixedCubeObservable_norm_le_one η hη w _)
  obtain ⟨A, hA, hAi, S, _, hS, hSdense, hScor⟩ := habsorb T U hT hU
    Finset.univ Finset.univ_nonempty I (fun t _ => hI t) sample signal
    (fun t _ n _ => hsignal t n) (fun t _ => hcor t)
  let embed : Q ↪ ((Fin (d + 1) → ZMod N) × ZMod N) := ⟨Subtype.val, Subtype.val_injective⟩
  let Q' := S.map embed
  have hQ' : Q'.Nonempty := hS.map
  have hsize : Real.exp (-r) * (Q.card : ℝ) ≤ (Q'.card : ℝ) := by
    simpa only [Q', Finset.card_map, Finset.card_univ, Fintype.card_coe] using hSdense
  refine ⟨w, A, hA, hAi, Q', hQ', ?_, ?_⟩
  · calc
      _ ≤ Real.exp (-(q + r)) * (N : ℝ) ^ (d + 2) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg htotal)) (by positivity)
      _ = Real.exp (-r) * (Real.exp (-q) * (N : ℝ) ^ (d + 2)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-r) * (Q.card : ℝ) := mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
    exact ⟨hshift t', start t', len t', hlen t', hend t', hshort t',
      (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hvol t'),
      (Real.exp_le_exp.mpr (neg_le_neg hrC)).trans (hScor t' ht')⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def HasSumTargetIntervals {J : Type*} [Fintype J] {d N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (M : NativeMixedCorrelation (d + 2) N p f)
    (η : J → (Fin 2 → ℤ) → ℂ) (q : ℝ) : Prop :=
  ∃ (j : J) (A : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ),
    (∀ i x, ‖A i x‖ ≤ 1) ∧
    (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
    ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
      Real.exp (-q) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.1 0 ∈ M.shifts ∧ ∃ a len : ℕ,
        0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
        Real.exp (-q) ≤ (len : ℝ) / N ∧ Real.exp (-q) ≤
          ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
            star (f ((∑ k, mixedDifferencePoint t n k : ℤ) : ZMod N)) *
              star (η j (correlationInput (mixedDifferencePoint t n 0)
                (∑ k : Fin (d + 2), mixedDifferencePoint t n k.succ))) *
              ∏ i, A i (mixedDifferencePoint t n)‖

theorem HasSumTargetIntervals.mono {J : Type*} [Fintype J] {d N : ℕ} [NeZero N]
    {p q q' : ℝ} {f : ZMod N → ℂ} {M : NativeMixedCorrelation (d + 2) N p f}
    {η : J → (Fin 2 → ℤ) → ℂ} (H : HasSumTargetIntervals f M η q) (hqq' : q ≤ q') :
    HasSumTargetIntervals f M η q' := by
  obtain ⟨j, A, hA, hAi, Q, hQ, hdense, hcorr⟩ := H
  refine ⟨j, A, hA, hAi, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqq'))
      (pow_nonneg (Nat.cast_nonneg N) _)).trans hdense
  · intro t ht
    obtain ⟨hs, a, len, hlen, hend, hshort, hvol, hc⟩ := hcorr t ht
    exact ⟨hs, a, len, hlen, hend, hshort,
      (Real.exp_le_exp.mpr (neg_le_neg hqq')).trans hvol,
      (Real.exp_le_exp.mpr (neg_le_neg hqq')).trans hc⟩

theorem HasWeightedTargetCubeIntervals.to_sum {J : Type*} [Fintype J] {d N : ℕ} [NeZero N]
    {p q : ℝ} {f : ZMod N → ℂ} {M : NativeMixedCorrelation (d + 2) N p f}
    {η : J → (Fin 2 → ℤ) → ℂ} (H : HasWeightedTargetCubeIntervals f M η q)
    (hf : ∀ z, ‖f z‖ ≤ 1) (hη : ∀ j x, ‖η j x‖ ≤ 1) : HasSumTargetIntervals f M η q := by
  obtain ⟨w, A, hA, hAi, Q, hQ, hdense, hcorr⟩ := H
  obtain ⟨B, hB, hBi, hnorm⟩ := exists_normalized_cube_weights
    (fun z : ℤ => f (z : ZMod N)) (fun z => hf _) η hη w A hA hAi
  refine ⟨w (fun _ => true), B, hB, hBi, Q, hQ, hdense, ?_⟩
  intro t ht
  obtain ⟨hs, a, len, hlen, hend, hshort, hvol, hc⟩ := hcorr t ht
  refine ⟨hs, a, len, hlen, hend, hshort, hvol, ?_⟩
  have hpoint (n : ℤ) :
      conjugationPower (d + 3)
        ((cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N) *
          star (mixedCubeObservable η w (mixedDifferencePoint t n))) * ∏ i, A i (mixedDifferencePoint t n)) =
      star (f ((∑ k, mixedDifferencePoint t n k : ℤ) : ZMod N)) *
        star (η (w (fun _ => true)) (correlationInput (mixedDifferencePoint t n 0)
          (∑ k : Fin (d + 2), mixedDifferencePoint t n k.succ))) *
        ∏ i, B i (mixedDifferencePoint t n) := by
    simpa only [fullCubeSignal_profile] using hnorm (mixedDifferencePoint t n)
  have hc' := hc.trans_eq (norm_expect_conjugationPower (Finset.Ico (a : ℤ) (a + len)) (d + 3)
    (fun n => (cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N) *
      star (mixedCubeObservable η w (mixedDifferencePoint t n))) * ∏ i, A i (mixedDifferencePoint t n))).symm
  simpa only [hpoint] using hc'

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def HasMixedTargetIntervals {J : Type*} {d N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (M : NativeMixedCorrelation (d + 2) N p f)
    (η : J → (Fin (d + 3) → ℤ) → ℂ) (q : ℝ) : Prop :=
  ∃ (j : J) (A : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ),
    (∀ i x, ‖A i x‖ ≤ 1) ∧
    (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
    ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
      Real.exp (-q) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.1 0 ∈ M.shifts ∧ ∃ a len : ℕ,
        0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
        Real.exp (-q) ≤ (len : ℝ) / N ∧ Real.exp (-q) ≤
          ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
            star (f ((∑ k, mixedDifferencePoint t n k : ℤ) : ZMod N)) *
              star (η j (mixedDifferencePoint t n)) * ∏ i, A i (mixedDifferencePoint t n)‖

def HasCommonMixedTargetInterval {J : Type*} {d N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (M : NativeMixedCorrelation (d + 2) N p f)
    (η : J → (Fin (d + 3) → ℤ) → ℂ) (q : ℝ) : Prop :=
  ∃ (j : J) (A : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ),
    (∀ i x, ‖A i x‖ ≤ 1) ∧
    (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
    ∃ a len : ℕ, 0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
      Real.exp (-q) ≤ (len : ℝ) / N ∧
      ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
        Real.exp (-q) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
        ∀ t ∈ Q, t.1 0 ∈ M.shifts ∧ Real.exp (-q) ≤
          ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
            star (f ((∑ k, mixedDifferencePoint t n k : ℤ) : ZMod N)) *
              star (η j (mixedDifferencePoint t n)) * ∏ i, A i (mixedDifferencePoint t n)‖

end Erdos3

end

section

namespace Erdos3

theorem exists_retained_sum_target_intervals (d : ℕ) {A : ℕ}
    (hI : CyclicNativeInverse (d + 2) A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter
        (fun _ : ReplicatedIndex (mixedCorrelationDegree (d + 2)) => 1) q,
        W.dim ≤ 2 ^ (d + 3) * M.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence (d + 2) q M.mixed.eval
          (fun k x => W.eval k (fun j => x j.1)) ∧
        HasSumTargetIntervals f M (fun k x => W.eval k (fun j => x j.1)) ((p + C) ^ C) := by
  obtain ⟨a, _, hretained⟩ := exists_retained_target_cube_intervals d hI
  obtain ⟨b, _, habsorb⟩ := exists_absorb_fixed_target_cube_errors d
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  let R := (P + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + R)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let q := (p + a) ^ a
  let r := (q + b) ^ b
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : q + r ≤ (p + C) ^ C := by
    simpa [X, P, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hrC : r ≤ (p + C) ^ C := by linarith
  obtain ⟨q₀, hq₀, hq₀q, M, W, hdim, hsym, E, H⟩ :=
    hretained hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hG
  have hW : ∀ (k : Fin W.outputDim) (x : Fin 2 → ℤ),
      ‖W.eval k (fun j => x j.1)‖ ≤ 1 := fun k x => W.norm_eval k _
  have Hweighted := habsorb hq f hf M (fun k x => W.eval k (fun j => x j.1)) hW H
  exact ⟨q₀, hq₀, hq₀q.trans hqC, M, W, hdim, hsym, E, (Hweighted.to_sum hf hW).mono hrC⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem HasMixedTargetIntervals.common {J : Type*} {d N : ℕ} [NeZero N] {p q : ℝ}
    {f : ZMod N → ℂ} {M : NativeMixedCorrelation (d + 2) N p f}
    {η : J → (Fin (d + 3) → ℤ) → ℂ} (H : HasMixedTargetIntervals f M η q)
    (hq : 0 ≤ q) (hN : Real.exp (2 * q + 8) ≤ (N : ℝ))
    (hf : ∀ x, ‖f x‖ ≤ 1) (hη : ∀ j x, ‖η j x‖ ≤ 1) :
    HasCommonMixedTargetInterval f M η (5 * q + 10) := by
  classical
  obtain ⟨j, A, hA, hAi, Q, hQ, hdense, hcorr⟩ := H
  have hdata (t : Q) := hcorr t.val t.property
  choose hshift start len hlen hend hshort hvol hcor using hdata
  let signal (t : Q) (n : ℤ) :=
    star (f ((∑ k, mixedDifferencePoint t.val n k : ℤ) : ZMod N)) *
      star (η j (mixedDifferencePoint t.val n)) * ∏ i, A i (mixedDifferencePoint t.val n)
  let : Nonempty Q := hQ.to_subtype
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hsignal (t : Q) (n : ℤ) : ‖signal t n‖ ≤ 1 := by
    dsimp only [signal]
    rw [norm_mul, norm_mul, norm_star, norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _)
      ((mul_le_of_le_one_left (norm_nonneg _) (hf _)).trans (hη j _))).trans
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => hA i _)
  obtain ⟨S, _, hS, hSdense, a, len', hlen', hend', hshort', hvol', hScor⟩ :=
    exists_common_integer_interval hq hN Finset.univ Finset.univ_nonempty start len
      (fun t _ => hend t) (fun t _ => hshort t)
      (fun t _ => (le_div_iff₀ hNpos).mp (hvol t)) signal
      (fun t _ n => hsignal t n) (fun t _ => hcor t)
  let embed : Q ↪ ((Fin (d + 1) → ZMod N) × ZMod N) := ⟨Subtype.val, Subtype.val_injective⟩
  let Q' := S.map embed
  have hsize : Real.exp (-(4 * q + 10)) * (Q.card : ℝ) ≤ (Q'.card : ℝ) := by
    simpa only [Q', Finset.card_map, Finset.card_univ, Fintype.card_coe] using hSdense
  have hbudget : q + 1 ≤ 5 * q + 10 := by linarith
  refine ⟨j, A, hA, hAi, a, len', hlen', hend', hshort', ?_, Q', hS.map, ?_, ?_⟩
  · apply (le_div_iff₀ hNpos).mpr
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hbudget)) hNpos.le).trans hvol'
  · calc
      _ = Real.exp (-(4 * q + 10)) * (Real.exp (-q) * (N : ℝ) ^ (d + 2)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-(4 * q + 10)) * (Q.card : ℝ) :=
        mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
    exact ⟨hshift t', (Real.exp_le_exp.mpr (neg_le_neg hbudget)).trans (hScor t' ht')⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_separated_sum_intervals (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p q r : ℝ}, 0 ≤ q → r ≤ q →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      ∀ (M : NativeMixedCorrelation (d + 2) N p f)
        (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) r),
      (∀ (e : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) k x,
        W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) e).symm j)) = W.eval k x) →
      HasSumTargetIntervals f M (fun k x => W.eval k (fun j => x j.1)) q →
      HasMixedTargetIntervals f M
        (fun k x => (W.tensorPower (d + 2).factorial).eval k
          (mixedReplicatedInput (x 0) (fun j => x j.succ))) ((q + C) ^ C) := by
  obtain ⟨a, _, hseparate⟩ := NativeMultidegreeNilcharacter.exists_mixed_separated_family
    (d + 2) (by omega)
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + P)
  refine ⟨C, hC, ?_⟩
  intro N _ p q r hq hrq f hf M W hsym H
  classical
  let v := (q + a) ^ a
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have htotal : q + v ≤ (q + C) ^ C := by
    simpa [X, P, v, Polynomial.eval₂_pow] using hbudget q hq
  have hqC : q ≤ (q + C) ^ C := by linarith
  have hvC : v ≤ (q + C) ^ C := by linarith
  obtain ⟨j, A, hA, hAi, Q, hQ, hdense, hcorr⟩ := H
  have hdata (t : Q) := hcorr t.val t.property
  choose hshift start len hlen hend hshort hvol hcor using hdata
  let I (t : Q) := Finset.Ico (start t : ℤ) (start t + len t)
  let sample (t : Q) := mixedDifferencePoint t.val
  let signal (t : Q) (n : ℤ) := star (f ((∑ k, sample t n k : ℤ) : ZMod N))
  let : Nonempty Q := hQ.to_subtype
  have hI (t : Q) : (I t).Nonempty := Finset.nonempty_Ico.mpr (by
    have hh := hlen t
    change (start t : ℤ) < start t + len t
    omega)
  obtain ⟨a', B, hB, hBi, S, _, hS, hSdense, hScor⟩ := hseparate (W.mono hrq) hsym
    Finset.univ Finset.univ_nonempty I (fun t _ => hI t) sample signal
    (fun t _ n _ => by simpa only [signal, norm_star] using hf _) j A hA hAi
    (fun t _ => by simpa only [I, signal, sample, mixedReplicatedInput_diagonal, NativeMultidegreeNilcharacter.mono_eval] using hcor t)
  let embed : Q ↪ ((Fin (d + 1) → ZMod N) × ZMod N) := ⟨Subtype.val, Subtype.val_injective⟩
  let Q' := S.map embed
  have hsize : Real.exp (-v) * (Q.card : ℝ) ≤ (Q'.card : ℝ) := by
    simpa only [Q', Finset.card_map, Finset.card_univ, Fintype.card_coe] using hSdense
  have htarget (x : Fin (d + 3) → ℤ) :
      (W.tensorPower (d + 2).factorial).eval (mixedPermutationTensorIndex W.outputDim a')
        (mixedReplicatedInput (x 0) (fun j => x j.succ)) =
      mixedPermutationProduct (W.mono hrq).eval a' x :=
    (W.mixedPermutationProduct_tensorPower a' x).symm
  refine ⟨mixedPermutationTensorIndex W.outputDim a', B, hB, hBi, Q', hS.map, ?_, ?_⟩
  · calc
      _ ≤ Real.exp (-(q + v)) * (N : ℝ) ^ (d + 2) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg htotal)) (by positivity)
      _ = Real.exp (-v) * (Real.exp (-q) * (N : ℝ) ^ (d + 2)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-v) * (Q.card : ℝ) := mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
    refine ⟨hshift t', start t', len t', hlen t', hend t', hshort t',
      (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hvol t'), ?_⟩
    simpa only [htarget, I, signal, sample, embed, Function.Embedding.coeFn_mk] using (Real.exp_le_exp.mpr (neg_le_neg hvC)).trans (hScor t' ht')

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedProfileCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def mixedProfileFromCoordinates {d : ℕ} {α : Type*} (x : Fin (d + 3) → α) :
    (Fin (d + 1) → α) × α :=
  (Fin.cons (x 0) (fun j => x j.succ.succ.succ), x 2)

def mixedProfileEquiv (d : ℕ) (α : Type*) :
    (((Fin (d + 1) → α) × α) × α) ≃ (Fin (d + 3) → α) where
  toFun t := Fin.cons (t.1.1 0) (Fin.cons t.2 (Fin.cons t.1.2 (Fin.tail t.1.1)))
  invFun x := (mixedProfileFromCoordinates x, x 1)
  left_inv := by
    rintro ⟨⟨t, u⟩, n⟩
    apply Prod.ext
    · apply Prod.ext
      · funext i
        exact Fin.cases rfl (fun _ => rfl) i
      · rfl
    · rfl
  right_inv := by
    intro x
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun _ => rfl) k

theorem mixedProfileFromCoordinates_independent {d : ℕ} {α : Type*}
    (x y : Fin (d + 3) → α) (h : ∀ k, k ≠ 1 → x k = y k) :
    mixedProfileFromCoordinates x = mixedProfileFromCoordinates y := by
  have h1 : (1 : Fin (d + 3)).val = 1 := Fin.val_one (d + 1)
  have h2 : (2 : Fin (d + 3)).val = 2 := by
    change 2 % (d + 3) = 2
    exact Nat.mod_eq_of_lt (by omega)
  apply Prod.ext
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h 0 (by
        intro e
        have he := congrArg Fin.val e
        norm_num only [Fin.val_zero, h1] at he)
    · exact h j.succ.succ.succ (by
        intro e
        have he := congrArg Fin.val e
        simp only [Fin.val_succ, h1] at he
        omega)
  · exact h 2 (by
      intro e
      have he := congrArg Fin.val e
      norm_num only [h2, h1] at he)

theorem mixedProfileFromCoordinates_point {d N : ℕ} [NeZero N]
    (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ℤ) :
    mixedProfileFromCoordinates (fun i => (mixedDifferencePoint t n i : ZMod N)) = t := by
  apply Prod.ext
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [mixedProfileFromCoordinates, mixedDifferencePoint, mixedDifferenceShifts]
  · change ((t.2.val : ℤ) : ZMod N) = t.2
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem mixedProfileEquiv_point {d N : ℕ}
    (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ZMod N) :
    (fun i => ((mixedProfileEquiv d (ZMod N) (t, n) i).val : ℤ)) =
      mixedDifferencePoint t (n.val : ℤ) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => ?_) j
  exact Fin.cases rfl (fun _ => rfl) k

theorem mixedProfile_average {d : ℕ} {α : Type*} [Fintype α]
    (F : (Fin (d + 3) → α) → ℂ) :
    (𝔼 x, F x) = 𝔼 t : (Fin (d + 1) → α) × α, 𝔼 n : α,
      F (mixedProfileEquiv d α (t, n)) := by
  calc
    _ = 𝔼 t : ((Fin (d + 1) → α) × α) × α, F (mixedProfileEquiv d α t) :=
      (Fintype.expect_equiv (mixedProfileEquiv d α) _ F (fun _ => rfl)).symm
    _ = _ := expect_prod_split _

theorem mixedProfile_card (d N : ℕ) [NeZero N] :
    Fintype.card ((Fin (d + 1) → ZMod N) × ZMod N) = N ^ (d + 2) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card, pow_succ]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPrimitiveGowers
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_mixed_sum_pair_factors (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      {N : ℕ} [NeZero N] (f : ZMod N → ℂ), (∀ x, ‖f x‖ ≤ 1) →
      ∀ (i : Fin W.outputDim) (A : Fin (n + 2) → (Fin (n + 2) → ZMod N) → ℂ),
      (∀ j x, ‖A j x‖ ≤ 1) → (∀ j, MissesBoxCoordinate (A j) j) →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      Real.exp (-p) ≤ ‖𝔼 u : Fin n → ZMod N, 𝔼 m : ZMod N, 𝔼 h : ZMod N,
        f (m + h + ∑ j, u j) * star (W.eval i (mixedSlotInput (h.val : ℤ) m.val (fun j => (u j).val))) *
          ∏ j, A j (Fin.cons h (Fin.cons m u))‖ →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ (j k : Fin W.outputDim)
        (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
          Finset.univ (fun x : Fin (n + 2) → ZMod N => fun l => ((x l).val : ℤ))
          (fun x => W.mixedAntisymmetric j k (fun l => ((x l).val : ℤ)))),
        Nonempty (NativePolynomialOrbitFactors (pi V.mixedPairModels)
          V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
          (fun _ : Fin (n + 2) => (N : ℝ)) ((p + C) ^ C)) := by
  obtain ⟨a, _, hkernel⟩ := NativeMultidegreeNilcharacter.exists_mixed_sum_kernel_correlation n
  obtain ⟨b, _, hstep⟩ := exists_mixed_pair_step_drop n
  obtain ⟨c, _, horbit⟩ := exists_mixed_pair_orbit_factors n
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a
  let U := (X + Q + Polynomial.C b) ^ b
  let T := (X + Q + U + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + U + T)
  refine ⟨C, hC, ?_⟩
  intro p W N _ f hf i A hA hmiss hN hcorr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + a) ^ a
  let u := (p + q + b) ^ b
  let t := (p + q + u + c) ^ c
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hsum : q + u + t ≤ (p + C) ^ C := by
    simpa [X, Q, U, T, q, u, t, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hsum, hu, ht]
  have huC : u ≤ (p + C) ^ C := by linarith only [hsum, hq, ht]
  have htC : t ≤ (p + C) ^ C := by linarith only [hsum, hq, hu]
  obtain ⟨j, k, ⟨V⟩⟩ := hkernel W f hf i A hA hmiss hcorr
  obtain ⟨F⟩ := hstep (W := W) V ((Real.exp_le_exp.mpr huC).trans hN)
  obtain ⟨O⟩ := horbit (W := W) F hu ((Real.exp_le_exp.mpr htC).trans hN)
  exact ⟨q, hq, hqC, j, k, V, ⟨O.mono htC (fun _ => by exact_mod_cast NeZero.pos N)⟩⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def HasPositiveMixedTargetInterval {J : Type*} {d N : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (η : J → (Fin (d + 3) → ℤ) → ℂ) (q : ℝ) : Prop :=
  ∃ (j : J) (A : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ),
    (∀ i x, ‖A i x‖ ≤ 1) ∧
    (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
    ∃ a len : ℕ, 0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
      Real.exp (-q) ≤ (len : ℝ) / N ∧ Real.exp (-q) ≤
        (𝔼 t : (Fin (d + 1) → ZMod N) × ZMod N,
          𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
            star (f ((∑ k, mixedDifferencePoint t n k : ℤ) : ZMod N)) *
              star (η j (mixedDifferencePoint t n)) * ∏ i, A i (mixedDifferencePoint t n)).re

theorem HasCommonMixedTargetInterval.positive {J : Type*} {d N : ℕ} [NeZero N] {p q : ℝ}
    {f : ZMod N → ℂ} {M : NativeMixedCorrelation (d + 2) N p f}
    {η : J → (Fin (d + 3) → ℤ) → ℂ} (H : HasCommonMixedTargetInterval f M η q)
    (hq : 0 ≤ q) : HasPositiveMixedTargetInterval f η (2 * q) := by
  classical
  obtain ⟨j, A, hA, hAi, a, len, hlen, hend, hshort, hvol, Q, _, hdense, hcorr⟩ := H
  let row (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ℤ) :=
    star (f ((∑ k, mixedDifferencePoint t n k : ℤ) : ZMod N)) *
      star (η j (mixedDifferencePoint t n)) * ∏ i, A i (mixedDifferencePoint t n)
  have hdensity : Real.exp (-q) * Fintype.card ((Fin (d + 1) → ZMod N) × ZMod N) ≤
      (Q.card : ℝ) := by
    simpa only [mixedProfile_card, Nat.cast_pow] using hdense
  obtain ⟨w, hw, _, hpositive⟩ := exists_dense_row_phase_alignment Q
    (Finset.Ico (a : ℤ) (a + len)) row (Real.exp_nonneg (-q)) hdensity
      (fun t ht => (hcorr t ht).2)
  let phase (x : Fin (d + 3) → ℤ) :=
    w (mixedProfileFromCoordinates (fun k => (x k : ZMod N)))
  let B (i : Fin (d + 3)) (x : Fin (d + 3) → ℤ) :=
    (if i = 1 then phase x else 1) * A i x
  have hB : ∀ i x, ‖B i x‖ ≤ 1 := by
    intro i x
    by_cases hi : i = 1
    · simp only [B, hi, ite_true, norm_mul]
      exact (mul_le_mul_of_nonneg_right (hw _) (norm_nonneg _)).trans (by
        simpa only [one_mul] using hA 1 x)
    · simpa only [B, hi, ite_false, one_mul] using hA i x
  have hBi : ∀ i x y, (∀ k, k ≠ i → x k = y k) → B i x = B i y := by
    intro i x y hxy
    by_cases hi : i = 1
    · subst i
      simp only [B, ite_true]
      rw [hAi 1 x y hxy]
      congr 1
      apply congrArg w
      exact mixedProfileFromCoordinates_independent _ _ (fun k hk => congrArg (fun z : ℤ => (z : ZMod N)) (hxy k hk))
    · simpa only [B, hi, ite_false, one_mul] using hAi i x y hxy
  have hphase (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ℤ) :
      phase (mixedDifferencePoint t n) = w t := by
    exact congrArg w (mixedProfileFromCoordinates_point t n)
  have hprod (x : Fin (d + 3) → ℤ) : (∏ i, B i x) = phase x * ∏ i, A i x := by
    simp only [B, Finset.prod_mul_distrib]
    simp
  have hpoint (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ℤ) :
      star (f ((∑ k, mixedDifferencePoint t n k : ℤ) : ZMod N)) *
        star (η j (mixedDifferencePoint t n)) * ∏ i, B i (mixedDifferencePoint t n) = w t * row t n := by
    rw [hprod, hphase]
    dsimp only [row]
    ring
  refine ⟨j, B, hB, hBi, a, len, hlen, hend, hshort,
    (Real.exp_le_exp.mpr (by linarith : -(2 * q) ≤ -q)).trans hvol, ?_⟩
  have hscore : Real.exp (-(2 * q)) ≤
      (𝔼 t, 𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), w t * row t n).re := by
    have heq : Real.exp (-(2 * q)) = Real.exp (-q) * Real.exp (-q) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact hpositive
  simpa only [hpoint] using hscore

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def HasCyclicMixedTargetCorrelation {J : Type*} {d N : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (η : J → (Fin (d + 3) → ℤ) → ℂ) (q : ℝ) : Prop :=
  ∃ (j : J) (A : Fin (d + 3) → (Fin (d + 3) → ZMod N) → ℂ),
    (∀ i x, ‖A i x‖ ≤ 1) ∧
    (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
    Real.exp (-q) ≤ ‖𝔼 x : Fin (d + 3) → ZMod N,
      star (f (∑ k, x k)) * star (η j (fun k => ((x k).val : ℤ))) * ∏ i, A i x‖

theorem HasCyclicMixedTargetCorrelation.mono {J : Type*} {d N : ℕ} [NeZero N] {q q' : ℝ}
    {f : ZMod N → ℂ} {η : J → (Fin (d + 3) → ℤ) → ℂ}
    (H : HasCyclicMixedTargetCorrelation f η q) (hqq' : q ≤ q') :
    HasCyclicMixedTargetCorrelation f η q' := by
  obtain ⟨j, A, hA, hAi, hc⟩ := H
  exact ⟨j, A, hA, hAi, (Real.exp_le_exp.mpr (neg_le_neg hqq')).trans hc⟩

theorem exists_mixed_interval_cutoff_weights {d N : ℕ} [NeZero N]
    (I : Finset (ZMod N)) (A : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ)
    (hA : ∀ i x, ‖A i x‖ ≤ 1)
    (hAi : ∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) :
    ∃ B : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ,
      (∀ i x, ‖B i x‖ ≤ 1) ∧
      (∀ i x y, (∀ k, k ≠ i → x k = y k) → B i x = B i y) ∧
      (∀ x, (∏ i, B i x) = finiteIndicator I (x 1 : ZMod N) * ∏ i, A i x) := by
  classical
  let B (i : Fin (d + 3)) (x : Fin (d + 3) → ℤ) :=
    (if i = 0 then finiteIndicator I (x 1 : ZMod N) else 1) * A i x
  refine ⟨B, ?_, ?_, ?_⟩
  · intro i x
    by_cases hi : i = 0
    · simp only [B, hi, ite_true, norm_mul]
      exact (mul_le_mul_of_nonneg_right (finiteIndicator_norm_le_one I _)
        (norm_nonneg _)).trans (by simpa only [one_mul] using hA 0 x)
    · simpa only [B, hi, ite_false, one_mul] using hA i x
  · intro i x y hxy
    by_cases hi : i = 0
    · subst i
      simp only [B, ite_true]
      rw [hAi 0 x y hxy, hxy 1 (by
        intro e
        have he := congrArg Fin.val e
        norm_num only [Fin.val_one, Fin.val_zero] at he)]
    · simpa only [B, hi, ite_false, one_mul] using hAi i x y hxy
  · intro x
    simp only [B, Finset.prod_mul_distrib]
    simp

theorem mixedInterval_zeroExtension_average {d N : ℕ} [NeZero N]
    (a len : ℕ) (hend : a + len ≤ N) (hshort : 2 * ((len : ℤ) - 1) < N)
    (F : (Fin (d + 3) → ℤ) → ℂ) :
    (𝔼 x : Fin (d + 3) → ZMod N,
      finiteIndicator (cyclicInterval (a : ZMod N) len) (x 1) * F (fun k => ((x k).val : ℤ))) =
      (((len : ℝ) / N : ℝ) : ℂ) *
        (𝔼 t : (Fin (d + 1) → ZMod N) × ZMod N,
          𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), F (mixedDifferencePoint t n)) := by
  let I := cyclicInterval (a : ZMod N) len
  have hbase (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ZMod N) :
      mixedProfileEquiv d (ZMod N) (t, n) 1 = n := rfl
  have hrow (t : (Fin (d + 1) → ZMod N) × ZMod N) :
      (𝔼 n : ZMod N, finiteIndicator I (mixedProfileEquiv d (ZMod N) (t, n) 1) *
        F (fun k => ((mixedProfileEquiv d (ZMod N) (t, n) k).val : ℤ))) =
      (((len : ℝ) / N : ℝ) : ℂ) * (𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), F (mixedDifferencePoint t n)) := by
    simpa only [hbase, mixedProfileEquiv_point] using
      cyclicInterval_zeroExtension_average a len hend hshort (fun n => F (mixedDifferencePoint t n))
  rw [mixedProfile_average]
  change (𝔼 t, 𝔼 n : ZMod N, finiteIndicator I (mixedProfileEquiv d (ZMod N) (t, n) 1) *
    F (fun k => ((mixedProfileEquiv d (ZMod N) (t, n) k).val : ℤ))) = _
  simp_rw [hrow]
  rw [← Finset.mul_expect]

theorem HasPositiveMixedTargetInterval.cyclic {J : Type*} {d N : ℕ} [NeZero N] {q : ℝ}
    {f : ZMod N → ℂ} {η : J → (Fin (d + 3) → ℤ) → ℂ}
    (H : HasPositiveMixedTargetInterval f η q) : HasCyclicMixedTargetCorrelation f η (2 * q) := by
  classical
  obtain ⟨j, A, hA, hAi, a, len, _, hend, hshort, hvol, hpositive⟩ := H
  let I := cyclicInterval (a : ZMod N) len
  obtain ⟨B, hB, hBi, hprod⟩ := exists_mixed_interval_cutoff_weights I A hA hAi
  let F (x : Fin (d + 3) → ℤ) := star (f ((∑ k, x k : ℤ) : ZMod N)) * star (η j x) * ∏ i, A i x
  let R (x : Fin (d + 3) → ZMod N) :=
    star (f (∑ k, x k)) * star (η j (fun k => ((x k).val : ℤ))) * ∏ i, B i (fun k => ((x k).val : ℤ))
  have hpoint (x : Fin (d + 3) → ZMod N) :
      R x = finiteIndicator I (x 1) * F (fun k => ((x k).val : ℤ)) := by
    dsimp only [R]
    rw [hprod]
    simp only [F, Int.cast_sum, Int.cast_natCast, ZMod.natCast_zmod_val]
    ring
  have hmean : (𝔼 x, R x).re = (len : ℝ) / N *
      (𝔼 t : (Fin (d + 1) → ZMod N) × ZMod N,
        𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), F (mixedDifferencePoint t n)).re := by
    simp_rw [hpoint]
    rw [mixedInterval_zeroExtension_average a len hend hshort F]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  refine ⟨j, (fun i x => B i (fun k => ((x k).val : ℤ))), (fun i x => hB i _), ?_, ?_⟩
  · intro i x y hxy
    exact hBi i _ _ (fun k hk => congrArg (fun z : ZMod N => (z.val : ℤ)) (hxy k hk))
  · change Real.exp (-(2 * q)) ≤ ‖𝔼 x, R x‖
    apply le_trans ?_ (Complex.re_le_norm _)
    rw [hmean]
    calc
      _ = Real.exp (-q) * Real.exp (-q) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul hvol hpositive (Real.exp_nonneg _) (by positivity)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem HasCyclicMixedTargetCorrelation.mixed_sum {d N : ℕ} [NeZero N] {p q : ℝ}
    {f : ZMod N → ℂ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p)
    (H : HasCyclicMixedTargetCorrelation f
      (fun k x => W.eval k (mixedReplicatedInput (x 0) (fun j => x j.succ))) q) :
    ∃ (i : Fin W.outputDim) (A : Fin (d + 3) → (Fin (d + 3) → ZMod N) → ℂ),
      (∀ j x, ‖A j x‖ ≤ 1) ∧ (∀ j, MissesBoxCoordinate (A j) j) ∧
      Real.exp (-q) ≤ ‖𝔼 u : Fin (d + 1) → ZMod N, 𝔼 m : ZMod N, 𝔼 h : ZMod N,
        star (f (m + h + ∑ j, u j)) *
          star (W.eval i (mixedSlotInput (h.val : ℤ) m.val (fun j => (u j).val))) *
            ∏ j, A j (Fin.cons h (Fin.cons m u))‖ := by
  obtain ⟨i, A, hA, hAi, hc⟩ := H
  refine ⟨i, A, hA, ?_, ?_⟩
  · intro j x v
    apply hAi j
    intro k hkj
    exact Function.update_of_ne hkj v x
  · have hvals (m : ZMod N) (u : Fin (d + 1) → ZMod N) :
        (fun j : Fin (d + 2) => (((Fin.cons m u : Fin (d + 2) → ZMod N) j).val : ℤ)) =
          Fin.cons (m.val : ℤ) (fun j => ((u j).val : ℤ)) := by
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    have hmean :
        (𝔼 x : Fin (d + 3) → ZMod N,
          star (f (∑ k, x k)) * star (W.eval i
            (mixedReplicatedInput ((x 0).val : ℤ) (fun j => ((x j.succ).val : ℤ)))) * ∏ j, A j x) =
        𝔼 u : Fin (d + 1) → ZMod N, 𝔼 m : ZMod N, 𝔼 h : ZMod N,
          star (f (m + h + ∑ j, u j)) *
            star (W.eval i (mixedSlotInput (h.val : ℤ) m.val (fun j => (u j).val))) *
              ∏ j, A j (Fin.cons h (Fin.cons m u)) := by
      rw [expect_mixed_tuple]
      apply Finset.expect_congr rfl
      intro u _
      rw [Finset.expect_comm]
      apply Finset.expect_congr rfl
      intro m _
      apply Finset.expect_congr rfl
      intro h _
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hvals, mixedSlotInput,
        add_left_comm, add_assoc]
    exact hc.trans_eq (congrArg norm hmean)

end Erdos3

end

section

namespace Erdos3

theorem exists_retained_cyclic_sum (d : ℕ) {A : ℕ} (hI : CyclicNativeInverse (d + 2) A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) q,
        W.dim ≤ 2 ^ (d + 3) * M.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence (d + 2) q M.mixed.eval
          (fun k x => W.eval k (fun j => x j.1)) ∧
        tensorPowerBudget (d + 2).factorial q ≤ (p + C) ^ C ∧
        HasCyclicMixedTargetCorrelation f
          (fun k x => (W.tensorPower (d + 2).factorial).eval k
            (mixedReplicatedInput (x 0) (fun j => x j.succ))) ((p + C) ^ C) := by
  obtain ⟨a, _, hretained⟩ := exists_retained_sum_target_intervals d hI
  obtain ⟨b, _, hseparate⟩ := exists_separated_sum_intervals d
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  let R := (P + Polynomial.C b) ^ b
  let T := Polynomial.C ((d + 2).factorial + 1) * (P + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (P + (2 * R + 8) + 4 * (5 * R + 10) + T)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let q := (p + a) ^ a
  let r := (q + b) ^ b
  let t := ((d + 2).factorial + 1 : ℝ) * (q + 1)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htotal : q + (2 * r + 8) + 4 * (5 * r + 10) + t ≤ (p + C) ^ C := by
    simpa [X, P, R, T, q, r, t, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hgridC : 2 * r + 8 ≤ (p + C) ^ C := by linarith
  have hcorrC : 2 * (2 * (5 * r + 10)) ≤ (p + C) ^ C := by linarith
  have htC : t ≤ (p + C) ^ C := by linarith
  obtain ⟨q₀, hq₀, hq₀q, M, W, hdim, hsym, E, H⟩ :=
    hretained hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hG
  have Hsep := hseparate hq hq₀q f hf M W hsym H
  have Hcommon := Hsep.common hr ((Real.exp_le_exp.mpr hgridC).trans hN) hf
    (fun k x => (W.tensorPower (d + 2).factorial).norm_eval k _)
  refine ⟨q₀, hq₀, hq₀q.trans hqC, M, W, hdim, hsym, E, ?_,
    ((Hcommon.positive (by positivity)).cyclic).mono hcorrC⟩
  apply le_trans ?_ htC
  have hqq : q₀ ≤ q := hq₀q
  exact mul_le_mul_of_nonneg_left (by linarith only [hqq] : q₀ + 1 ≤ q + 1) (by positivity)

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_cyclic_target_pair_factors (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p),
      p ≤ q → ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((q + C) ^ C) ≤ (N : ℝ) →
      HasCyclicMixedTargetCorrelation f
        (fun k x => W.eval k (mixedReplicatedInput (x 0) (fun j => x j.succ))) q →
      ∃ u : ℝ, 0 ≤ u ∧ u ≤ (q + C) ^ C ∧
      ∃ (i j : Fin W.outputDim)
        (V : NativeSampleCorrelation (fun _ : Fin (d + 3) => 1) (d + 2) u
          Finset.univ (fun x : Fin (d + 3) → ZMod N => fun k => ((x k).val : ℤ))
          (fun x => W.mixedAntisymmetric i j (fun k => ((x k).val : ℤ)))),
        Nonempty (NativePolynomialOrbitFactors (pi V.mixedPairModels)
          V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
          (fun _ : Fin (d + 3) => (N : ℝ)) ((q + C) ^ C)) := by
  obtain ⟨C, hC, hpair⟩ := exists_mixed_sum_pair_factors (d + 1)
  refine ⟨C, hC, ?_⟩
  intro N _ p q W hpq f hf hN H
  have H' : HasCyclicMixedTargetCorrelation f
      (fun k x => (W.mono hpq).eval k (mixedReplicatedInput (x 0) (fun j => x j.succ))) q := H
  obtain ⟨i, A, hA, hmiss, hc⟩ := HasCyclicMixedTargetCorrelation.mixed_sum (W.mono hpq) H'
  obtain ⟨u, hu, huC, i', j', V, R⟩ := hpair (W.mono hpq) (fun x => star (f x))
    (fun x => by simpa only [norm_star] using hf x) i A hA hmiss hN hc
  exact ⟨u, hu, huC, i', j', V, R⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_retained_mixed_pair_factors (d : ℕ) {A : ℕ}
    (hI : CyclicNativeInverse (d + 2) A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) q,
        W.dim ≤ 2 ^ (d + 3) * M.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence (d + 2) q M.mixed.eval
          (fun k x => W.eval k (fun j => x j.1)) ∧
        tensorPowerBudget (d + 2).factorial q ≤ (p + C) ^ C ∧
        ∃ u : ℝ, 0 ≤ u ∧ u ≤ (p + C) ^ C ∧
        ∃ (i j : Fin (W.tensorPower (d + 2).factorial).outputDim)
          (V : NativeSampleCorrelation (fun _ : Fin (d + 3) => 1) (d + 2) u
            Finset.univ (fun x : Fin (d + 3) → ZMod N => fun k => ((x k).val : ℤ))
            (fun x => (W.tensorPower (d + 2).factorial).mixedAntisymmetric i j (fun k => ((x k).val : ℤ)))),
          ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
            Nonempty (NativePolynomialOrbitFactors (pi V.mixedPairModels)
              V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
              (fun _ : Fin (d + 3) => (N : ℝ)) r) := by
  obtain ⟨a, _, hcyclic⟩ := exists_retained_cyclic_sum d hI
  obtain ⟨b, _, hpair⟩ := exists_cyclic_target_pair_factors d
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  let R := (P + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + R)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let q := (p + a) ^ a
  let r := (q + b) ^ b
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hsum : q + r ≤ (p + C) ^ C := by
    simpa [X, P, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hrC : r ≤ (p + C) ^ C := by linarith
  obtain ⟨q₀, hq₀, hq₀q, M, W, hdim, hsym, E, htensor, H⟩ :=
    hcyclic hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hG
  obtain ⟨u, hu, hur, i, j, V, R⟩ := hpair (W.tensorPower (d + 2).factorial) htensor f hf
    ((Real.exp_le_exp.mpr hrC).trans hN) H
  exact ⟨q₀, hq₀, hq₀q.trans hqC, M, W, hdim, hsym, E, htensor.trans hqC,
    u, hu, hur.trans hrC, i, j, V, r, hr, hrC, R⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_retained_mixed_sampled_exchange (d : ℕ) {A : ℕ}
    (hI : CyclicNativeInverse (d + 2) A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      Real.exp ((p + e + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) q,
        W.dim ≤ 2 ^ (d + 3) * M.mixed.dim ∧
        (∀ (a : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) a).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence (d + 2) q M.mixed.eval
          (fun k x => W.eval k (fun j => x j.1)) ∧
        tensorPowerBudget (d + 2).factorial q ≤ (p + C) ^ C ∧
        ∃ u : ℝ, 0 ≤ u ∧ u ≤ (p + C) ^ C ∧
        ∃ (i j : Fin (W.tensorPower (d + 2).factorial).outputDim)
          (V : NativeSampleCorrelation (fun _ : Fin (d + 3) => 1) (d + 2) u
            Finset.univ (fun x : Fin (d + 3) → ZMod N => fun k => ((x k).val : ℤ))
            (fun x => (W.tensorPower (d + 2).factorial).mixedAntisymmetric i j (fun k => ((x k).val : ℤ)))),
          ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
          ∃ _R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
            V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
            (fun _ : Fin (d + 3) => (N : ℝ)) r,
          ∃ G : (Fin (d + 3) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
            (∀ π a c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (d + 2)
              ((p + e + C) ^ C) (G π a c))) ∧
            (∀ π a c (x : Fin 2 → ZMod N), ‖G π a c (fun k => ((x k).val : ℤ))‖ ≤ 1) ∧
            (∀ π a c, (𝔼 x : Fin 2 → ZMod N,
              ‖W.eval a (mixedSlotInput ((x (π 0)).val : ℤ) ((x (π 1)).val : ℤ)
                  (fun l => ((x (π l.succ.succ)).val : ℤ))) *
                  star (W.eval c (mixedSlotInput ((x (π 1)).val : ℤ) ((x (π 0)).val : ℤ)
                    (fun l => ((x (π l.succ.succ)).val : ℤ)))) -
                G π a c (fun k => ((x k).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨a, _, hpair⟩ := exists_retained_mixed_pair_factors d hI
  obtain ⟨b, _, hexchange⟩ := exists_mixed_precise_sampled_exchange (d + 1)
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  let S := (3 * P + X + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + S)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hG
  classical
  let v := p + e
  let t := (p + a) ^ a
  let tmax := (v + a) ^ a
  have hv : 0 ≤ v := add_nonneg hp he
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htm : 0 ≤ tmax := by dsimp [tmax]; positivity
  have hstep : t ≤ tmax := pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) a
  have hsum : tmax + (3 * tmax + v + b) ^ b ≤ (p + e + C) ^ C := by
    simpa [X, P, S, tmax, v, Polynomial.eval₂_pow] using hbudget v hv
  have htC : t ≤ (p + C) ^ C := by
    have h := hbudget p hp
    have hn : 0 ≤ (3 * t + p + b) ^ b := by positivity
    have hh : t + (3 * t + p + b) ^ b ≤ (p + C) ^ C := by
      simpa [X, P, S, t, Polynomial.eval₂_pow] using h
    linarith
  have htmaxC : tmax ≤ (p + e + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hsC : (3 * tmax + v + b) ^ b ≤ (p + e + C) ^ C :=
    (le_add_of_nonneg_left htm).trans hsum
  obtain ⟨q, hq, hqt, M, W, hdim, hsym, E, htensor, u, hu, hut, i, j, V, r, hr, hrt, ⟨R⟩⟩ :=
    hpair hp ((Real.exp_le_exp.mpr (hstep.trans htmaxC)).trans hN) f hf hG
  let : NeZero (d + 2).factorial := ⟨Nat.ne_of_gt (Nat.factorial_pos _)⟩
  have htnonneg : 0 ≤ tensorPowerBudget (d + 2).factorial q :=
    hq.trans (tensorPowerBudget_bounds (d + 2).factorial hq).1
  have hcost : (tensorPowerBudget (d + 2).factorial q + u + r + e + b) ^ b ≤
      (p + e + C) ^ C := by
    apply le_trans _ hsC
    apply pow_le_pow_left₀ (by positivity)
    dsimp only [v]
    linarith
  obtain ⟨G, hGa, hGb, hGc⟩ := hexchange (W := W) R hr he ((Real.exp_le_exp.mpr hcost).trans hN)
  refine ⟨q, hq, hqt.trans htC, M, W, hdim, hsym, E, htensor.trans htC,
    u, hu, hut.trans htC, i, j, V, r, hr, hrt.trans htC, R, G, ?_, hGb, hGc⟩
  intro π a c
  exact ⟨(Classical.choice (hGa π a c)).mono hcost⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators NNReal

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_retained_mixed_cyclic_comparison (d : ℕ) {A : ℕ}
    (hI : CyclicNativeInverse (d + 2) A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      Real.exp ((p + e + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) q,
        W.dim ≤ 2 ^ (d + 3) * M.mixed.dim ∧
        (∀ (a : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) a).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence (d + 2) q M.mixed.eval
          (fun k x => W.eval k (fun j => x j.1)) ∧
        tensorPowerBudget (d + 2).factorial q ≤ (p + C) ^ C ∧
        ∃ u : ℝ, 0 ≤ u ∧ u ≤ (p + C) ^ C ∧
        ∃ (i j : Fin (W.tensorPower (d + 2).factorial).outputDim)
          (V : NativeSampleCorrelation (fun _ : Fin (d + 3) => 1) (d + 2) u
            Finset.univ (fun x : Fin (d + 3) → ZMod N => fun k => ((x k).val : ℤ))
            (fun x => (W.tensorPower (d + 2).factorial).mixedAntisymmetric i j (fun k => ((x k).val : ℤ)))),
          ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
          ∃ _R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
            V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
            (fun _ : Fin (d + 3) => (N : ℝ)) r,
          ∃ K : (Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) →
              (MixedNonconstantCorner d → Fin W.mixedIntegrationRoot.outputDim) → (Fin 2 → ℤ) → ℂ,
            (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (d + 2)
              ((p + e + C) ^ C) (K a b))) ∧
            (∀ a b, (𝔼 x : Fin 2 → ZMod N,
              ‖W.mixedIntegrationRoot.mixedCyclicDiagonalDerivative a x *
                  star (W.mixedIntegrationRoot.mixedCanonicalTensor b (fun k => ((x k).val : ℤ))) -
                K a b (fun k => ((x k).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨a, _, hmodel⟩ := exists_retained_mixed_sampled_exchange d hI
  obtain ⟨b, _, hroot⟩ := NativeMultidegreeNilcharacter.exists_mixedRootCyclicCorrection_expansion d
  let L := mixedCyclicErrorSlope d
  let J := mixedCyclicErrorBuffer d
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C a) ^ a
  let T := (X + Polynomial.C L * U + Polynomial.C J + Polynomial.C a) ^ a
  let S := (U + T + X + Polynomial.C J + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + T + X + Polynomial.C J + S)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hGowers
  let v := p + e
  let u := (p + a) ^ a
  let umax := (v + a) ^ a
  let accuracy := e + (L : ℝ) * u + J
  let t := (p + accuracy + a) ^ a
  let tmax := (v + (L : ℝ) * umax + J + a) ^ a
  let errorScale := e + J
  let smax := (umax + tmax + v + J + b) ^ b
  let δ : ℝ≥0 := ⟨Real.exp (-errorScale), (Real.exp_pos _).le⟩
  have hδval : (δ : ℝ) = Real.exp (-errorScale) := rfl
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have humax : 0 ≤ umax := by dsimp [umax]; positivity
  have ht : 0 ≤ t := by dsimp [t, accuracy]; positivity
  have htmax : 0 ≤ tmax := by dsimp [tmax]; positivity
  have hsmax : 0 ≤ smax := by dsimp [smax]; positivity
  have hb : 0 ≤ errorScale := by dsimp [errorScale]; positivity
  have hδ : 0 < δ := Real.exp_pos _
  have hinv : (δ : ℝ)⁻¹ ≤ Real.exp errorScale := by rw [hδval, ← Real.exp_neg, neg_neg]
  have hsum : umax + tmax + v + J + smax ≤ (p + e + C) ^ C := by
    simpa [X, U, T, S, umax, tmax, smax, v, Polynomial.eval₂_pow] using hbudget v hv
  have hum : u ≤ umax := pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) a
  have htm : t ≤ tmax := by
    apply pow_le_pow_left₀ (by dsimp [accuracy]; positivity)
    have hL := mul_le_mul_of_nonneg_left hum (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    dsimp [accuracy, v]
    linarith
  have htC : tmax ≤ (p + e + C) ^ C := by linarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
  have hsC : smax ≤ (p + e + C) ^ C := by linarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
  have hbC : errorScale ≤ (p + e + C) ^ C := by dsimp [errorScale, v] at *; linarith
  have huC : u ≤ (p + C) ^ C := by
    have hh : u + (p + (L : ℝ) * u + J + a) ^ a + p + J +
        (u + (p + (L : ℝ) * u + J + a) ^ a + p + J + b) ^ b ≤ (p + C) ^ C := by
      simpa [X, U, T, S, u, Polynomial.eval₂_pow] using hbudget p hp
    have h1 : 0 ≤ (p + (L : ℝ) * u + J + a) ^ a := by positivity
    have h2 : 0 ≤ (u + (p + (L : ℝ) * u + J + a) ^ a + p + J + b) ^ b := by positivity
    linarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
  obtain ⟨q, hq, hqu, M, W, hdim, hsymm, E, htensor, u₀, hu₀, hu₀u, i, j, V, r, hr, hru,
      R, G, hG, hcap, herr⟩ :=
    hmodel hp (by dsimp [accuracy]; positivity : 0 ≤ accuracy)
      ((Real.exp_le_exp.mpr (htm.trans htC)).trans hN) f hf hGowers
  have hqmax : q ≤ umax := hqu.trans hum
  have hcost : (q + t + errorScale + b) ^ b ≤ (p + e + C) ^ C := by
    apply le_trans _ hsC
    apply pow_le_pow_left₀ (by positivity)
    dsimp [errorScale, v]
    linarith
  have herror := mixed_cyclic_error_bound d (Nat.cast_nonneg W.outputDim) hu
    (W.output_bound.trans (Real.exp_le_exp.mpr hqu)) ((Real.exp_le_exp.mpr hbC).trans hN)
  have hexchange : ∀ π a c, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval a (mixedSampledInput π (fun k => ((x k).val : ℤ))) *
          star (W.eval c (mixedSampledInput (mixedSwapSample π) (fun k => ((x k).val : ℤ)))) -
        G π a c (fun k => ((x k).val : ℤ))‖) ≤ Real.exp (-accuracy) := by
    intro π a c
    simp only [mixedSwapSample_input]
    simpa only [mixedSampledInput_slots] using herr π a c
  refine ⟨q, hq, hqu.trans huC, M, W, hdim, hsymm, E, htensor.trans huC,
    u₀, hu₀, hu₀u.trans huC, i, j, V, r, hr, hru.trans huC, R,
    W.mixedRootCyclicCorrection N δ G, ?_, ?_⟩
  · intro a c
    exact ⟨(Classical.choice (hroot W N δ hδ ht hb hinv hsymm G hG a c)).mono hcost⟩
  · intro a c
    apply (W.mixedRootCyclicCorrection_mean_error δ hδ G (Real.exp_nonneg _) hcap hexchange a c).trans
    simpa only [W.mixedIntegrationRoot_outputDim, Nat.cast_pow, hδval, errorScale, accuracy, L, J] using herror

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_retained_mixed_original_integration (d : ℕ) {A : ℕ}
    (hI : CyclicNativeInverse (d + 2) A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      Real.exp ((p + e + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) q,
        W.dim ≤ 2 ^ (d + 3) * M.mixed.dim ∧
        (∀ (a : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) a).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence (d + 2) q M.mixed.eval
          (fun k x => W.eval k (fun j => x j.1)) ∧
        tensorPowerBudget (d + 2).factorial q ≤ (p + C) ^ C ∧
        ∃ u : ℝ, 0 ≤ u ∧ u ≤ (p + C) ^ C ∧
        ∃ (i j : Fin (W.tensorPower (d + 2).factorial).outputDim)
          (V : NativeSampleCorrelation (fun _ : Fin (d + 3) => 1) (d + 2) u
            Finset.univ (fun x : Fin (d + 3) → ZMod N => fun k => ((x k).val : ℤ))
            (fun x => (W.tensorPower (d + 2).factorial).mixedAntisymmetric i j (fun k => ((x k).val : ℤ)))),
          ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
          ∃ _R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
            V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
            (fun _ : Fin (d + 3) => (N : ℝ)) r,
          ∃ K : (Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) →
              Fin M.mixed.outputDim → (MixedMiddleCorner d → Fin W.mixedIntegrationRoot.outputDim) →
              Fin W.mixedIntegrationRoot.outputDim → (Fin 2 → ℤ) → ℂ,
            (∀ a i b c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (d + 2)
              ((p + e + C) ^ C) (K a i b c))) ∧
            (∀ a i b c, (𝔼 x : Fin 2 → ZMod N,
              ‖W.mixedIntegrationRoot.mixedCyclicDiagonalDerivative a x *
                  (M.mixed.eval i (fun k => ((x k).val : ℤ)) *
                    (W.mixedIntegrationRoot.mixedMiddleTensor b (fun k => ((x k).val : ℤ)) *
                      W.mixedIntegrationRoot.eval c (fun _ => ((x 0).val : ℤ)))) -
                K a i b c (fun k => ((x k).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨a, _, hmodel⟩ := exists_retained_mixed_cyclic_comparison d hI
  obtain ⟨b, _, hexpansion⟩ := NativeMultidegreeNilcharacter.exists_mixedOriginalWeightCorrection_expansion d
  let L := mixedRootTensorExponent d * (d + 3)
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C a) ^ a
  let T := (X + Polynomial.C L * U + Polynomial.C a) ^ a
  let S := (U + T + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + T + S)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hGowers
  let v := p + e
  let u := (p + a) ^ a
  let umax := (v + a) ^ a
  let accuracy := e + (L : ℝ) * u
  let t := (p + accuracy + a) ^ a
  let tmax := (v + (L : ℝ) * umax + a) ^ a
  let smax := (umax + tmax + b) ^ b
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have humax : 0 ≤ umax := by dsimp [umax]; positivity
  have ht : 0 ≤ t := by dsimp [t, accuracy]; positivity
  have htmax : 0 ≤ tmax := by dsimp [tmax]; positivity
  have hsmax : 0 ≤ smax := by dsimp [smax]; positivity
  have hsum : umax + tmax + smax ≤ (p + e + C) ^ C := by
    simpa [X, U, T, S, umax, tmax, smax, v, Polynomial.eval₂_pow] using hbudget v hv
  have hum : u ≤ umax := pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) a
  have htm : t ≤ tmax := by
    apply pow_le_pow_left₀ (by dsimp [accuracy]; positivity)
    have hL := mul_le_mul_of_nonneg_left hum (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    dsimp [accuracy, v]
    linarith
  have htC : tmax ≤ (p + e + C) ^ C := by linarith
  have hsC : smax ≤ (p + e + C) ^ C := by linarith
  have huC : u ≤ (p + C) ^ C := by
    have hh : u + (p + (L : ℝ) * u + a) ^ a +
        (u + (p + (L : ℝ) * u + a) ^ a + b) ^ b ≤ (p + C) ^ C := by
      simpa [X, U, T, S, u, Polynomial.eval₂_pow] using hbudget p hp
    have h1 : 0 ≤ (p + (L : ℝ) * u + a) ^ a := by positivity
    have h2 : 0 ≤ (u + (p + (L : ℝ) * u + a) ^ a + b) ^ b := by positivity
    linarith
  obtain ⟨q, hq, hqu, M, W, hdim, hsymm, E, htensor, u₀, hu₀, hu₀u, i, j, V, r, hr, hru,
      R, K, hK, herr⟩ :=
    hmodel hp (by dsimp [accuracy]; positivity : 0 ≤ accuracy)
      ((Real.exp_le_exp.mpr (htm.trans htC)).trans hN) f hf hGowers
  have hqmax : q ≤ umax := hqu.trans hum
  have hcost : (q + t + b) ^ b ≤ (p + e + C) ^ C := by
    apply le_trans _ hsC
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hd : (W.outputDim : ℝ) ≤ Real.exp u :=
    W.output_bound.trans (Real.exp_le_exp.mpr hqu)
  have hpow : (W.outputDim : ℝ) ^ L ≤ Real.exp ((L : ℝ) * u) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hd L).trans_eq (Real.exp_nat_mul u L).symm
  have hrootDim : (W.mixedIntegrationRoot.outputDim : ℝ) ^ (d + 3) ≤ Real.exp ((L : ℝ) * u) := by
    simpa only [W.mixedIntegrationRoot_outputDim, Nat.cast_pow, ← pow_mul, L] using hpow
  have herror : (W.mixedIntegrationRoot.outputDim : ℝ) ^ (d + 3) * Real.exp (-accuracy) ≤ Real.exp (-e) := by
    calc
      _ ≤ Real.exp ((L : ℝ) * u) * Real.exp (-accuracy) :=
        mul_le_mul_of_nonneg_right hrootDim (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [accuracy]; ring
  refine ⟨q, hq, hqu.trans huC, M, W, hdim, hsymm, E, htensor.trans huC,
    u₀, hu₀, hu₀u.trans huC, i, j, V, r, hr, hru.trans huC, R,
    (fun a i b c => M.mixed.mixedOriginalWeightCorrection W K a i (mixedSplitHigherMerge b c)), ?_, ?_⟩
  · intro a i b c
    exact ⟨(Classical.choice (hexpansion M.mixed W ht E K hK a i (mixedSplitHigherMerge b c))).mono hcost⟩
  · intro a i b c
    have H := M.mixed.mixedOriginalWeightCorrection_mean_error W K
      (fun a (x : Fin 2 → ZMod N) => W.mixedIntegrationRoot.mixedCyclicDiagonalDerivative a x)
      herr a i (mixedSplitHigherMerge b c)
    simpa only [NativeMultidegreeNilcharacter.mixedHigherTensor_split] using H.trans herror

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def mixedRowCoordinateCount (s : ℕ) : ℕ := Fintype.card (MixedMiddleCorner s) + 3

theorem mixedRowIndex_card (s D : ℕ) :
    (Fintype.card (((Fin D × Fin D) × (MixedMiddleCorner s → Fin D)) × Fin D) : ℝ) =
      (D : ℝ) ^ mixedRowCoordinateCount s := by
  simp only [mixedRowCoordinateCount, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_pow, pow_add]
  ring

namespace NativeMultidegreeNilcharacter

open scoped BigOperators

theorem mixed_original_row_correlation_bound {s : ℕ} {p ε : ℝ} {N : ℕ} [NeZero N]
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (s + 2)) p)
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)
    (i : Fin M.outputDim) (row : ZMod N → ZMod N → ℂ)
    (hrow : ∀ h n, ‖row h n‖ ≤ 1)
    (K : (Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) →
      (MixedMiddleCorner s → Fin W.mixedIntegrationRoot.outputDim) → Fin W.mixedIntegrationRoot.outputDim → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b c, (𝔼 x : Fin 2 → ZMod N,
      ‖W.mixedIntegrationRoot.mixedCyclicDiagonalDerivative a x *
          (M.eval i (fun k => ((x k).val : ℤ)) *
            (W.mixedIntegrationRoot.mixedMiddleTensor b (fun k => ((x k).val : ℤ)) *
              W.mixedIntegrationRoot.eval c (fun _ => ((x 0).val : ℤ)))) -
        K a b c (fun k => ((x k).val : ℤ))‖) ≤ ε) :
    (𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
      row h n * star (M.evalCyclic N i (correlationInput h n))‖) ≤
      (∑ abc : ((Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) ×
          (MixedMiddleCorner s → Fin W.mixedIntegrationRoot.outputDim)) × Fin W.mixedIntegrationRoot.outputDim,
        𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
          row h n *
            (W.mixedIntegrationRoot.mixedCyclicDiagonalDerivative abc.1.1 ![h, n] *
              W.mixedIntegrationRoot.mixedMiddleTensor abc.1.2 ![(h.val : ℤ), (n.val : ℤ)]) *
                star (K abc.1.1 abc.1.2 abc.2 ![(h.val : ℤ), (n.val : ℤ)])‖) +
          (W.mixedIntegrationRoot.outputDim : ℝ) ^ mixedRowCoordinateCount s * ε := by
  let R := W.mixedIntegrationRoot
  let I := (Fin R.outputDim × Fin R.outputDim) × (MixedMiddleCorner s → Fin R.outputDim)
  have hinput (h n : ZMod N) : (fun k => ((![h, n] k).val : ℤ)) = ![(h.val : ℤ), (n.val : ℤ)] := by
    funext k
    fin_cases k <;> rfl
  have heval (h n : ZMod N) : M.evalCyclic N i (correlationInput h n) =
      M.eval i ![(h.val : ℤ), (n.val : ℤ)] := by
    unfold evalCyclic
    congr 1
    funext k
    fin_cases k <;> rfl
  have hunit (h n : ZMod N) : ∑ ab : I,
      ‖R.mixedCyclicDiagonalDerivative ab.1 ![h, n] *
        R.mixedMiddleTensor ab.2 ![(h.val : ℤ), (n.val : ℤ)]‖ ^ 2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [norm_mul, mul_pow, ← Finset.mul_sum, R.mixedMiddleTensor_unit, mul_one]
    exact R.mixedCyclicDiagonalDerivative_unit _
  have hh := unit_row_correlation_bound row
    (fun h n => M.eval i ![(h.val : ℤ), (n.val : ℤ)])
    (fun ab : I => fun h n => R.mixedCyclicDiagonalDerivative ab.1 ![h, n] *
      R.mixedMiddleTensor ab.2 ![(h.val : ℤ), (n.val : ℤ)])
    (fun c h => R.eval c (fun _ => (h.val : ℤ)))
    (fun ab c h n => K ab.1 ab.2 c ![(h.val : ℤ), (n.val : ℤ)]) hrow hunit
    (fun h => R.unit_eval _) (fun ab h n => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (R.mixedCyclicDiagonalDerivative_norm _ _)
        (norm_nonneg _)).trans (by
          simpa only [one_mul] using R.mixedMiddleTensor_norm _ _))
      (fun c h => R.norm_eval _ _) (ε := ε) (by
      intro ab c
      have he := herr ab.1 ab.2 c
      rw [expect_fin_two] at he
      simpa only [hinput, Matrix.cons_val_zero, mul_assoc, mul_comm, mul_left_comm] using he)
  have hcard : (Fintype.card (I × Fin R.outputDim) : ℝ) =
      (R.outputDim : ℝ) ^ mixedRowCoordinateCount s := mixedRowIndex_card s R.outputDim
  simpa only [heval, hcard] using hh

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {d : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p)

noncomputable def mixedPrimitiveFactor {N : ℕ} [NeZero N] (f : ZMod N → ℂ)
    (i : Fin W.outputDim) (n : ZMod N) : ℂ :=
  f n * W.eval i (fun _ => (n.val : ℤ))

theorem mixedPrimitiveFactor_norm {N : ℕ} [NeZero N] (f : ZMod N → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (i : Fin W.outputDim) (n : ZMod N) :
    ‖W.mixedPrimitiveFactor f i n‖ ≤ 1 := by
  rw [mixedPrimitiveFactor, norm_mul]
  exact (mul_le_mul_of_nonneg_right (hf n) (norm_nonneg _)).trans (by
    simpa only [one_mul] using W.norm_eval _ _)

theorem mixedPrimitiveFactor_cross {N : ℕ} [NeZero N] (f : ZMod N → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim) (h n : ZMod N) :
    multiplicativeDerivative f h n * W.mixedCyclicDiagonalDerivative a ![h, n] =
      W.mixedPrimitiveFactor f a.1 n * star (W.mixedPrimitiveFactor f a.2 (n + h)) := by
  simp only [multiplicativeDerivative, mixedCyclicDiagonalDerivative, mixedPrimitiveFactor,
    Matrix.cons_val_zero, Matrix.cons_val_one, star_mul]
  rw [add_comm h n]
  ring

end NativeMultidegreeNilcharacter

namespace NativeMixedCorrelation

variable {d : ℕ} {m p : ℝ} {N : ℕ} [NeZero N] {f : ZMod N → ℂ}
  (M : NativeMixedCorrelation (d + 2) N m f)
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p)

noncomputable def mixedPrimitiveRow (a : Fin W.outputDim × Fin W.outputDim)
    (b : (MixedMiddleCorner d → Fin W.outputDim)) (h n : ZMod N) : ℂ :=
  (W.mixedPrimitiveFactor f a.1 n * star (W.mixedPrimitiveFactor f a.2 (n + h))) *
    W.mixedMiddleTensor b ![(h.val : ℤ), (n.val : ℤ)] *
      star (M.residualMultiplier h (fun _ => (n.val : ℤ)))

theorem mixedPrimitiveRow_eq (a : Fin W.outputDim × Fin W.outputDim)
    (b : (MixedMiddleCorner d → Fin W.outputDim)) (h n : ZMod N) :
    M.mixedPrimitiveRow W a b h n = M.normalizedResidualRow h n *
      (W.mixedCyclicDiagonalDerivative a ![h, n] *
        W.mixedMiddleTensor b ![(h.val : ℤ), (n.val : ℤ)]) := by
  rw [mixedPrimitiveRow, M.normalizedResidualRow_factor, ← W.mixedPrimitiveFactor_cross f a h n]
  ring

end NativeMixedCorrelation

theorem exists_mixed_primitive_rows (d : ℕ) {I : ℕ} (hI : CyclicNativeInverse (d + 2) I) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) q,
      ∃ a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim,
      ∃ b : (MixedMiddleCorner d → Fin W.mixedIntegrationRoot.outputDim),
        Nonempty (NativeMeanRowCorrelation (fun _ : Fin 2 => 1) (d + 2) ((p + C) ^ C)
          (fun h n : ZMod N => ![(h.val : ℤ), (n.val : ℤ)])
          (M.mixedPrimitiveRow W.mixedIntegrationRoot a b)) := by
  obtain ⟨A, _, hintegrate⟩ := exists_retained_mixed_original_integration d hI
  let L := mixedRowCoordinateCount d
  let B0 := mixedRootTensorExponent d + 1
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let R := Polynomial.C B0 * (U + 1)
  let E := 4 * U + Polynomial.C L * R + 4
  let T := (X + E + Polynomial.C A) ^ A
  let V := 4 * U + 2 + Polynomial.C L * R + T
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + R + E + T + V)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let u := (p + A) ^ A
  let r := (B0 : ℝ) * (u + 1)
  let e := 4 * u + (L : ℝ) * r + 4
  let t := (p + e + A) ^ A
  let v := 4 * u + 2 + (L : ℝ) * r + t
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hsum : u + r + e + t + v ≤ (p + C) ^ C := by
    simpa [X, U, R, E, T, V, u, r, e, t, v, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := by linarith
  have huC : u ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  obtain ⟨q, hq, hqu, M, W, hdim, hsymm, E, htensor, u0, hu0, hu0u,
    i, j, Vpair, rpair, hrpair, hrbound, R, K, hK, herr⟩ :=
    hintegrate hp he ((Real.exp_le_exp.mpr htC).trans hN) f hf hGowers
  obtain ⟨out, H, hHM, hH, hdense, hcorr⟩ := M.exists_fixed_normalized_residual_coordinate
  let B := W.mixedIntegrationRoot
  have hroot : tensorPowerBudget (mixedRootTensorExponent d) q ≤ r := by
    dsimp [tensorPowerBudget, r, B0]
    push_cast
    exact mul_le_mul_of_nonneg_left (show q + 1 ≤ u + 1 by dsimp [u]; linarith) (by positivity)
  have hD : (B.outputDim : ℝ) ≤ Real.exp r :=
    B.output_bound.trans (Real.exp_le_exp.mpr hroot)
  have hDL : (B.outputDim : ℝ) ^ L ≤ Real.exp ((L : ℝ) * r) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hD L).trans_eq (Real.exp_nat_mul r L).symm
  let J := ((Fin B.outputDim × Fin B.outputDim) × (MixedMiddleCorner d → Fin B.outputDim)) × Fin B.outputDim
  let z (abc : J) := 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
    M.normalizedResidualRow h n *
      (B.mixedCyclicDiagonalDerivative abc.1.1 ![h, n] *
        B.mixedMiddleTensor abc.1.2 ![(h.val : ℤ), (n.val : ℤ)]) *
          star (K abc.1.1 out abc.1.2 abc.2 ![(h.val : ℤ), (n.val : ℤ)])‖
  have hcard : (Fintype.card J : ℝ) ≤ Real.exp ((L : ℝ) * r) := by
    have hc : (Fintype.card J : ℝ) = (B.outputDim : ℝ) ^ L := mixedRowIndex_card d B.outputDim
    rw [hc]
    exact hDL
  have hmass : Real.exp (-(4 * u)) ≤ 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
      M.normalizedResidualRow h n * star (M.mixed.evalCyclic N out (correlationInput h n))‖ := by
    have hh := dense_set_mean_lower_bound H _ (fun _ => norm_nonneg _)
      (Real.exp_nonneg (-(2 * q))) (by simpa only [ZMod.card] using hdense) hcorr
    have heq : Real.exp (-(2 * q)) * Real.exp (-(2 * q)) = Real.exp (-(4 * q)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [heq] at hh
    exact (Real.exp_le_exp.mpr (by linarith)).trans hh
  have htransfer := M.mixed.mixed_original_row_correlation_bound W out
    M.normalizedResidualRow (M.normalizedResidualRow_norm hf)
    (fun a b c => K a out b c) (fun a b c => herr a out b c)
  change _ ≤ (∑ abc : J, z abc) + (B.outputDim : ℝ) ^ L * Real.exp (-e) at htransfer
  let δ := Real.exp (-(4 * u + 2))
  have hδ : 0 < δ := Real.exp_pos _
  have herror : (B.outputDim : ℝ) ^ L * Real.exp (-e) ≤ δ := by
    calc
      _ ≤ Real.exp ((L : ℝ) * r) * Real.exp (-e) :=
        mul_le_mul_of_nonneg_right hDL (Real.exp_nonneg _)
      _ = Real.exp (-(4 * u + 4)) := by rw [← Real.exp_add]; congr 1; dsimp [e]; ring
      _ ≤ δ := Real.exp_le_exp.mpr (by linarith)
  have htwo : 2 * δ ≤ Real.exp (-(4 * u)) := by
    calc
      _ ≤ Real.exp 2 * δ := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) hδ.le
      _ = _ := by dsimp [δ]; rw [← Real.exp_add]; congr 1; ring
  have hmass' : δ ≤ ∑ abc : J, z abc := by linarith
  obtain ⟨abc, habc⟩ := exists_large_nonnegative_weighted_term (fun _ : J => (1 : ℝ)) z
    (fun _ => by norm_num) (fun _ => Finset.expect_nonneg (fun _ _ => norm_nonneg _))
    hδ (Real.exp_pos _) (by simpa using hcard) (by simpa only [one_mul] using hmass')
  have habc' : Real.exp (-(4 * u + 2 + (L : ℝ) * r)) ≤ z abc := by
    have heq : δ / Real.exp ((L : ℝ) * r) = Real.exp (-(4 * u + 2 + (L : ℝ) * r)) := by
      dsimp [δ]; rw [← Real.exp_sub]; congr 1; ring
    rwa [heq] at habc
  let expansion := Classical.choice (hK abc.1.1 out abc.1.2 abc.2)
  obtain ⟨P⟩ := NativeMeanRowCorrelation.exists_of_expansion expansion
    (by positivity : 0 ≤ 4 * u + 2 + (L : ℝ) * r) habc'
  have heq : (fun h n : ZMod N => M.normalizedResidualRow h n *
      (B.mixedCyclicDiagonalDerivative abc.1.1 ![h, n] *
        B.mixedMiddleTensor abc.1.2 ![(h.val : ℤ), (n.val : ℤ)])) =
      M.mixedPrimitiveRow B abc.1.1 abc.1.2 := by
    funext h n
    exact (M.mixedPrimitiveRow_eq B abc.1.1 abc.1.2 h n).symm
  refine ⟨q, hq, hqu.trans huC, M, W, abc.1.1, abc.1.2, ?_⟩
  exact ⟨heq ▸ P.mono hvC⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMixedCorrelation

variable {d : ℕ} {m p : ℝ} {N : ℕ} [NeZero N] {f : ZMod N → ℂ}
  (M : NativeMixedCorrelation (d + 2) N m f)
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p)

noncomputable def mixedResidualRowFactor (b : (MixedMiddleCorner d → Fin W.outputDim))
    (h : ZMod N) (x : Unit → ℤ) : ℂ :=
  M.residualMultiplier h x * star (W.mixedMiddleTensor b ![(h.val : ℤ), x ()])

theorem mixedResidualRowFactor_norm (b : (MixedMiddleCorner d → Fin W.outputDim))
    (h : ZMod N) (x : Unit → ℤ) : ‖M.mixedResidualRowFactor W b h x‖ ≤ 1 := by
  rw [mixedResidualRowFactor, norm_mul, norm_star]
  exact (mul_le_mul_of_nonneg_right (M.residualMultiplier_norm h x)
    (norm_nonneg _)).trans (by
      simpa only [one_mul] using W.mixedMiddleTensor_norm _ _)

theorem mixedPrimitiveRow_cross_residual (a : Fin W.outputDim × Fin W.outputDim)
    (b : (MixedMiddleCorner d → Fin W.outputDim)) (h n : ZMod N) :
    M.mixedPrimitiveRow W a b h n =
      (W.mixedPrimitiveFactor f a.1 n * star (W.mixedPrimitiveFactor f a.2 (n + h))) *
        star (M.mixedResidualRowFactor W b h (fun _ => (n.val : ℤ))) := by
  simp only [mixedPrimitiveRow, mixedResidualRowFactor, star_mul, star_star]
  ring

theorem exists_mixedResidualRowFactor_expansion (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {m p : ℝ} {N : ℕ} [NeZero N] {f : ZMod N → ℂ}
      (M : NativeMixedCorrelation (d + 2) N m f)
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p)
      (b : (MixedMiddleCorner d → Fin W.outputDim)) (h : ZMod N),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (d + 1) ((m + p + C) ^ C)
        (M.mixedResidualRowFactor W b h)) := by
  obtain ⟨A, _, hmiddle⟩ := NativeMultidegreeNilcharacter.exists_mixedMiddleTensor_row_expansion d
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro m p N _ f M W b h
  have hm : 0 ≤ m := (Nat.cast_nonneg M.mixed.dim).trans M.mixed.complexity.1.1
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let t := m + p + (m + p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hmt : m ≤ t := by
    have hpow : 0 ≤ (m + p + A) ^ A := by positivity
    dsimp [t]
    linarith
  have hAt : (p + A) ^ A ≤ t := by
    apply (pow_le_pow_left₀ (by positivity) (show p + A ≤ m + p + A by linarith) A).trans
    exact le_add_of_nonneg_left (add_nonneg hm hp)
  obtain ⟨F⟩ := hmul ht ((Classical.choice (M.residualMultiplier_expansion h)).mono hmt)
    ((Classical.choice (hmiddle W h.val b)).conjugate.mono hAt)
  have hcost : (t + B) ^ B ≤ (m + p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget (m + p) (add_nonneg hm hp)
  exact ⟨F.mono hcost⟩

end NativeMixedCorrelation

theorem exists_mixed_residual_cross_rows (d : ℕ) {I : ℕ} (hI : CyclicNativeInverse (d + 2) I) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) q,
      ∃ a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim,
      ∃ b : (MixedMiddleCorner d → Fin W.mixedIntegrationRoot.outputDim),
        Nonempty (NativeMeanRowCorrelation (fun _ : Fin 2 => 1) (d + 2) ((p + C) ^ C)
          (fun h n : ZMod N => ![(h.val : ℤ), (n.val : ℤ)])
          (fun h n =>
            (W.mixedIntegrationRoot.mixedPrimitiveFactor f a.1 n *
              star (W.mixedIntegrationRoot.mixedPrimitiveFactor f a.2 (n + h))) *
                star (M.mixedResidualRowFactor W.mixedIntegrationRoot b h (fun _ => (n.val : ℤ))))) ∧
        (∀ h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (d + 1) ((p + C) ^ C)
          (M.mixedResidualRowFactor W.mixedIntegrationRoot b h))) ∧
        (∀ h x, ‖M.mixedResidualRowFactor W.mixedIntegrationRoot b h x‖ ≤ 1) := by
  obtain ⟨A, _, hrows⟩ := exists_mixed_primitive_rows d hI
  obtain ⟨B, _, hfactor⟩ := NativeMixedCorrelation.exists_mixedResidualRowFactor_expansion d
  let n := mixedRootTensorExponent d
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + (Polynomial.C (n + 2) * (U + 1) + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let u := (p + A) ^ A
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hsum : u + (((n : ℝ) + 2) * (u + 1) + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, U, u, Polynomial.eval₂_pow] using hbudget p hp
  have huC : u ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  obtain ⟨q, hq, hqu, M, W, a, b, ⟨V⟩⟩ :=
    hrows hp ((Real.exp_le_exp.mpr huC).trans hN) f hf hGowers
  have hcost : (q + tensorPowerBudget (mixedRootTensorExponent d) q + B) ^ B ≤ (p + C) ^ C := by
    apply le_trans _ ((le_add_of_nonneg_left hu).trans hsum)
    apply pow_le_pow_left₀ (by unfold tensorPowerBudget; positivity)
    simp only [tensorPowerBudget]
    have hm := mul_le_mul_of_nonneg_left (show q + 1 ≤ u + 1 by dsimp [u]; linarith)
      (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)
    change q + ((n : ℝ) + 1) * (q + 1) + B ≤ ((n : ℝ) + 2) * (u + 1) + B
    nlinarith
  have heq : M.mixedPrimitiveRow W.mixedIntegrationRoot a b =
      (fun h n =>
        (W.mixedIntegrationRoot.mixedPrimitiveFactor f a.1 n *
          star (W.mixedIntegrationRoot.mixedPrimitiveFactor f a.2 (n + h))) *
            star (M.mixedResidualRowFactor W.mixedIntegrationRoot b h (fun _ => (n.val : ℤ)))) := by
    funext h n
    exact M.mixedPrimitiveRow_cross_residual W.mixedIntegrationRoot a b h n
  refine ⟨q, hq, hqu.trans huC, M, W, a, b, ⟨heq ▸ V.mono huC⟩, ?_, ?_⟩
  · intro h
    exact ⟨(Classical.choice (hfactor M W.mixedIntegrationRoot b h)).mono hcost⟩
  · intro h x
    exact M.mixedResidualRowFactor_norm W.mixedIntegrationRoot b h x

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeMeanRowCorrelation.lie NativeMeanRowCorrelation.algebra NativeMeanRowCorrelation.topology NativeMeanRowCorrelation.topologicalAdd NativeMeanRowCorrelation.continuousSMul NativeMeanRowCorrelation.hausdorff

theorem exists_mixed_primitive_gowers (d : ℕ) {I : ℕ} (hI : CyclicNativeInverse (d + 2) I) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
        ∃ W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) q,
        ∃ i : Fin W.outputDim,
          Real.exp (-((p + C) ^ C)) ≤ gowersNorm (d + 3) (W.mixedPrimitiveFactor f i) := by
  obtain ⟨A, _, hrows⟩ := exists_mixed_residual_cross_rows d hI
  obtain ⟨B, _, hcross⟩ := RationalFilteredNilmanifold.exists_gowers_of_residual_cross_rows (d + 2) (by omega)
  let n := mixedRootTensorExponent d
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + Polynomial.C (n + 1) * (U + 1) + (U + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let u := (p + A) ^ A
  let v := (u + B) ^ B
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have htotal : u + ((n : ℝ) + 1) * (u + 1) + v ≤ (p + C) ^ C := by
    simpa [X, U, u, v, Polynomial.eval₂_pow] using hbudget p hp
  have hr : 0 ≤ ((n : ℝ) + 1) * (u + 1) := by positivity
  have huC : u ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  obtain ⟨q, hq, hqu, M, W, a, b, ⟨V⟩, hR, hRnorm⟩ :=
    hrows hp ((Real.exp_le_exp.mpr huC).trans hN) f hf hGowers
  have hc := hcross V.model V.test hu V.complexity
    ((Real.exp_le_exp.mpr hvC).trans hN)
    (W.mixedIntegrationRoot.mixedPrimitiveFactor f a.1) (W.mixedIntegrationRoot.mixedPrimitiveFactor f a.2)
    (M.mixedResidualRowFactor W.mixedIntegrationRoot b)
    (W.mixedIntegrationRoot.mixedPrimitiveFactor_norm f hf a.1)
    (W.mixedIntegrationRoot.mixedPrimitiveFactor_norm f hf a.2)
    (fun h n => hRnorm h (fun _ => (n.val : ℤ))) hR V.correlation
  have hroot : 0 ≤ tensorPowerBudget (mixedRootTensorExponent d) q := by unfold tensorPowerBudget; positivity
  have hrootC : tensorPowerBudget (mixedRootTensorExponent d) q ≤ (p + C) ^ C := by
    have hm := mul_le_mul_of_nonneg_left (show q + 1 ≤ u + 1 by dsimp [u]; linarith)
      (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)
    change ((n : ℝ) + 1) * (q + 1) ≤ (p + C) ^ C
    linarith
  exact ⟨tensorPowerBudget (mixedRootTensorExponent d) q, hroot, hrootC, W.mixedIntegrationRoot, a.2,
    (Real.exp_le_exp.mpr (neg_le_neg hvC)).trans hc⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AxisCompression
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def normalizedAxisProduct {G : Type*} [Add G] {n : ℕ}
    (f : Fin n → G → ℝ) (t : Fin n → G) (c : ℝ) (y : G) : ℝ := axisProduct f t y / c ^ n

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_native_cyclic_small_modulus_correlation (s : ℕ) (hs : 1 ≤ s)
    {N : ℕ} [NeZero N] {p q : ℝ}
    (hN : (N : ℝ) ≤ Real.exp q) (f : ZMod N → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hGowers : Real.exp (-p) ≤ gowersNorm (s + 1) f) :
    ∃ g ∈ nativeCyclicFunctions s N 211,
      Real.exp (-(((2 ^ (s + 1) : ℕ) : ℝ) * p + q)) ≤ ‖𝔼 n, f n * star (g n)‖ := by
  have hmass : Real.exp (-(((2 ^ (s + 1) : ℕ) : ℝ) * p)) ≤
      ∑ χ : AddChar (ZMod N) ℂ, ‖finiteFourierCoeff f χ‖ := by
    calc
      _ = Real.exp (-p) ^ (2 ^ (s + 1)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ gowersNorm (s + 1) f ^ (2 ^ (s + 1)) :=
        pow_le_pow_left₀ (Real.exp_nonneg _) hGowers _
      _ ≤ 𝔼 n, ‖f n‖ := gowersNorm_pow_le_mean_norm s f hf
      _ ≤ _ := mean_norm_le_fourier_sum f
  obtain ⟨χ, hχ⟩ := exists_large_nonnegative_weighted_term
    (fun _ : AddChar (ZMod N) ℂ => (1 : ℝ)) (fun χ => ‖finiteFourierCoeff f χ‖)
    (fun _ => by norm_num) (fun _ => norm_nonneg _) (Real.exp_pos _) (Real.exp_pos q)
    (by simpa using hN) (by simpa only [one_mul] using hmass)
  have hcorr : Real.exp (-(((2 ^ (s + 1) : ℕ) : ℝ) * p + q)) ≤
      ‖finiteFourierCoeff f χ‖ := by
    have heq : Real.exp (-(((2 ^ (s + 1) : ℕ) : ℝ) * p)) / Real.exp q =
        Real.exp (-(((2 ^ (s + 1) : ℕ) : ℝ) * p + q)) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    rwa [heq] at hχ
  obtain ⟨T, hTnorm, hT, hTeval⟩ := exists_cyclic_character_niltest χ
  refine ⟨fun n => χ n, ⟨{
    L := RationalTorus.Algebra 1
    dim := 1
    model := (RationalTorus.nilmanifold 1).raiseStep hs
    test := T.raiseStep hs
    norm := hTnorm
    complexity := ?_
    eval := ?_ }⟩, hcorr⟩
  · have hh := T.raiseStep_complexity hs (by norm_num) hT
    convert hh using 1
    norm_num [raisedNiltestBudget]
  · intro n
    rw [RationalFilteredNilmanifold.Niltest.raiseStep_evalCyclic]
    exact (hTeval n).symm

end Erdos3

end

section

universe u

namespace Erdos3

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_mixed_primitive_correlation_large_modulus (d : ℕ) {I : ℕ}
    (hI : CyclicNativeInverse (d + 2) I) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ g ∈ nativeCyclicFunctions (d + 3) N ((p + C) ^ C),
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n, f n * star (g n)‖ := by
  obtain ⟨A, _, hprimitive⟩ := exists_mixed_primitive_gowers d hI
  let B := I
  have hinverse : CyclicNativeInverse (d + 2) B := hI
  obtain ⟨D, _, hmodel⟩ := NativeMultidegreeNilcharacter.exists_mixed_primitive_niltest_budget d
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let V := (U + 2 + Polynomial.C B) ^ B
  let R := U + V + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + V + (R + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let u := (p + A) ^ A
  let v := (u + 2 + B) ^ B
  let r := u + v + 2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : u + v + (r + D) ^ D ≤ (p + C) ^ C := by
    simpa [X, U, V, R, u, v, r, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (r + D) ^ D := by positivity
  have huC : u ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  have hmC : (r + D) ^ D ≤ (p + C) ^ C := by linarith
  obtain ⟨q, hq, hqu, W, i, hW⟩ :=
    hprimitive hp ((Real.exp_le_exp.mpr huC).trans hN) f hf hGowers
  obtain ⟨g, ⟨G⟩, hg⟩ := hinverse (by linarith : 2 ≤ u + 2)
    (W.mixedPrimitiveFactor f i) (W.mixedPrimitiveFactor_norm f hf i)
    ((Real.exp_le_exp.mpr (by linarith : -(u + 2) ≤ -u)).trans hW)
  have hqr : q ≤ r := by dsimp [r]; linarith
  have hvr : v ≤ r := by dsimp [r]; linarith
  have hgmodel : g ∈ nativeCyclicFunctions (d + 2) N r :=
    ⟨{ G with complexity := G.complexity.mono hvr }⟩
  have hm := hmodel hr (W.mono hqr) i g hgmodel
  have hm' : (fun n : ZMod N => star (W.eval i (fun _ => (n.val : ℤ))) * g n) ∈
      nativeCyclicFunctions (d + 3) N ((r + D) ^ D) := by
    simpa only [NativeMultidegreeNilcharacter.mono_eval] using hm
  obtain ⟨M⟩ := hm'
  refine ⟨fun n => star (W.eval i (fun _ => (n.val : ℤ))) * g n,
    ⟨{ M with complexity := M.complexity.mono hmC }⟩, ?_⟩
  have heq : (𝔼 n : ZMod N, f n * star (star (W.eval i (fun _ => (n.val : ℤ))) * g n)) =
      𝔼 n : ZMod N, W.mixedPrimitiveFactor f i n * star (g n) := by
    apply Finset.expect_congr rfl
    intro n _
    simp only [NativeMultidegreeNilcharacter.mixedPrimitiveFactor, star_mul, star_star]
    ring
  rw [heq]
  exact (Real.exp_le_exp.mpr (neg_le_neg hvC)).trans hg

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_cyclicNativeInverse_step (d : ℕ) {I : ℕ}
    (hI : CyclicNativeInverse (d + 2) I) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicNativeInverse (d + 3) C := by
  obtain ⟨A, _, hlarge⟩ := exists_mixed_primitive_correlation_large_modulus d hI
  let L := 2 ^ (d + 4)
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + Polynomial.C L * X + 211)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hGowers
  have hp0 : 0 ≤ p := by linarith
  let u := (p + A) ^ A
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hLp : 0 ≤ (L : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp0
  have hsum : u + (L : ℝ) * p + 211 ≤ (p + C) ^ C := by
    simpa [X, u, Polynomial.eval₂_pow] using hbudget p hp0
  have huC : u ≤ (p + C) ^ C := by linarith
  by_cases hN : Real.exp u ≤ (N : ℝ)
  · obtain ⟨g, ⟨M⟩, hcorr⟩ := hlarge hp0 hN f hf hGowers
    exact ⟨g, ⟨{ M with complexity := M.complexity.mono huC }⟩,
      (Real.exp_le_exp.mpr (neg_le_neg huC)).trans hcorr⟩
  · obtain ⟨g, ⟨M⟩, hcorr⟩ :=
      exists_native_cyclic_small_modulus_correlation (d + 3) (by omega) (not_le.mp hN).le f hf hGowers
    have h211 : (211 : ℝ) ≤ (p + C) ^ C := by linarith
    have hc : (L : ℝ) * p + u ≤ (p + C) ^ C := by linarith
    exact ⟨g, ⟨{ M with complexity := M.complexity.mono h211 }⟩,
      (Real.exp_le_exp.mpr (neg_le_neg hc)).trans hcorr⟩

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

end Erdos3

end

section

namespace Erdos3.PositiveShiftBasis

universe u

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

universe u

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

universe u

namespace PositiveShiftBasis

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

end PositiveShiftBasis
end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def CyclicTranslatedNiltestShiftBound (degree N : ℕ) [NeZero N]
    (p error : ℝ) (a J : ZMod N → ℝ) (E : Finset (ZMod N)) : Prop :=
  ∀ h ∉ E, ∀ f : ZMod N → ℝ, PositiveCyclicNiltest.{0} degree N p f →
    ∀ b : ZMod N, (𝔼 x, a x * J (x + h) * f (b + x)) ≤ error

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalCubeNativeDetection
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem conjugationPower_twice (n : ℕ) (z : ℂ) :
    conjugationPower n (conjugationPower n z) = z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change star (conjugationPower n (star (conjugationPower n z))) = z
    rw [conjugationPower_star, ih, star_star]

namespace BooleanCubeKernel

def vertexFinsetEquiv (j : ℕ) : (Fin j → Bool) ≃ Finset (Fin j) where
  toFun ω := Finset.univ.filter (fun i => ω i)
  invFun s := fun i => decide (i ∈ s)
  left_inv ω := by funext i; simp
  right_inv s := by ext i; simp

theorem vertexFinsetEquiv_card {j : ℕ} (ω : Fin j → Bool) :
    (vertexFinsetEquiv j ω).card = booleanWeight ω := by
  simp only [vertexFinsetEquiv, Equiv.coe_fn_mk, booleanWeight]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem physical_twisted_cube_product {X : Type*} (j : ℕ)
    (f : (X → ℤ) → ℂ) (twist : Finset (Fin j) → (X → ℤ) → ℂ)
    (u : X → (Unit ⊕ Fin j) → ℤ) :
    (∏ s, conjugationPower s.card (f (physicalCubeVertexValue u s)) *
      twist s (physicalCubeVertexValue u s)) =
    mixedCubeProduct (fun ω x => f x * conjugationPower (booleanWeight ω)
      (twist (vertexFinsetEquiv j ω) x))
      (physicalCubeParametersEquiv X j u).1 (physicalCubeParametersEquiv X j u).2 := by
  rw [← (vertexFinsetEquiv j).prod_comp]
  apply Finset.prod_congr rfl
  intro ω _
  rw [vertexFinsetEquiv_card]
  change conjugationPower (booleanWeight ω)
      (f (physicalCubeVertexValue u (Finset.univ.filter (fun i => ω i)))) *
      twist (vertexFinsetEquiv j ω) (physicalCubeVertexValue u (Finset.univ.filter (fun i => ω i))) = _
  rw [physicalCubeParametersEquiv_vertex, map_mul, conjugationPower_twice]

theorem physical_twisted_cube_mean {X : Type*} (j : ℕ)
    (Q : Finset (X → ℤ)) (f : (X → ℤ) → ℂ)
    (twist : Finset (Fin j) → (X → ℤ) → ℂ) :
    (𝔼 cube : SupportedCube j (Q : Set (X → ℤ)),
      let u := (physicalCubeParametersEquiv X j).symm cube.val
      ∏ s, conjugationPower s.card (f (physicalCubeVertexValue u s)) *
        twist s (physicalCubeVertexValue u s)) =
      normalizedSupportedCubeSum j Q (fun ω x => f x *
        conjugationPower (booleanWeight ω) (twist (vertexFinsetEquiv j ω) x)) := by
  simp_rw [physical_twisted_cube_product, Equiv.apply_symm_apply]
  simp only [normalizedSupportedCubeSum, supportedCubeSum, Fintype.expect_eq_sum_div_card,
    Nat.card_eq_fintype_card]

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

noncomputable def integerSelfSiteTest {X : Type*} (q : ℕ) (f : (X → ℤ) → ℂ)
    (site : Finset (Fin q)) (y : X → ℝ) : ℂ :=
  conjugationPower site.card (f (fun x => ⌊y x⌋))

theorem integerSelfSiteTest_norm_le {X : Type*} (q : ℕ) (f : (X → ℤ) → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (site : Finset (Fin q)) (y : X → ℝ) :
    ‖integerSelfSiteTest q f site y‖ ≤ 1 := by
  rw [integerSelfSiteTest, conjugationPower_norm]
  exact hf _

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PreparedModularGeneralCenteredLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

section Joint

variable {C B K I : Type*} [MeasurableSpace C] [Fintype K] [Fintype I]
variable (A : Finset B) (hA : A.Nonempty)
variable (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
variable (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)

include hA hW hZ in

theorem selectedJointDensityMass_measurable
    (D : C → B → (K × I → ℤ) → ℝ)
    (hDm : ∀ a z, Measurable (fun c => D c a z)) :
    Measurable (fun c => selectedJointDensityMass A modulus T W (D c)) := by
  have h := (selectedJointReference A hA modulus T W hW hZ).mean_measurable
    (fun c z => D c z.1.val z.2.val) (fun z => hDm z.1.val z.2.val)
  simpa only [selectedJointReference_densityMass] using h

theorem selectedJointFiniteLaw_weight_measurable
    (D : C → B → (K × I → ℤ) → ℝ)
    (hDm : ∀ a z, Measurable (fun c => D c a z))
    (hD0 : ∀ c a z, 0 ≤ D c a z)
    (hD : ∀ c, 0 < selectedJointDensityMass A modulus T W (D c))
    (z : A × rectangularWeightIndices 0 W 1) :
    Measurable (fun c =>
      (selectedJointFiniteLaw A hA modulus T W hW hZ (D c) (hD0 c) (hD c)).weight z) := by
  simp only [selectedJointFiniteLaw_weight]
  exact ((hDm z.1.val z.2.val).const_mul _).div
    (selectedJointDensityMass_measurable A hA modulus T W hW hZ D hDm)

theorem selectedJointFiniteLaw_realTest_measurable
    (D : C → B → (K × I → ℤ) → ℝ)
    (hDm : ∀ a z, Measurable (fun c => D c a z))
    (hD0 : ∀ c a z, 0 ≤ D c a z)
    (hD : ∀ c, 0 < selectedJointDensityMass A modulus T W (D c))
    (f : B → (K × I → ℤ) → ℝ) :
    Measurable (fun c =>
      (selectedJointFiniteLaw A hA modulus T W hW hZ (D c) (hD0 c) (hD c)).mean
        (fun z => f z.1.val z.2.val)) :=
  Finset.measurable_sum _ (fun z _ =>
    (selectedJointFiniteLaw_weight_measurable A hA modulus T W hW hZ D hDm hD0 hD z).mul_const _)

theorem selectedJointFiniteLaw_realTest_integrable
    (μ : Measure C) [IsFiniteMeasure μ]
    (D : C → B → (K × I → ℤ) → ℝ)
    (hDm : ∀ a z, Measurable (fun c => D c a z))
    (hD0 : ∀ c a z, 0 ≤ D c a z)
    (hD : ∀ c, 0 < selectedJointDensityMass A modulus T W (D c))
    (f : B → (K × I → ℤ) → ℝ) (hf : ∀ a z, |f a z| ≤ 1) :
    Integrable (fun c =>
      (selectedJointFiniteLaw A hA modulus T W hW hZ (D c) (hD0 c) (hD c)).mean
        (fun z => f z.1.val z.2.val)) μ := by
  apply Integrable.of_bound
    (selectedJointFiniteLaw_realTest_measurable A hA modulus T W hW hZ D hDm hD0 hD f).aestronglyMeasurable 1
  apply ae_of_all
  intro c
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ((selectedJointFiniteLaw A hA modulus T W hW hZ (D c) (hD0 c) (hD c)).mean_mem_Icc
    (fun z => f z.1.val z.2.val) (fun z => abs_le.mp (hf z.1.val z.2.val)))

end Joint

namespace VectorPolynomial

open Module Submodule

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (L₀ : ℕ)
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (X : Type*) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

noncomputable def allocatedJointBaseDensity (base : X → ℤ)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) : ℝ :=
  allocatedCoefficientDensity B U b hb o hR hσ S (affineSampleCoefficientTorus U
    (fun j => translate (fun t => (base t : ℝ)) (poly j))
    (fun j => coefficients_translate_mem (U j) (fun t => (base t : ℝ)) (poly j) (hmem j))
    (fun k t => (z (k, t) : ℝ)))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

omit [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [Fintype X] in
theorem allocatedJointBaseDensity_nonneg (base : X → ℤ)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    0 ≤ allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem base z :=
  canonicalCoefficientDensity_nonneg U b hb o (allocatedLayerCenters B U b S)
    (allocatedLayerWidths B U b S) (allocatedLayerIntegerPMFs B U b hR hσ S)
    (allocatedLayerWidths_pos B U b hR hσ S) _

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))


variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (X : Type*) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "hwidths" => narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
local notation "baseDensity" => allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

noncomputable def allocatedOriginalPathLaw :
    FiniteProbabilityWeights (bases × rectangularWeightIndices 0 widths 1) :=
  selectedJointFiniteLaw bases hbases stride cells widths hwidths hmass baseDensity
    (allocatedJointBaseDensity_nonneg B U b hb o hR hσ S X poly hmem) htotal


noncomputable def allocatedSlicedCubeSource
    (H : LayerSamplerVariables G I n B → ℕ) (hH : ∀ k, 0 < H k)
    (c : LayerSamplerVariables G I n B → ℤ) (step : ℕ) (f : (X → ℤ) → ℂ) : ℂ :=
  (FiniteProbabilityWeights.pi (fun k => integerScalarCubeWeights (Fin dim) (H k) (hH k))).complexMean
    (fun cube =>
      (𝔼 base ∈ bases, ∑' z,
        ((selectedResidueSmoothPMF stride cells widths hwidths hmass z).toReal : ℂ) *
          (physicalCubeSiteTest (integerSelfSiteTest dim f)
            (physicalCubeRootDifferences
              (commonStridePoint c step (fun k => (cube k none : ℤ)))
              (fun j k => (step : ℤ) * (cube k (some j) : ℤ)) base z) *
            (baseDensity base z : ℂ))) / (selectedJointDensityMass bases stride cells widths baseDensity : ℂ))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j) (c : ∀ j, U j)

omit [DecidableEq G] [Fintype X] [∀ index, DecidableEq (I index)]
  [∀ axis, DecidableEq (B axis)] in
theorem allocatedJointBaseDensity_subtractConstant_affine (a : X → ℤ)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedJointBaseDensity B U b hb o hR hσ S X (fun j => subtractConstant (c j).val (poly j)) (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j)) a z =
      allocatedAffineDensity B U b hb o hR hσ S poly hmem c
        (fun k i => (jointIntegerFrame (a, z) k i : ℝ)) := by
  unfold allocatedJointBaseDensity
  rw [affineSampleCoefficientTorus_joint_frame U
    (fun j => subtractConstant (c j).val (poly j))
    (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j)) a z,
    affineSampleCoefficientTorus_subtractConstant U poly hmem c]
  rfl

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (N : X → ℕ) (hN : ∀ i, 0 < N i)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X
    (fun j => subtractConstant (c j).val (poly j))
    (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j))))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

noncomputable def allocatedCenteredJointDensity
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (a : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ) : ℝ :=
  allocatedCoefficientDensity B U b hb o hR hσ S
    (coefficientConstantCenter U center +
      affineSampleCoefficientTorus U poly hmem
        (fun k i => (jointIntegerFrame (a, z) k i : ℝ)))

omit [Fintype X] in
theorem allocatedCenteredJointDensity_eq_affine
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (c : ∀ j, U j)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))))
    (a : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center a z =
      allocatedAffineDensity B U b hb o hR hσ S poly hmem c
        (fun k i => (jointIntegerFrame (a, z) k i : ℝ)) := by
  unfold allocatedCenteredJointDensity allocatedAffineDensity
  rw [centeredAffineCoefficientTorus_eq_subtractive, ← hc]

omit [Fintype X] in
theorem allocatedJointBaseDensity_subtractConstant_centered
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (c : ∀ j, U j)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1)))) :
    allocatedJointBaseDensity B U b hb o hR hσ S X
      (fun j => subtractConstant (c j).val (poly j))
      (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j)) =
    allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center := by
  funext a z
  rw [allocatedJointBaseDensity_subtractConstant_affine,
    allocatedCenteredJointDensity_eq_affine B U b hb o hR hσ S poly hmem center c hc]

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

omit [Fintype X] in
theorem allocatedCenteredJointDensity_nonneg
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (a : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    0 ≤ allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center a z :=
  canonicalCoefficientDensity_nonneg U b hb o (allocatedLayerCenters B U b S)
    (allocatedLayerWidths B U b S) (allocatedLayerIntegerPMFs B U b hR hσ S)
    (allocatedLayerWidths_pos B U b hR hσ S) _

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

omit [Fintype X] [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedCenteredJointDensity_measurable_center
    (a : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    Measurable (fun center =>
      allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center a z) :=
  (canonicalCoefficientDensity_measurable U b hb o
    (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
    (allocatedLayerIntegerPMFs B U b hR hσ S)).comp
      ((coefficientConstantCenter_continuous U).measurable.add measurable_const)

variable (N : X → ℕ) (hN : ∀ i, 0 < N i)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)

omit [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
  [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)] in
theorem allocatedOriginalPathLaw_subtractConstant_eq_centered
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (c : ∀ j, U j)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))))
    (htotal : 0 < selectedJointDensityMass bases stride cells widths
      (allocatedJointBaseDensity B U b hb o hR hσ S X
        (fun j => subtractConstant (c j).val (poly j))
        (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j))))
    (hcenter : 0 < selectedJointDensityMass bases stride cells widths
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center)) :
    allocatedOriginalPathLaw B U b hb o hR hσ S X
      (fun j => subtractConstant (c j).val (poly j))
      (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j))
      N hN hW hτ hξ stride cells hmass bases hbases htotal =
    selectedJointFiniteLaw bases hbases stride cells widths
      (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN) hmass
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center)
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem center) hcenter := by
  unfold allocatedOriginalPathLaw
  simp only [allocatedJointBaseDensity_subtractConstant_centered B U b hb o hR hσ S poly hmem center c hc]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
variable (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
variable (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
variable (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)

variable {X : Type*}
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
variable (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
variable (a : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem allocatedFixedScale_center_mixture_compare
    {m : ℕ} {X G : Type*} [Fintype X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hσ1 : ∀ j, σ j ≤ 1) (C V : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (W : Option (LayerSamplerVariables G I n B) × X → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z)
    (base : X → ℤ) (root : LayerSamplerVariables G I n B → ℤ)
    (hlocal : ∀ center, 0 < selectedResidueDensityMass stride T W
      (allocatedCenteredJointDensity B U b hb o hR hσ S p hm center base))
    {P : ℝ}
    (hclose : ∀ center, |selectedResidueDensityMass stride T W
      (allocatedCenteredJointDensity B U b hb o hR hσ S p hm center base) - 1| ≤
        3 * positiveProjectionAccuracy P)
    (hcomparison : ∀ (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
      (φ : (X → ℝ) → ℂ), (∀ v, ‖φ v‖ ≤ 1) →
      let sample := fun z => affineSampleCoefficientTorus U p hm
        (fun k i => (jointIntegerFrame (base,z) k i : ℝ))
      let D₀ := allocatedCoefficientDensity B U b hb o hR hσ S
      let fiber := fun z => coefficientFiberAverage U μ root
        (fun x => D₀ (coefficientConstantCenter U center + x))
        (coefficientEvaluationTorus U root (sample z))
      ‖(∑' z, ((selectedResidueSmoothPMF stride T W hW hZ z).toReal : ℂ) *
        (φ ((fun i => (base i : ℝ)) + physicalAffineSite root z) *
          (allocatedCenteredJointDensity B U b hb o hR hσ S p hm center base z : ℂ))) -
        (∑' z, ((selectedResidueSmoothPMF stride T W hW hZ z).toReal : ℂ) *
          (φ ((fun i => (base i : ℝ)) + physicalAffineSite root z) * (fiber z : ℂ)))‖ ≤
        3 * positiveProjectionAccuracy P) :
    ∀ ψ : (X → ℝ) → ℂ, (∀ v, ‖ψ v‖ ≤ 1) →
      ‖(∫ center, ∑' z, ((selectedResidueDensityPMF stride T W hW hZ
          (allocatedCenteredJointDensity B U b hb o hR hσ S p hm center base)
          (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S p hm center base)
          (hlocal center) z).toReal : ℂ) * ψ (physicalAffineSite root z) ∂μ) -
        ∑' z, ((selectedResidueSmoothPMF stride T W hW hZ z).toReal : ℂ) *
          ψ (physicalAffineSite root z)‖ ≤ 6 * positiveProjectionAccuracy P := by
  intro ψ hψ
  let D₀ := allocatedCoefficientDensity B U b hb o hR hσ S
  have hspec := allocatedCoefficientDensity_spec B U b hb o hR hσ S
    hσ1 Cinv hCinv hchart hsmall μ ν
  have hcap := allocatedCoefficientDensity_bounds B U b hb o hR hσ S C V hC hV
    hσ1 Cinv hCinv hchart hsmall
  have hbound (x) : ‖D₀ x‖ ≤
      (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hcap x).1]
    exact (hcap x).2
  let D := fun center => allocatedCenteredJointDensity B U b hb o hR hσ S p hm center base
  let sample := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
    affineSampleCoefficientTorus U p hm
    (fun k i => (jointIntegerFrame (base,z) k i : ℝ))
  let F := fun center z => coefficientFiberAverage U μ root
    (fun x => D₀ (coefficientConstantCenter U center + x))
    (coefficientEvaluationTorus U root (sample z))
  apply selectedResidue_center_mixture_compare μ stride T W hW hZ D
    (fun z => allocatedCenteredJointDensity_measurable_center B U b hb o hR hσ S p hm base z)
    (fun center => allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S p hm center base)
    hlocal F
    (fun z => coefficientMixedFiber_integrable U μ D₀ hspec.1 hbound root _)
    (fun z => (coefficientMixedFiber_average U μ D₀ hspec.1 hbound root _).trans hspec.2.2.2.1)
    (fun z => ψ (physicalAffineSite root z)) (fun _ => hψ _)
  intro center
  have hraw := hcomparison center (fun v => ψ (v - (fun i => (base i : ℝ))))
    (fun _ => hψ _)
  dsimp only at hraw
  simp only [add_sub_cancel_left] at hraw
  have herr := selectedResidueDensityPMF_error_of_bounded_test stride T W hW hZ (D center)
    (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S p hm center base)
    (hlocal center) (fun z => ψ (physicalAffineSite root z)) (fun _ => hψ _) hraw (hclose center)
  exact herr.trans_eq (by ring)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (N : X → ℕ) (hN : ∀ i, 0 < N i)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFixedScaleJointMarginal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_allocated_narrow_normalization (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let pa := fun (base : X → ℤ) j => translate (fun d => (base d : ℝ)) (p j)
    let hma := fun (base : X → ℤ) j => coefficients_translate_mem (U j) (fun d => (base d : ℝ)) (p j) (hm j)
    let density := fun base z => allocatedCoefficientDensity B U basis hb o hR hσ S
      (affineSampleCoefficientTorus U (pa base) (hma base) (fun k d => (z (k, d) : ℝ)))
    ∃ (_hwidths : ∀ z, 0 < widths z) (_hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
      (∀ base, |selectedResidueDensityMass stride T widths (density base) - 1| ≤
        3 * positiveProjectionAccuracy P) ∧
      ∀ (bases : Finset (X → ℤ)), bases.Nonempty →
        let Z := selectedJointDensityMass bases stride T widths density
        |Z - 1| ≤ Real.exp (-P) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2 := by
  obtain ⟨A₀, _, hmass⟩ := exists_affine_coefficient_density_mass m
  obtain ⟨b, _, hbnd⟩ := exists_positiveComparisonDataBudget_bound m 0
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    (((Polynomial.X + Polynomial.C b) ^ b + 8 * Polynomial.X + 128 + Polynomial.C A₀) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ hW hWP hτ hτP hξ hξ1 hξP
    N hsize rank hrank hRank T hT widths pa hma density
  have h2P : 0 ≤ 2 * P := mul_nonneg (by norm_num) hP
  have hP2P : P ≤ 2 * P := by linarith
  have hτξ : 0 < ξ * τ := mul_pos hξ hτ
  have hτξP : (ξ * τ)⁻¹ ≤ Real.exp (2 * P) := by
    rw [mul_inv_rev]
    calc
      τ⁻¹ * ξ⁻¹ ≤ Real.exp P * Real.exp P := by gcongr
      _ = Real.exp (2 * P) := by rw [← Real.exp_add]; congr 1; ring
  let Q := positiveComparisonDataBudget m 0 P + spatialSamplingBudget (2 * P)
  have hdata := positiveComparisonDataBudget_bounds m 0 hP
  have hdataQ : positiveComparisonDataBudget m 0 P ≤ Q :=
    le_add_of_nonneg_right (h2P.trans (le_spatialSamplingBudget h2P))
  have hspatialQ : spatialSamplingBudget (2 * P) ≤ Q := le_add_of_nonneg_left hdata.1
  have hPQ : P ≤ Q := hdata.2.1.trans hdataQ
  have hQ : 0 ≤ Q := hP.trans hPQ
  have hExp := Real.exp_le_exp.mpr hPQ
  have hcut : (Q + A₀) ^ A₀ ≤ (P + A) ^ A := by
    have hbase : Q + (A₀ : ℝ) ≤ (P + b) ^ b + 8 * P + 128 + A₀ := by
      have h := hbnd P hP
      dsimp [Q, spatialSamplingBudget]
      linarith
    calc
      _ ≤ ((P + b) ^ b + 8 * P + 128 + A₀) ^ A₀ :=
        pow_le_pow_left₀ (add_nonneg hQ (Nat.cast_nonneg A₀)) hbase A₀
      _ ≤ _ := by simpa [Polynomial.eval₂_pow] using hbudget P hP
  obtain ⟨_, F, inst, frequency, coeff, hfreq, hcoeff, happ⟩ :=
    exists_allocated_positive_fourier_data B U basis hb o S C V hC hV 0
      hR hσ hσ1 Cinv hCinv hchart hsmall hP hmSize hK hRP hσP hcount hI hn hJ hAP hLP hCP hVP
  let _ := inst
  have hspec := allocatedCoefficientDensity_spec B U basis hb o hR hσ S
    hσ1 Cinv hCinv hchart hsmall μ ν
  have hN (d) : 0 < N d := by exact_mod_cast (Real.exp_pos _).trans_le (hsize d)
  have hwidths := narrowTrimmedSpatialWidths_pos (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτ hξ N hN
  have hwidthLower (z : Option (LayerSamplerVariables G I n B) × X) :
      spatialWidthFraction (2 * P) (ξ * τ) * (N z.2 : ℝ) ≤ widths z :=
    (spatialWidthFraction_le_allocated_width h2P hW
      (hWP.trans (Real.exp_le_exp.mpr hP2P)) hτξ.le N z).trans
        (narrowTrimmedSpatialWidths_lower hW hτ hξ1 N hN z)
  have hη : 0 < positiveProjectionAccuracy P := Real.exp_pos _
  have hηQ : 1 / positiveProjectionAccuracy P ≤ Real.exp Q := by
    simp only [one_div, positiveProjectionAccuracy, Real.exp_neg, inv_inv]
    exact Real.exp_le_exp.mpr (hdata.2.2.1.trans hdataQ)
  have hlocal (base : X → ℤ) :
      ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z,
        |selectedResidueDensityMass stride T widths (density base) - 1| ≤
          3 * positiveProjectionAccuracy P := by
    have hpa (j) : DegreeLE (1 : X → ℕ) (j.val + 1) (pa base j) :=
      degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j)
    have hranka (j) : HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (pa base j) :=
      (hasLayerSamplingRank_translate_iff _ _ _ _ _ _ (hp j)).mpr (hrank j)
    obtain ⟨hZ, hclose⟩ := hmass hQ (hX.trans hPQ) (hdim.trans hPQ) U μ
      (Real.exp_nonneg Q) le_rfl frequency
      (fun t j d hd i => (hfreq t j d hd i).trans (Real.exp_le_exp.mpr hdataQ))
      coeff (Real.exp_nonneg Q) le_rfl (hcoeff.trans (Real.exp_le_exp.mpr hdataQ))
      (pa base) hpa (hma base) stride hs (Real.exp_nonneg Q) le_rfl
      (spatialWidthFraction_pos (2 * P) hτξ) hη
      ((spatialWidthFraction_inv_le h2P hτξ hτξP).trans (Real.exp_le_exp.mpr hspatialQ)) hηQ
      (fun d => (hsP d).trans hExp) (fun d => (N d : ℝ))
      (fun d => (Real.exp_le_exp.mpr hcut).trans (hsize d)) hranka
      ((Real.exp_le_exp.mpr hcut).trans hRank) T hT widths hwidths
      hwidthLower
      (allocatedCoefficientDensity B U basis hb o hR hσ S) hspec.2.2.1 hspec.2.2.2.1 hη.le happ
    refine ⟨hZ, ?_⟩
    change |selectedResidueDensityMass stride T widths (density base) - 1| ≤
      2 * positiveProjectionAccuracy P + positiveProjectionAccuracy P at hclose
    linarith
  obtain ⟨hZ, _⟩ := hlocal 0
  have hclose (base) := (hlocal base).choose_spec
  exact ⟨hwidths, hZ, hclose, fun bases hbases =>
    selectedJointDensityMass_positive_accuracy bases hbases stride T widths density hP hclose⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

theorem narrowTrimmedSpatial_site_width {G J X : Type*}
    [Fintype G] [Fintype J] {W τ ξ : ℝ}
    (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (root : G ⊕ J → ℤ) (hroot : (∑ k, |(root k : ℝ)|) ≤ W)
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (i : X) :
    physicalSiteWidth root (narrowTrimmedSpatialWidths W τ ξ N) i ≤
      (spatialTrimMargin τ N i : ℝ) := by
  apply le_trans _ (spatialTrimMargin_fits hW hτ.le root hroot N i)
  unfold physicalSiteWidth
  exact add_le_add (narrowTrimmedSpatialWidths_le hW hτ hξ N hN _)
    (Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left
      (narrowTrimmedSpatialWidths_le hW hτ hξ N hN _) (abs_nonneg _)))

noncomputable def narrowPhysicalSiteMap {G J X T : Type*}
    [Fintype G] [Fintype J] [Fintype X] [DecidableEq X]
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (N : X → ℕ) (hN : ∀ i, 0 < N i)
    (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
    (root : T → G ⊕ J → ℤ) (hroot : ∀ t, (∑ k, |(root t k : ℝ)|) ≤ W) :
    (trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0 (narrowTrimmedSpatialWidths (G := G) (J := J) W τ ξ N) 1) →
      T → integerBox N :=
  fun z t => ⟨jointIntegerPhysicalSite (root t) (z.1.val, z.2.val),
    jointIntegerPhysicalSite_mem_box (root t) N (spatialTrimMargin τ N) hmargin _
      (narrowTrimmedSpatial_site_width hW hτ hξ (root t) (hroot t) N hN) z⟩

theorem narrowPhysicalSiteMap_cast {G J X T : Type*}
    [Fintype G] [Fintype J] [Fintype X] [DecidableEq X]
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (N : X → ℕ) (hN : ∀ i, 0 < N i)
    (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
    (root : T → G ⊕ J → ℤ) (hroot : ∀ t, (∑ k, |(root t k : ℝ)|) ≤ W)
    (z) (t) :
    (fun i => ((narrowPhysicalSiteMap hW hτ hξ N hN hmargin root hroot z t).val i : ℝ)) =
      (fun i => (z.1.val i : ℝ)) + physicalAffineSite (root t) z.2.val :=
  jointIntegerPhysicalSite_cast (root t) (z.1.val, z.2.val)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_allocated_narrow_oneSite_domination (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let pa := fun (base : X → ℤ) j => translate (fun d => (base d : ℝ)) (p j)
    let hma := fun (base : X → ℤ) j => coefficients_translate_mem (U j) (fun d => (base d : ℝ)) (p j) (hm j)
    let density := fun base z => allocatedCoefficientDensity B U basis hb o hR hσ S
      (affineSampleCoefficientTorus U (pa base) (hma base) (fun k d => (z (k, d) : ℝ)))
    ∃ (hwidths : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
    ∀ (base : X → ℤ) (root : LayerSamplerVariables G I n B → ℤ),
      (∀ k, |(root k : ℝ)| ≤ Real.exp P) →
    ∀ (φ : (X → ℝ) → ℝ), (∀ u, φ u ∈ Set.Icc (0 : ℝ) 1) →
      (∑' z, (selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal *
        (φ (fun i => (base i : ℝ) + physicalAffineSite root z i) * density base z)) ≤
      (∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)) *
        (∑' z, (selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal *
          φ (fun i => (base i : ℝ) + physicalAffineSite root z i)) +
        3 * positiveProjectionAccuracy P := by
  obtain ⟨A₀, _, hcompare⟩ := exists_affine_oneSite_density_comparison m
  obtain ⟨b, _, hbnd⟩ := exists_positiveComparisonDataBudget_bound m 0
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    (((Polynomial.X + Polynomial.C b) ^ b + 8 * Polynomial.X + 128 + Polynomial.C A₀) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ hW hWP hτ hτP hξ hξ1 hξP
    N hsize rank hrank hRank T hT widths pa hma density
  have h2P : 0 ≤ 2 * P := mul_nonneg (by norm_num) hP
  have hP2P : P ≤ 2 * P := by linarith
  have hτξ : 0 < ξ * τ := mul_pos hξ hτ
  have hτξP : (ξ * τ)⁻¹ ≤ Real.exp (2 * P) := by
    rw [mul_inv_rev]
    calc
      τ⁻¹ * ξ⁻¹ ≤ Real.exp P * Real.exp P := by gcongr
      _ = Real.exp (2 * P) := by rw [← Real.exp_add]; congr 1; ring
  let Q := positiveComparisonDataBudget m 0 P + spatialSamplingBudget (2 * P)
  have hdata := positiveComparisonDataBudget_bounds m 0 hP
  have hdataQ : positiveComparisonDataBudget m 0 P ≤ Q :=
    le_add_of_nonneg_right (h2P.trans (le_spatialSamplingBudget h2P))
  have hspatialQ : spatialSamplingBudget (2 * P) ≤ Q := le_add_of_nonneg_left hdata.1
  have hPQ : P ≤ Q := hdata.2.1.trans hdataQ
  have hQ : 0 ≤ Q := hP.trans hPQ
  have hExp := Real.exp_le_exp.mpr hPQ
  have hcut : (Q + A₀) ^ A₀ ≤ (P + A) ^ A := by
    have hbase : Q + (A₀ : ℝ) ≤ (P + b) ^ b + 8 * P + 128 + A₀ := by
      have h := hbnd P hP
      dsimp [Q, spatialSamplingBudget]
      linarith
    calc
      _ ≤ ((P + b) ^ b + 8 * P + 128 + A₀) ^ A₀ :=
        pow_le_pow_left₀ (add_nonneg hQ (Nat.cast_nonneg A₀)) hbase A₀
      _ ≤ _ := by simpa [Polynomial.eval₂_pow] using hbudget P hP
  obtain ⟨_, F, inst, frequency, coeff, hfreq, hcoeff, happ⟩ :=
    exists_allocated_positive_fourier_data B U basis hb o S C V hC hV 0
      hR hσ hσ1 Cinv hCinv hchart hsmall hP hmSize hK hRP hσP hcount hI hn hJ hAP hLP hCP hVP
  let _ := inst
  have hN (d) : 0 < N d := by exact_mod_cast (Real.exp_pos _).trans_le (hsize d)
  have hwidths := narrowTrimmedSpatialWidths_pos (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτ hξ N hN
  have hwidthLower (z : Option (LayerSamplerVariables G I n B) × X) :
      spatialWidthFraction (2 * P) (ξ * τ) * (N z.2 : ℝ) ≤ widths z :=
    (spatialWidthFraction_le_allocated_width h2P hW
      (hWP.trans (Real.exp_le_exp.mpr hP2P)) hτξ.le N z).trans
        (narrowTrimmedSpatialWidths_lower hW hτ hξ1 N hN z)
  have hη : 0 < positiveProjectionAccuracy P := Real.exp_pos _
  have hηQ : 1 / positiveProjectionAccuracy P ≤ Real.exp Q := by
    simp only [one_div, positiveProjectionAccuracy, Real.exp_neg, inv_inv]
    exact Real.exp_le_exp.mpr (hdata.2.2.1.trans hdataQ)
  have hfiber (root : LayerSamplerVariables G I n B → ℤ) (y) :=
    allocatedCoefficientDensity_fiber_cap B U basis hb o hR hσ S (fun j => (V j : ℝ))
      (fun j => (V j).coe_nonneg) (fun j => (hV j).2) μ ν hσ1 Cinv hCinv hchart hsmall root y
  have hlocal (base : X → ℤ) (root : LayerSamplerVariables G I n B → ℤ)
      (hroot : ∀ k, |(root k : ℝ)| ≤ Real.exp P)
      (φ : (X → ℝ) → ℝ) (hφ : ∀ u, φ u ∈ Set.Icc (0 : ℝ) 1) :
      ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z,
      (∑' z, (selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal *
        (φ (fun i => (base i : ℝ) + physicalAffineSite root z i) * density base z)) ≤
      (∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)) *
        (∑' z, (selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal *
          φ (fun i => (base i : ℝ) + physicalAffineSite root z i)) +
        3 * positiveProjectionAccuracy P := by
    have hpa (j) : DegreeLE (1 : X → ℕ) (j.val + 1) (pa base j) :=
      degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j)
    have hranka (j) : HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (pa base j) :=
      (hasLayerSamplingRank_translate_iff _ _ _ _ _ _ (hp j)).mpr (hrank j)
    let ψ : (X → ℝ) → ℂ := fun v => (φ (fun i => (base i : ℝ) + v i) : ℂ)
    have hψ (v) : ‖ψ v‖ ≤ 1 := by
      dsimp only [ψ]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hφ _).1]
      exact (hφ _).2
    obtain ⟨hZ, he⟩ := hcompare hQ (hX.trans hPQ) (hdim.trans hPQ) U μ
      root (fun i => Fin.elim0 i) (Real.exp_nonneg Q) (Real.exp_nonneg Q) le_rfl le_rfl
      (fun s k => by
        have hs : s = ∅ := Finset.eq_empty_of_isEmpty s
        simpa [affineSite, hs] using (hroot k).trans hExp)
      frequency (fun t j d hd i => (hfreq t j d hd i).trans (Real.exp_le_exp.mpr hdataQ))
      coeff (Real.exp_nonneg Q) le_rfl (hcoeff.trans (Real.exp_le_exp.mpr hdataQ))
      (pa base) hpa (hma base) stride hs (Real.exp_nonneg Q) le_rfl
      (spatialWidthFraction_pos (2 * P) hτξ) hη
      ((spatialWidthFraction_inv_le h2P hτξ hτξP).trans (Real.exp_le_exp.mpr hspatialQ)) hηQ
      (fun d => (hsP d).trans hExp) (fun d => (N d : ℝ))
      (fun d => (Real.exp_le_exp.mpr hcut).trans (hsize d)) hranka
      ((Real.exp_le_exp.mpr hcut).trans hRank)
      0 (by simp) (fun _ => ψ) (fun _ v => hψ v) T hT widths hwidths hwidthLower
      (allocatedCoefficientDensity B U basis hb o hR hσ S) (fun y => (hfiber root y).1)
      hη.le (fun y => by simpa only [norm_sub_rev] using happ y)
    simp only [layeredSiteWeight_physical, ψ] at he
    have hbound := selectedResidueSmoothPMF_test_le_of_complex stride T widths hwidths hZ
      (density base)
      (fun z => coefficientFiberAverage U μ root (allocatedCoefficientDensity B U basis hb o hR hσ S)
        (coefficientEvaluationTorus U root (affineSampleCoefficientTorus U (pa base) (hma base)
          (fun k i => (z (k, i) : ℝ)))))
      (fun z => φ (fun i => (base i : ℝ) + physicalAffineSite root z i))
      (fun z => (hfiber root _).2.2) (fun z => (hφ _).1) he
    refine ⟨hZ, hbound.trans_eq ?_⟩
    ring
  obtain ⟨hZ, _⟩ := hlocal 0 0 (by intro k; simpa using (Real.exp_nonneg P))
    (fun _ => 0) (fun _ => by simp)
  refine ⟨hwidths, hZ, ?_⟩
  intro base root hroot φ hφ
  exact (hlocal base root hroot φ hφ).choose_spec

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_allocated_fixed_scale_centered_normalization (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∃ (_hwidths : ∀ z, 0 < widths z) (_hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
      ∀ center : CoefficientTorus (K := LayerSamplerVariables G I n B) U,
        let density := allocatedCenteredJointDensity B U basis hb o hR hσ S p hm center
        (∀ base, |selectedResidueDensityMass stride T widths (density base) - 1| ≤
          3 * positiveProjectionAccuracy P) ∧
        ∀ (bases : Finset (X → ℤ)), bases.Nonempty →
          let Z := selectedJointDensityMass bases stride T widths density
          |Z - 1| ≤ Real.exp (-P) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2 := by
  classical
  obtain ⟨A, hA, hnorm⟩ := exists_allocated_narrow_normalization m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ hW hWP hτ hτP hξ hξ1 hξP
    N hsize rank hrank hRank T hT widths
  obtain ⟨hwidths, hZ, _⟩ := hnorm B U basis S hb o μ ν hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmall hP hmSize hK hX hdim hRP hσP hcount hI hn hJ hAP hLP hCP hVP
    p hp hm stride hs hsP hW hWP hτ hτP hξ hξ1 hξP N hsize hrank hRank T hT
  refine ⟨hwidths, hZ, ?_⟩
  intro center
  obtain ⟨c, hc⟩ := exists_subtractive_constant_center U center
  let pc := fun j => subtractConstant (c j).val (p j)
  let hmc := fun j => coefficients_subtractConstant_mem (U j) (c j) (p j) (hm j)
  have hpc (j : Fin m) : DegreeLE (1 : X → ℕ) (j.val + 1) (pc j) :=
    (hp j).subtractConstant (c j).val
  have hrankc (j : Fin m) :
      HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (pc j) :=
    (hasLayerSamplingRank_subtractConstant_iff (Nat.zero_lt_succ _) _ _ (U j)
      (c j).val (p j)).mpr (hrank j)
  obtain ⟨_, _, hlocal, hjoint⟩ := hnorm B U basis S hb o μ ν hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmall hP hmSize hK hX hdim hRP hσP hcount hI hn hJ hAP hLP hCP hVP
    pc hpc hmc stride hs hsP hW hWP hτ hτP hξ hξ1 hξP N hsize hrankc hRank T hT
  change (∀ base, |selectedResidueDensityMass stride T widths
      (allocatedJointBaseDensity B U basis hb o hR hσ S X pc hmc base) - 1| ≤
        3 * positiveProjectionAccuracy P) at hlocal
  change ∀ bases : Finset (X → ℤ), bases.Nonempty →
    let Z := selectedJointDensityMass bases stride T widths
      (allocatedJointBaseDensity B U basis hb o hR hσ S X pc hmc)
    |Z - 1| ≤ Real.exp (-P) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2 at hjoint
  have hdensity := allocatedJointBaseDensity_subtractConstant_centered
    B U basis hb o hR hσ S p hm center c hc
  change allocatedJointBaseDensity B U basis hb o hR hσ S X pc hmc =
    allocatedCenteredJointDensity B U basis hb o hR hσ S p hm center at hdensity
  rw [hdensity] at hlocal hjoint
  exact ⟨hlocal, hjoint⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def AllocatedFixedScaleCenteredOneSiteStatement (m A : ℕ) : Prop :=
    ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let sample := fun (base : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ) =>
      affineSampleCoefficientTorus U p hm (fun k i => (jointIntegerFrame (base,z) k i : ℝ))
    let D₀ := allocatedCoefficientDensity B U basis hb o hR hσ S
    ∃ (hwidths : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
    ∀ (base : X → ℤ) (root : LayerSamplerVariables G I n B → ℤ),
      (∀ k, |(root k : ℝ)| ≤ Real.exp P) →
    ∀ (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
      (φ : (X → ℝ) → ℂ), (∀ u, ‖φ u‖ ≤ 1) →
      let fiber := fun z => coefficientFiberAverage U μ root
        (fun x => D₀ (coefficientConstantCenter U center + x))
        (coefficientEvaluationTorus U root (sample base z))
      ‖(∑' z, ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
        (φ ((fun i => (base i : ℝ)) + physicalAffineSite root z) *
          (allocatedCenteredJointDensity B U basis hb o hR hσ S p hm center base z : ℂ))) -
        (∑' z, ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
          (φ ((fun i => (base i : ℝ)) + physicalAffineSite root z) * (fiber z : ℂ)))‖ ≤
        3 * positiveProjectionAccuracy P

theorem exists_allocated_fixedScale_centered_oneSite_comparison (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ AllocatedFixedScaleCenteredOneSiteStatement m A := by
  obtain ⟨A₀, _, hcompare⟩ := exists_affine_oneSite_density_comparison m
  obtain ⟨b, _, hbnd⟩ := exists_positiveComparisonDataBudget_bound m 0
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    (((Polynomial.X + Polynomial.C b) ^ b + 8 * Polynomial.X + 128 + Polynomial.C A₀) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ hW hWP hτ hτP hξ hξ1 hξP
    N hsize rank hrank hRank T hT widths sample D₀
  let pa := fun (base : X → ℤ) j => translate (fun d => (base d : ℝ)) (p j)
  let hma := fun (base : X → ℤ) j => coefficients_translate_mem (U j) (fun d => (base d : ℝ)) (p j) (hm j)
  have h2P : 0 ≤ 2 * P := mul_nonneg (by norm_num) hP
  have hP2P : P ≤ 2 * P := by linarith
  have hτξ : 0 < ξ * τ := mul_pos hξ hτ
  have hτξP : (ξ * τ)⁻¹ ≤ Real.exp (2 * P) := by
    rw [mul_inv_rev]
    calc
      τ⁻¹ * ξ⁻¹ ≤ Real.exp P * Real.exp P := by gcongr
      _ = Real.exp (2 * P) := by rw [← Real.exp_add]; congr 1; ring
  let Q := positiveComparisonDataBudget m 0 P + spatialSamplingBudget (2 * P)
  have hdata := positiveComparisonDataBudget_bounds m 0 hP
  have hdataQ : positiveComparisonDataBudget m 0 P ≤ Q :=
    le_add_of_nonneg_right (h2P.trans (le_spatialSamplingBudget h2P))
  have hspatialQ : spatialSamplingBudget (2 * P) ≤ Q := le_add_of_nonneg_left hdata.1
  have hPQ : P ≤ Q := hdata.2.1.trans hdataQ
  have hQ : 0 ≤ Q := hP.trans hPQ
  have hExp := Real.exp_le_exp.mpr hPQ
  have hcut : (Q + A₀) ^ A₀ ≤ (P + A) ^ A := by
    have hbase : Q + (A₀ : ℝ) ≤ (P + b) ^ b + 8 * P + 128 + A₀ := by
      have h := hbnd P hP
      dsimp [Q, spatialSamplingBudget]
      linarith
    calc
      _ ≤ ((P + b) ^ b + 8 * P + 128 + A₀) ^ A₀ :=
        pow_le_pow_left₀ (add_nonneg hQ (Nat.cast_nonneg A₀)) hbase A₀
      _ ≤ _ := by simpa [Polynomial.eval₂_pow] using hbudget P hP
  obtain ⟨_, F, inst, frequency, coeff, hfreq, hcoeff, happ⟩ :=
    exists_allocated_positive_fourier_data B U basis hb o S C V hC hV 0
      hR hσ hσ1 Cinv hCinv hchart hsmall hP hmSize hK hRP hσP hcount hI hn hJ hAP hLP hCP hVP
  let _ := inst
  have hN (d) : 0 < N d := by exact_mod_cast (Real.exp_pos _).trans_le (hsize d)
  have hwidths := narrowTrimmedSpatialWidths_pos (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτ hξ N hN
  have hwidthLower (z : Option (LayerSamplerVariables G I n B) × X) :
      spatialWidthFraction (2 * P) (ξ * τ) * (N z.2 : ℝ) ≤ widths z :=
    (spatialWidthFraction_le_allocated_width h2P hW
      (hWP.trans (Real.exp_le_exp.mpr hP2P)) hτξ.le N z).trans
        (narrowTrimmedSpatialWidths_lower hW hτ hξ1 N hN z)
  have hη : 0 < positiveProjectionAccuracy P := Real.exp_pos _
  have hηQ : 1 / positiveProjectionAccuracy P ≤ Real.exp Q := by
    simp only [one_div, positiveProjectionAccuracy, Real.exp_neg, inv_inv]
    exact Real.exp_le_exp.mpr (hdata.2.2.1.trans hdataQ)
  have hspec := allocatedCoefficientDensity_spec B U basis hb o hR hσ S
    hσ1 Cinv hCinv hchart hsmall μ ν
  have hcap := allocatedCoefficientDensity_bounds B U basis hb o hR hσ S C V hC hV
    hσ1 Cinv hCinv hchart hsmall
  have hbound (x) : ‖D₀ x‖ ≤
      (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hcap x).1]
    exact (hcap x).2
  have hlocal (base : X → ℤ) (root : LayerSamplerVariables G I n B → ℤ)
      (hroot : ∀ k, |(root k : ℝ)| ≤ Real.exp P)
      (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
      (φ : (X → ℝ) → ℂ) (hφ : ∀ u, ‖φ u‖ ≤ 1) :
      ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z,
        ‖(∑' z, ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
          (φ ((fun i => (base i : ℝ)) + physicalAffineSite root z) *
            (allocatedCenteredJointDensity B U basis hb o hR hσ S p hm center base z : ℂ))) -
          (∑' z, ((selectedResidueSmoothPMF stride T widths hwidths hZ z).toReal : ℂ) *
            (φ ((fun i => (base i : ℝ)) + physicalAffineSite root z) *
              ((coefficientFiberAverage U μ root
                (fun x => D₀ (coefficientConstantCenter U center + x))
                (coefficientEvaluationTorus U root (sample base z)) : ℝ) : ℂ)))‖ ≤
          3 * positiveProjectionAccuracy P := by
    have hpa (j) : DegreeLE (1 : X → ℕ) (j.val + 1) (pa base j) :=
      degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j)
    have hranka (j) : HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (pa base j) :=
      (hasLayerSamplingRank_translate_iff _ _ _ _ _ _ (hp j)).mpr (hrank j)
    let ψ : (X → ℝ) → ℂ := fun v => φ ((fun i => (base i : ℝ)) + v)
    have hψ (v) : ‖ψ v‖ ≤ 1 := hφ _
    obtain ⟨hZ, he⟩ := hcompare hQ (hX.trans hPQ) (hdim.trans hPQ) U μ
      root (fun i => Fin.elim0 i) (Real.exp_nonneg Q) (Real.exp_nonneg Q) le_rfl le_rfl
      (fun s k => by
        have hs : s = ∅ := Finset.eq_empty_of_isEmpty s
        simpa only [affineSite, hs, Finset.sum_empty, add_zero] using (hroot k).trans hExp)
      frequency (fun t j d hd i => (hfreq t j d hd i).trans (Real.exp_le_exp.mpr hdataQ))
      (fun a => coeff a * coefficientTorusCharacter U (frequency a) (coefficientConstantCenter U center))
      (Real.exp_nonneg Q) le_rfl
      (by rw [coefficientFourier_translate_norm]; exact hcoeff.trans (Real.exp_le_exp.mpr hdataQ))
      (pa base) hpa (hma base) stride hs (Real.exp_nonneg Q) le_rfl
      (spatialWidthFraction_pos (2 * P) hτξ) hη
      ((spatialWidthFraction_inv_le h2P hτξ hτξP).trans (Real.exp_le_exp.mpr hspatialQ)) hηQ
      (fun d => (hsP d).trans hExp) (fun d => (N d : ℝ))
      (fun d => (Real.exp_le_exp.mpr hcut).trans (hsize d)) hranka
      ((Real.exp_le_exp.mpr hcut).trans hRank)
      0 (by simp) (fun _ => ψ) (fun _ v => hψ v) T hT widths hwidths hwidthLower
      (fun x => D₀ (coefficientConstantCenter U center + x))
      (bounded_coefficient_translate_fiber_integrable U μ D₀ hspec.1 hbound _ root)
      hη.le (fun x => by
        rw [norm_sub_rev]
        exact coefficientFourier_translate_approx U D₀ frequency coeff
          happ (coefficientConstantCenter U center) x)
    refine ⟨hZ, ?_⟩
    have hsample (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
        affineSampleCoefficientTorus U (pa base) (hma base) (fun k i => (z (k,i) : ℝ)) =
          sample base z := affineSampleCoefficientTorus_joint_frame U p hm base z
    simp only [layeredSiteWeight_physical, hsample] at he
    exact he.trans_eq (by ring)
  obtain ⟨hZ, _⟩ := hlocal 0 0 (by intro k; simpa using Real.exp_nonneg P) 0
    (fun _ => 0) (fun _ => by simp)
  refine ⟨hwidths, hZ, ?_⟩
  intro base root hroot center φ hφ
  exact (hlocal base root hroot center φ hφ).choose_spec

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def AllocatedFixedScaleJointMarginalStatement (m A : ℕ) : Prop :=
    ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P : ℝ} (_hP : 0 ≤ P) (_hmSize : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hLP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P) (_hτhalf : τ ≤ 1 / 2)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let density := allocatedCenteredJointDensity B U basis hb o hR hσ S p hm
    ∃ (_hN : ∀ i, 0 < N i) (hwidths : ∀ z, 0 < widths z)
      (hmargin : ∀ i, 2 * spatialTrimMargin τ N i < N i)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z)
      (hD : ∀ center, 0 < selectedJointDensityMass bases stride T widths (density center)),
      (∀ center,
        let Z := selectedJointDensityMass bases stride T widths (density center)
        |Z - 1| ≤ Real.exp (-P) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ Z⁻¹ ≤ 2) ∧
      ∀ (root : LayerSamplerVariables G I n B → ℤ),
        (∀ k, |(root k : ℝ)| ≤ Real.exp P) →
        (∑ k, |(root k : ℝ)|) ≤ W →
      ∀ φ : (X → ℝ) → ℂ, (∀ v, ‖φ v‖ ≤ 1) →
        let f := fun center =>
          (selectedJointFiniteLaw bases (trimmedIntegerBox_nonempty N _ hmargin)
            stride T widths hwidths hmass (density center)
            (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S p hm center)
            (hD center)).complexMean
              (fun z => φ ((fun i => (z.1.val i : ℝ)) + physicalAffineSite root z.2.val))
        Integrable f μ ∧
          ‖(∫ center, f center ∂μ) - (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ)))‖ ≤
            12 * positiveProjectionAccuracy P + 2 * (Fintype.card X : ℝ) * τ

theorem exists_allocated_fixedScale_joint_marginal (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ AllocatedFixedScaleJointMarginalStatement m A := by
  obtain ⟨A₁, _, hone⟩ := exists_allocated_fixedScale_centered_oneSite_comparison m
  obtain ⟨A₂, _, hnorm⟩ := exists_allocated_fixed_scale_centered_normalization m
  let A := max (max A₁ A₂) 256
  have hA : 256 ≤ A := le_max_right _ _
  have hA₁A : A₁ ≤ A := (le_max_left _ _).trans (le_max_left _ _)
  have hA₂A : A₂ ≤ A := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨A, by omega, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U basis R σ S hb o _ _ _ _ μ _ _ ν _ _
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall P hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP W τ ξ
    hW hWP hτ hτP hτhalf hξ hξ1 hξP N hsize rank hrank hRank T hT widths bases density
  have hthreshold (a : ℕ) (ha : a ≤ A) :
      Real.exp ((P + a) ^ a) ≤ Real.exp ((P + A) ^ A) := by
    have hAr : (256 : ℝ) ≤ A := by exact_mod_cast hA
    have har : (a : ℝ) ≤ A := by exact_mod_cast ha
    apply Real.exp_le_exp.mpr
    exact (pow_le_pow_left₀ (by positivity) (by linarith only [har] : P + (a : ℝ) ≤ P + A) a).trans
      (pow_le_pow_right₀ (by linarith only [hP, hAr] : (1 : ℝ) ≤ P + A) ha)
  obtain ⟨hwidths, hmass, hone⟩ := hone B U basis S hb o μ ν
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP
    hW hWP hτ hτP hξ hξ1 hξP N
    (fun x => (hthreshold A₁ hA₁A).trans (hsize x)) hrank
    ((hthreshold A₁ hA₁A).trans hRank) T hT
  obtain ⟨_, _, hnorm⟩ := hnorm B U basis S hb o μ ν
    hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hLP hCP hVP p hp hm stride hs hsP
    hW hWP hτ hτP hξ hξ1 hξP N
    (fun x => (hthreshold A₂ hA₂A).trans (hsize x)) hrank
    ((hthreshold A₂ hA₂A).trans hRank) T hT
  have hN (x) : 0 < N x := by exact_mod_cast (Real.exp_pos _).trans_le (hsize x)
  have hmarginSize (x) : 4 ≤ τ * (N x : ℝ) :=
    spatialTrimMargin_size_of_exp_size hP hτ hτP
      ((spatial_threshold_large hP hA).trans (hsize x))
  have hproper := spatialTrimMargin_proper hτhalf N hN hmarginSize
  have hbases : bases.Nonempty := trimmedIntegerBox_nonempty N _ hproper
  have hD (center) : 0 < selectedJointDensityMass bases stride T widths (density center) :=
    ((hnorm center).2 bases hbases).2.2.1
  have hlocal (center) (a) : 0 < selectedResidueDensityMass stride T widths (density center a) :=
    (positiveProjectionAccuracy_normalizer hP ((hnorm center).1 a)).2.2.1
  refine ⟨hN, hwidths, hproper, hmass, hD, ?_, ?_⟩
  · intro center
    have h := (hnorm center).2 bases hbases
    exact ⟨h.1, h.2.1, h.2.2.2⟩
  · intro root hroot hrootSum φ hφ
    have hfit := narrowTrimmedSpatial_site_width hW hτ hξ1 root hrootSum N hN
    have hmeas (a) (z) : Measurable (fun center => density center a z) :=
      allocatedCenteredJointDensity_measurable_center B U basis hb o hR hσ S p hm a z
    have hnonneg (center) (a) (z) : 0 ≤ density center a z :=
      allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S p hm center a z
    have hmix (a : X → ℤ) (ψ : (X → ℝ) → ℂ) (hψ : ∀ v, ‖ψ v‖ ≤ 1) :
        ‖(∫ center, ∑' z, ((selectedResidueDensityPMF stride T widths hwidths hmass (density center a)
            (hnonneg center a) (hlocal center a) z).toReal : ℂ) * ψ (physicalAffineSite root z) ∂μ) -
          ∑' z, ((selectedResidueSmoothPMF stride T widths hwidths hmass z).toReal : ℂ) *
            ψ (physicalAffineSite root z)‖ ≤ 6 * positiveProjectionAccuracy P := by
      exact allocatedFixedScale_center_mixture_compare B U basis hb o hR hσ S μ ν hσ1
        C V hC hV Cinv hCinv hchart hsmall p hm stride T widths hwidths hmass a root
        (fun center => hlocal center a) (fun center => (hnorm center).1 a)
        (fun center φ hφ => hone a root hroot center φ hφ) ψ hψ
    have h := fixedScaleJointMarginalTransfer μ root N (spatialTrimMargin τ N) hproper
      stride T widths hwidths hmass hfit density hmeas hnonneg hD hlocal
      (fun center a => (hnorm center).1 a) hmix φ hφ
    refine ⟨h.1, h.2.trans ?_⟩
    have hboundary := spatialTrimMargin_error_bound N hN hmarginSize
    nlinarith only [hboundary]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexPositiveMasks
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

def complexMaskComponent (b : Bool) (z : ℂ) : ℝ := if b then z.re else z.im

def complexMaskSign (b : Bool) : ℝ := if b then 1 else -1

noncomputable def complexPositiveMask (t : Bool × Bool) (z : ℂ) : ℝ :=
  (1 + complexMaskSign t.2 * complexMaskComponent t.1 z) / 2

def complexMaskCoefficient (t : Bool × Bool) : ℂ :=
  (complexMaskSign t.2 : ℂ) * (if t.1 then 1 else Complex.I)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PositiveGridFamily
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open Filter Topology

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev PositiveGridVertex {j : ℕ} (a : Fin j → ℕ) := ∀ i, Fin (a i)

abbrev PositiveGridShifts {j : ℕ} (a : Fin j → ℕ) (G : Type*) := ∀ i, Fin (a i) → G

def positiveGridVolume {j : ℕ} (a : Fin j → ℕ) : ℕ := ∏ i, a i

noncomputable def positiveGridProduct {j : ℕ} (a : Fin j → ℕ) {G : Type*} [AddCommMonoid G]
    (f : PositiveGridVertex a → G → ℝ) (t : PositiveGridShifts a G) : ℝ :=
  ∏ b, f b (∑ i, t i (b i))

noncomputable def positiveGridMean {j : ℕ} (a : Fin j → ℕ) {G : Type*}
    [AddCommMonoid G] [Fintype G] (f : PositiveGridVertex a → G → ℝ) : ℝ :=
  𝔼 t, positiveGridProduct a f t

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def positiveGridFiber {j : ℕ} (a : Fin (j + 1) → ℕ) {G : Type*} [Add G]
    (f : PositiveGridVertex a → G → ℝ) (t : Fin (a 0) → G) (c : ℝ)
    (b : PositiveGridVertex (fun i => a i.succ)) : G → ℝ :=
  normalizedAxisProduct (fun i => f (Fin.cons i b)) t c

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

open scoped BigOperators

def PositiveGridEstimate (s : ℕ) (epsilon : ℝ) (C : ℕ) : Prop :=
  ∀ {N j : ℕ} [NeZero N] {p L g : ℝ}, 2 ≤ p → 2 ≤ L → 1 ≤ g → g ≤ Real.exp p →
    Odd N → Real.exp ((p + L + 2) ^ C) ≤ N → 1 ≤ j → j ≤ s + 1 →
    ∀ a : Fin j → ℕ, (∀ i, 1 ≤ a i ∧ (a i : ℝ) ≤ p) →
    ∀ f : PositiveGridVertex a → ZMod N → ℝ,
    (∀ b x, 0 ≤ f b x ∧ f b x ≤ Real.exp p) →
    (∀ b, CyclicNiltestUpperComparison.{0} s N ((p + L + 2) ^ C)
      (Real.exp (-((p + L + 2) ^ C))) (f b) (fun _ => g)) →
    positiveGridMean a f ≤ (g * (1 + epsilon) ^ (s + 1)) ^ positiveGridVolume a + Real.exp (-L)

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

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

end Erdos3

end

end OAI

end


