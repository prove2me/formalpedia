-- Prove2me | Definitions.Def_OAIErdos3B129
-- name    : OAIErdos3B129
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T08:00:51.663229+00:00
-- url     : https://prove2.me/theorems/c3a0f8c2-bc83-4d50-a115-7c277f2cde15
-- title:
--   OpenAI Erdős-3 split, definitions bundle 130 of 132
-- statement:
--   Definitions bundle 130 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B128`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 130 available.
--
--   Modules: `OAI.Erdos3.DegreeRankLieFiltration.boundedRankIntegralModel`, `OAI.Erdos3.DegreeRankLieFiltration.boundedRankIntegralModel_coordinates`, `OAI.Erdos3.DegreeRankLieFiltration.boundedRankIntegralStructure`, `OAI.Erdos3.DegreeRankLieFiltration.boundedRankIntegralStructure_complexity`, `OAI.Erdos3.DegreeRankLieFiltration.exists_bounded_rank_integral_model`, `OAI.Erdos3.DegreeRankLieFiltration.exists_bounded_rank_integral_model_with_frequency`, `OAI.Erdos3.FiniteProbabilityWeights.mean_mono_positive_support`, `OAI.Erdos3.MixedReplicatedIndex`, `OAI.Erdos3.MultidegreeLieFiltration.boundedIntegralModel`, `OAI.Erdos3.MultidegreeLieFiltration.boundedIntegralModel_coordinates`, `OAI.Erdos3.MultidegreeLieFiltration.boundedIntegralStructure`, `OAI.Erdos3.MultidegreeLieFiltration.boundedIntegralStructure_complexity`, `OAI.Erdos3.MultidegreeLieFiltration.exists_bounded_integral_model`, `OAI.Erdos3.NativeIntegerVectorEquivalence.exists_mixed_cube_budget`, `OAI.Erdos3.NativeMixedCorrelation.exists_fixed_quadratic_coordinate`, `OAI.Erdos3.NativeMixedCorrelation.exists_fixed_residual_coordinate`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_mixed_cube_translation`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_quadratic_diagonal_niltest`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedCubeWithShift`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedCubeWithShift_diagonal`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedCubeWithShift_unit`, `OAI.Erdos3.NativeMultidegreeNilcharacter.mixedCubeWithShift_zero_eq`, `OAI.Erdos3.NativeVectorCorrelation.mean_correlation_of_degree_zero`, `OAI.Erdos3.NilpotentLieFiltration.exists_frozenMarkedRightOrbit_grid_bound`, `OAI.Erdos3.RankPreparationFamily.PreparedHeights.euclideanLayerTorus_compact`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_nativePresentPivotQuotient_budget`, `OAI.Erdos3.VectorPolynomial.allocatedAffineCoefficientAccuracyLog`, `OAI.Erdos3.VectorPolynomial.allocatedAffineL1Log`, `OAI.Erdos3.VectorPolynomial.allocatedAffineL1Log_nonneg`, `OAI.Erdos3.VectorPolynomial.allocatedAffineLengthLog`, `OAI.Erdos3.VectorPolynomial.allocatedAffineLengthLog_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedAffineReferenceAccuracyLog`, `OAI.Erdos3.VectorPolynomial.allocatedAffineScale`, `OAI.Erdos3.VectorPolynomial.allocatedAffineScalePolynomial`, `OAI.Erdos3.VectorPolynomial.allocatedComparisonDimension_mono`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceBadDepth`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceIntegerPolynomial`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceIntegerSelectedCoefficients`, `OAI.Erdos3.VectorPolynomial.allocatedCongruenceIntegerSelectedCoefficients_reduce`, `OAI.Erdos3.VectorPolynomial.allocatedIdealCoverInputLog`, `OAI.Erdos3.VectorPolynomial.allocatedIdealCoverInputLog_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedIdealCoverPrimitiveLog`, `OAI.Erdos3.VectorPolynomial.allocatedIdealCoverPrimitiveRadius`, `OAI.Erdos3.VectorPolynomial.allocatedIdealCoverPrimitiveRadius_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedIdealCoverPrimitiveRadius_le`, `OAI.Erdos3.VectorPolynomial.allocatedIdealCoverRadius_half_le_physical`, `OAI.Erdos3.VectorPolynomial.allocatedIdealCoverRadius_inverse_from_dimensions`, `OAI.Erdos3.VectorPolynomial.allocatedIntegerBlock_card_le`, `OAI.Erdos3.VectorPolynomial.allocatedNaturalSiteLog`, `OAI.Erdos3.VectorPolynomial.allocatedNaturalSiteRadius_exp_bound`, `OAI.Erdos3.VectorPolynomial.allocatedNaturalSupportLog`, `OAI.Erdos3.VectorPolynomial.allocatedNaturalSupportLog_nonneg`, `OAI.Erdos3.VectorPolynomial.allocatedNaturalSupportRadius_exp_bound`, `OAI.Erdos3.VectorPolynomial.allocatedSiteCoefficientLog`, `OAI.Erdos3.VectorPolynomial.allocatedSiteCoefficientLog_nonneg`, `OAI.Erdos3.VectorPolynomial.allocatedSiteCoefficientRadius_exp_bound`, `OAI.Erdos3.VectorPolynomial.allocatedSourceCoverRadius`, `OAI.Erdos3.VectorPolynomial.allocatedSourceCoverRadiusLog`, `OAI.Erdos3.VectorPolynomial.exists_allocatedAffineL1Log_bound`, `OAI.Erdos3.VectorPolynomial.exists_allocatedAffineScaleLog_bound`, `OAI.Erdos3.VectorPolynomial.preparedNestedEndpointDimensionExponent`, `OAI.Erdos3.affineReferenceCoefficientLog`, `OAI.Erdos3.blockJetScaleBound_four_exp`, `OAI.Erdos3.boxNiltestDetection_succ`, `OAI.Erdos3.conjugationPower_next_self`, `OAI.Erdos3.cubeProduct_comp_addHom`, `OAI.Erdos3.cubeProduct_swap_head`, `OAI.Erdos3.exists_boxNiltestDetection`, `OAI.Erdos3.exists_finite_site_niltest_detection`, `OAI.Erdos3.exists_nested_box_niltest_detection`, `OAI.Erdos3.exists_polynomial_box_detection`, `OAI.Erdos3.exists_sampled_niltest_cube_detection_with_sides`, `OAI.Erdos3.mem_mixedRepeatedCoordinates`, `OAI.Erdos3.mixedCubeInput`, `OAI.Erdos3.mixedCubeInputHom`, `OAI.Erdos3.mixedCubeObservable`, `OAI.Erdos3.mixedCubeObservable_norm_le_one`, `OAI.Erdos3.mixedCubeObservable_unit`, `OAI.Erdos3.mixedHead`, `OAI.Erdos3.mixedRepeatedCoordinates`, `OAI.Erdos3.mixedRepeatedCoordinates_get`, `OAI.Erdos3.mixedRepeatedCoordinates_length`, `OAI.Erdos3.mixedRepeatedCoordinates_nodup`, `OAI.Erdos3.mixedReplica`, `OAI.Erdos3.mixedReplica_injective`, `OAI.Erdos3.mixedReplicatedInput`, `OAI.Erdos3.mixedReplicatedInput_diagonal`, `OAI.Erdos3.mixedReplicatedInput_head`, `OAI.Erdos3.mixedReplicatedInput_replica`, `OAI.Erdos3.mixedReplicated_cases`, `OAI.Erdos3.norm_expect_conjugationPower`, `OAI.Erdos3.sampledSupportedSlicedDetectionConstant`, `OAI.Erdos3.selectedJointFiniteLaw_normalized_norm_le`, `OAI.Erdos3.selectedJointFiniteLaw_spatial_cutoff_bound`, `OAI.Erdos3.selectedJointFiniteLaw_support`, `OAI.Erdos3.selectedJointFiniteLaw_weighted_reference_comparison`, `OAI.Erdos3.selectedJointFiniteLaw_weighted_reference_real_comparison`, `OAI.Erdos3.selectedResidueFiniteLaw_cutoff_le_event`, `OAI.Erdos3.selectedResidueFiniteLaw_event_eq_map_true`, `OAI.Erdos3.selectedResidueFiniteLaw_normalized_norm_le`, `OAI.Erdos3.selectedResidueSmoothWeight_normalized_norm_le`, `_private.Dynamics.PreparedNestedEndpointDimensionBudget.0.OAI.Erdos3.VectorPolynomial.exists_endpointDimension_local_budget`, `_private.Dynamics.PreparedNestedEndpointDimensionBudget.0.OAI.Erdos3.VectorPolynomial.exists_endpointDimension_uniform_budget`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B123
import Definitions.Def_OAIErdos3B126

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CyclicNiltestDetection
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem boxNiltestDetection_succ.{u,v} {s c : ℕ}
    (hI : BoxNiltestDetection.{u,v} s (fun p => (p + c) ^ c)) :
    ∃ C : ℕ, 2 ≤ C ∧ BoxNiltestDetection.{u,v} (s + 1) (fun p => (p + C) ^ C) := by
  classical
  obtain ⟨av, _, hav⟩ := exists_verticalDecompositionBudget_bound
  obtain ⟨bs, _, hder⟩ := exists_vertical_derivative_detection s
  obtain ⟨C, hC, hbudget⟩ := exists_boxDetectionStepBudget_bound s av bs c
  refine ⟨C, hC, ?_⟩
  intro σ _ _ L _ _ d _ _ _ _ D p hp hσ w hw T hT z lengths _ f hf hc
  let Q := translatedIntegerBox z lengths
  have hQ : Q.Nonempty := translatedIntegerBox_nonempty lengths z
  obtain ⟨η, U, hU, hcorrU, hchar⟩ :=
    T.exists_detection_vertical_mode av hav hp hT hQ f hf hc
  let r := boxModeBudget av p
  let q := boxInductionInputBudget av bs p
  let ℓ := boxRetainedBudget av p
  let ρ := Real.exp (-r)
  let δ := Real.exp (-(ℓ + p))
  let η0 := Real.exp (-((q + c) ^ c))
  let μ := Real.exp (-ℓ)
  let P := fun h : σ → ℤ =>
    ρ ^ 2 / 2 ≤ ‖finiteCorrelation (derivativeSupport Q h)
      (multiplicativeDerivative f h) (multiplicativeDerivative U.eval h)‖ ∧
    δ * Q.card < ((derivativeSupport Q h).card : ℝ)
  have hcost := boxInductionInputBudget_bounds av bs hp
  have hq : 0 ≤ q := hp.trans hcost.2.2
  have hρsq : Real.exp (-q) ≤ ρ ^ 2 / 2 := by
    have hq' : 2 * r + 1 ≤ q := hcost.2.1
    have he : ρ ^ 2 = Real.exp (-2 * r) := by
      dsimp [ρ]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [he]
    exact (Real.exp_le_exp.mpr (by linarith : -q ≤ -2 * r - 1)).trans
      (exp_sub_one_le_half_exp (-2 * r))
  have hweight := weight_correlating_large_box_overlaps z lengths f U.eval
    (ρ := ρ) (B := Real.exp (p + 1)) (δ := δ)
    (Real.exp_nonneg _) (Real.exp_pos _) (Real.exp_nonneg _) hf
    (fun x _ => U.eval_budget hU x) hcorrU
  have hμ : μ ≤ ∑ h ∈ cubeDifferenceSupport Q,
      (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) * (if P h then (1 : ℝ) else 0) :=
    (retained_exponential_weight (Fintype.card σ) (r := r) hσ).trans hweight
  have hretained (h : σ → ℤ) (hh : h ∈ cubeDifferenceSupport Q) (hP : P h) :
      δ * Q.card ≤ ((derivativeSupport Q h).card : ℝ) ∧
      η0 ≤ finiteSupportGowersNorm (s + 1) (derivativeSupport Q h) (multiplicativeDerivative f h) := by
    refine ⟨hP.2.le, ?_⟩
    let lens := fun i => ((lengths i : ℤ) - |h i|).toNat
    let origin := fun i => z i + max 0 (-h i)
    let : ∀ i, NeZero (lens i) := fun i => ⟨(box_overlap_length_pos z lengths hh i).ne'⟩
    have hR : derivativeSupport Q h = translatedIntegerBox origin lens :=
      derivativeSupport_translatedIntegerBox z lengths h
    have hunit : ∀ x ∈ translatedIntegerBox origin lens, ‖multiplicativeDerivative f h x‖ ≤ 1 := by
      rw [← hR]
      intro x hx
      obtain ⟨hx, hxh⟩ := Finset.mem_filter.mp hx
      simpa only [multiplicativeDerivative, norm_mul, norm_star, one_mul] using
        mul_le_mul (hf x hx) (hf (x + h) hxh) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have hcorr : Real.exp (-q) ≤ ‖finiteCorrelation (translatedIntegerBox origin lens)
        (multiplicativeDerivative f h) (multiplicativeDerivative U.eval h)‖ := by
      rw [← hR]
      exact hρsq.trans hP.1
    have hd := hder c hI D (p + 1) q (by linarith) hq (hσ.trans hcost.2.2) hcost.1
      w hw U hU (fun g => ((realifyFunctional η g.coord : ℝ) : CircleFourier.Circle)) hchar
      h origin lens (multiplicativeDerivative f h) hunit hcorr
    rwa [← hR] at hd
  have hgowers := box_gowers_lower_bound_of_overlaps z lengths s f P
    (Real.exp_nonneg _) (Real.exp_nonneg _) hμ hretained
  have hpow : Real.exp (-boxDetectionStepBudget s av bs c p) ≤
      finiteSupportGowersNorm (s + 2) Q f ^ (2 ^ (s + 2)) :=
    (box_detection_exponential_product s av bs c (Fintype.card σ) hσ).trans hgowers
  have hnorm : 0 ≤ finiteSupportGowersNorm (s + 2) Q f := by
    rw [finiteSupportGowersNorm_eq_restricted (translatedIntegerBox_reflectsPairSums lengths z)]
    exact restrictedGowersNorm_nonneg (s + 1) _ _
  exact (Real.exp_le_exp.mpr (neg_le_neg (hbudget p hp))).trans
    (exp_neg_le_of_pow hnorm (boxDetectionStepBudget_nonneg s av bs c hp)
      (pow_ne_zero _ (by norm_num)) hpow)

theorem exists_boxNiltestDetection.{u,v} (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ BoxNiltestDetection.{u,v} s (fun p => (p + C) ^ C) := by
  induction s with
  | zero =>
    refine ⟨2, le_rfl, ?_⟩
    intro σ _ _ L _ _ d _ _ _ _ D p hp hσ w hw T hT z lengths _ f hf hc
    have hb : 2 * p ≤ (p + (2 : ℕ)) ^ 2 := by
      norm_num only [Nat.cast_ofNat]
      nlinarith [sq_nonneg p]
    exact (Real.exp_le_exp.mpr (neg_le_neg hb)).trans
      (boxNiltestDetection_zero D p hp hσ w hw T hT z lengths f hf hc)
  | succ s ih =>
    obtain ⟨c, _, hc⟩ := ih
    exact boxNiltestDetection_succ hc

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedReplicatedCoordinates
namespace OAI

section

namespace Erdos3

abbrev MixedReplicatedIndex (s : ℕ) := ReplicatedIndex (mixedCorrelationDegree s)

def mixedHead (s : ℕ) : MixedReplicatedIndex s := ⟨0, ⟨0, by change 0 < 1; omega⟩⟩

def mixedReplica {s : ℕ} (j : Fin s) : MixedReplicatedIndex s := ⟨1, ⟨j.val, j.isLt⟩⟩

theorem mixedReplica_injective (s : ℕ) : Function.Injective (mixedReplica (s := s)) := by
  intro i j h
  exact Fin.ext (congrArg (fun a : MixedReplicatedIndex s => a.2.val) h)

theorem mixedReplicated_cases {s : ℕ} (j : MixedReplicatedIndex s) :
    j = mixedHead s ∨ ∃ i : Fin s, j = mixedReplica i := by
  rcases j with ⟨b, j⟩
  fin_cases b
  · left
    change Fin 1 at j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl
  · exact Or.inr ⟨⟨j.val, j.isLt⟩, rfl⟩

def mixedRepeatedCoordinates (s : ℕ) : List (MixedReplicatedIndex s) :=
  List.ofFn (mixedReplica (s := s))

theorem mixedRepeatedCoordinates_length (s : ℕ) : (mixedRepeatedCoordinates s).length = s := by
  simp only [mixedRepeatedCoordinates, List.length_ofFn]

theorem mixedRepeatedCoordinates_nodup (s : ℕ) : (mixedRepeatedCoordinates s).Nodup :=
  List.nodup_ofFn.mpr (mixedReplica_injective s)

theorem mixedRepeatedCoordinates_get (s : ℕ) (j : Fin (mixedRepeatedCoordinates s).length) :
    (mixedRepeatedCoordinates s).get j = mixedReplica (Fin.cast (mixedRepeatedCoordinates_length s) j) := by
  exact List.get_ofFn (mixedReplica (s := s)) j

theorem mem_mixedRepeatedCoordinates (s : ℕ) (j : MixedReplicatedIndex s) :
    j ∈ mixedRepeatedCoordinates s ↔ j.1 = 1 := by
  change j ∈ List.ofFn (mixedReplica (s := s)) ↔ j.1 = 1
  constructor
  · intro h
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
    rfl
  · intro h
    rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
    · norm_num [mixedHead] at h
    · exact List.mem_ofFn.mpr ⟨i, rfl⟩

def mixedReplicatedInput {s : ℕ} {α : Type*} (h : α) (v : Fin s → α)
    (j : MixedReplicatedIndex s) : α :=
  if hj : j.1 = 1 then v ⟨j.2.val, by
    have hs : mixedCorrelationDegree s j.1 = s := by rw [hj]; rfl
    simpa only [hs] using j.2.isLt⟩
  else h

theorem mixedReplicatedInput_head {s : ℕ} {α : Type*} (h : α) (v : Fin s → α) :
    mixedReplicatedInput h v (mixedHead s) = h := rfl

theorem mixedReplicatedInput_replica {s : ℕ} {α : Type*} (h : α) (v : Fin s → α) (j : Fin s) :
    mixedReplicatedInput h v (mixedReplica j) = v j := rfl

theorem mixedReplicatedInput_diagonal {s : ℕ} {α : Type*} (h n : α) :
    mixedReplicatedInput h (fun _ : Fin s => n) =
      fun j : MixedReplicatedIndex s => correlationInput h n j.1 := by
  funext j
  rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
  · rfl
  · rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubeSignalAlgebra
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def mixedCubeInput {d : ℕ} (ω : Fin d → Bool) (x : Fin (d + 2) → ℤ) : Fin 2 → ℤ :=
  correlationInput (x 0) (x 1 + cubeShift (fun j => x j.succ.succ) ω)

namespace NativeMultidegreeNilcharacter

noncomputable def mixedCubeWithShift {s d : ℕ} {p : ℝ}
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
    (c : (Fin d → Bool) → ℤ) (a : (Fin d → Bool) → Fin M.outputDim)
    (x : Fin (d + 2) → ℤ) : ℂ :=
  ∏ ω, conjugationPower (booleanWeight ω)
    (M.eval (a ω) (mixedCubeInput ω x + ![0, c ω]))

theorem mixedCubeWithShift_unit {s d : ℕ} {p : ℝ}
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
    (c : (Fin d → Bool) → ℤ) (x : Fin (d + 2) → ℤ) :
    ∑ a, ‖M.mixedCubeWithShift c a x‖ ^ 2 = 1 := by
  simp only [mixedCubeWithShift, norm_prod, ← Finset.prod_pow, conjugationPower_norm]
  rw [← Fintype.prod_sum (fun ω (i : Fin M.outputDim) =>
    ‖M.eval i (mixedCubeInput ω x + ![0, c ω])‖ ^ 2)]
  simp only [M.unit_eval, Finset.prod_const_one]

theorem mixedCubeWithShift_diagonal {s d : ℕ} {p : ℝ}
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
    (c : (Fin d → Bool) → ℤ) (i : Fin M.outputDim) (h n : ℤ) (k : Fin d → ℤ) :
    M.mixedCubeWithShift c (fun _ => i) (Fin.cons h (Fin.cons n k)) =
      integerCubeProductWithShift (fun z => M.eval i (correlationInput h z)) k c n := by
  have hinput (ω : Fin d → Bool) :
      mixedCubeInput ω (Fin.cons h (Fin.cons n k)) + ![0, c ω] =
        correlationInput h (n + cubeShift k ω + c ω) := by
    funext j
    fin_cases j <;> simp [mixedCubeInput, correlationInput, cubeShift]
    rfl
  simp only [mixedCubeWithShift, integerCubeProductWithShift, hinput]

theorem exists_mixed_cube_translation (s d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
      (c : (Fin d → Bool) → ℤ),
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (M.mixedCubeWithShift c) (M.mixedCubeWithShift 0) := by
  obtain ⟨A, _, htranslate⟩ := exists_multidegree_integer_translation s
  obtain ⟨B, _, hprod⟩ := NativeIntegerVectorEquivalence.exists_finite_product_budget (Fin d → Bool)
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C A) ^ A
  let U := X + P
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((U + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p M c
  have hp : 0 ≤ p := (Nat.cast_nonneg M.dim).trans M.complexity.1.1
  let q := (p + A) ^ A
  let u := p + q
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hu : 0 ≤ u := add_nonneg hp hq
  have hpu : p ≤ u := le_add_of_nonneg_right hq
  have hqu : q ≤ u := le_add_of_nonneg_left hp
  have hcost : (u + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, P, U, q, u, Polynomial.eval₂_pow] using hbudget p hp
  have hdegree : (∑ i, mixedCorrelationDegree s i) = s + 1 := by
    rw [Fin.sum_univ_two]
    change 1 + s = s + 1
    omega
  let F (ω : Fin d → Bool) : Fin 2 → ((Fin (d + 2) → ℤ) →+ ℤ) := fun i =>
    { toFun := fun x => mixedCubeInput ω x i
      map_zero' := by
        fin_cases i <;> simp [mixedCubeInput, correlationInput, cubeShift]
        rfl
      map_add' := by
        intro x y
        fin_cases i
        · rfl
        · change x 1 + y 1 + cubeShift (fun j => x j.succ.succ + y j.succ.succ) ω =
            (x 1 + cubeShift (fun j => x j.succ.succ) ω) +
              (y 1 + cubeShift (fun j => y j.succ.succ) ω)
          have hs : cubeShift (fun j => x j.succ.succ + y j.succ.succ) ω =
              cubeShift (fun j => x j.succ.succ) ω + cubeShift (fun j => y j.succ.succ) ω := by
            simp only [cubeShift, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j _
            split_ifs <;> simp
          rw [hs]
          ring }
  have hzero : (![0, 0] : Fin 2 → ℤ) = 0 := by ext i; fin_cases i <;> rfl
  have E (ω : Fin d → Bool) : NativeIntegerVectorEquivalence s u
      (fun i x => M.eval i (mixedCubeInput ω x + ![0, c ω]))
      (fun i x => M.eval i (mixedCubeInput ω x + ![0, 0])) := by
    have T := ((htranslate (mixedCorrelationDegree s) hdegree M ![0, c ω] 0).linearPullbackHom (F ω)).mono hqu
    change NativeIntegerVectorEquivalence s u
      (fun i x => M.eval i (mixedCubeInput ω x + ![0, c ω]))
      (fun i x => M.eval i (mixedCubeInput ω x + 0)) at T
    simpa only [hzero] using T
  have hdim : (Fintype.card (Fin M.outputDim) : ℝ) ≤ Real.exp u := by
    simpa only [Fintype.card_fin] using M.output_bound.trans (Real.exp_le_exp.mpr hpu)
  exact (hprod _ _ hu hdim hdim (fun ω => (E ω).conjugationPower (booleanWeight ω))).mono hcost

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def mixedCubeInputHom {d : ℕ} (ω : Fin d → Bool) : Fin 2 → ((Fin (d + 2) → ℤ) →+ ℤ) :=
  fun i =>
    { toFun := fun x => mixedCubeInput ω x i
      map_zero' := by
        fin_cases i <;> simp [mixedCubeInput, correlationInput, cubeShift]
        rfl
      map_add' := by
        intro x y
        fin_cases i
        · rfl
        · change x 1 + y 1 + cubeShift (fun j => x j.succ.succ + y j.succ.succ) ω =
            (x 1 + cubeShift (fun j => x j.succ.succ) ω) +
              (y 1 + cubeShift (fun j => y j.succ.succ) ω)
          have hs : cubeShift (fun j => x j.succ.succ + y j.succ.succ) ω =
              cubeShift (fun j => x j.succ.succ) ω + cubeShift (fun j => y j.succ.succ) ω := by
            simp only [cubeShift, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j _
            split_ifs <;> simp
          rw [hs]
          ring }

def mixedCubeObservable {J : Type*} {d : ℕ} (f : J → (Fin 2 → ℤ) → ℂ)
    (a : (Fin d → Bool) → J) (x : Fin (d + 2) → ℤ) : ℂ :=
  ∏ ω, conjugationPower (booleanWeight ω) (f (a ω) (mixedCubeInput ω x))

theorem mixedCubeObservable_unit {J : Type*} [Fintype J] {d : ℕ}
    (f : J → (Fin 2 → ℤ) → ℂ) (hf : ∀ y, ∑ j, ‖f j y‖ ^ 2 = 1)
    (x : Fin (d + 2) → ℤ) : ∑ a, ‖mixedCubeObservable f a x‖ ^ 2 = 1 := by
  simp only [mixedCubeObservable, norm_prod, ← Finset.prod_pow, conjugationPower_norm]
  rw [← Fintype.prod_sum (fun ω (j : J) => ‖f j (mixedCubeInput ω x)‖ ^ 2)]
  simp only [hf, Finset.prod_const_one]

theorem NativeMultidegreeNilcharacter.mixedCubeWithShift_zero_eq {s d : ℕ} {p : ℝ}
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p) :
    M.mixedCubeWithShift (d := d) 0 = mixedCubeObservable M.eval := by
  funext a x
  have hzero : (![0, 0] : Fin 2 → ℤ) = 0 := by ext i; fin_cases i <;> rfl
  simp only [NativeMultidegreeNilcharacter.mixedCubeWithShift, mixedCubeObservable,
    Pi.zero_apply, hzero, add_zero]

theorem NativeIntegerVectorEquivalence.exists_mixed_cube_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I J : Type*} [Fintype I] [Fintype J] {s : ℕ} {p : ℝ}
      {f : I → (Fin 2 → ℤ) → ℂ} {g : J → (Fin 2 → ℤ) → ℂ},
      0 ≤ p → NativeIntegerVectorEquivalence s p f g →
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (mixedCubeObservable (d := d) f) (mixedCubeObservable (d := d) g) := by
  obtain ⟨C, hC, hprod⟩ := NativeIntegerVectorEquivalence.exists_finite_product_budget (Fin d → Bool)
  refine ⟨C, hC, ?_⟩
  intro I J _ _ s p f g hp E
  have H (ω : Fin d → Bool) : NativeIntegerVectorEquivalence s p
      (fun i x => f i (mixedCubeInput ω x)) (fun j x => g j (mixedCubeInput ω x)) :=
    E.linearPullbackHom (mixedCubeInputHom ω)
  exact hprod _ _ hp E.left_dimension E.right_dimension
    (fun ω => (H ω).conjugationPower (booleanWeight ω))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mixedCubeObservable_norm_le_one {J : Type*} {d : ℕ}
    (f : J → (Fin 2 → ℤ) → ℂ) (hf : ∀ j x, ‖f j x‖ ≤ 1)
    (a : (Fin d → Bool) → J) (x : Fin (d + 2) → ℤ) : ‖mixedCubeObservable f a x‖ ≤ 1 := by
  unfold mixedCubeObservable
  rw [norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro ω _
  rw [conjugationPower_norm]
  exact hf _ _

theorem conjugationPower_next_self (n : ℕ) (z : ℂ) :
    conjugationPower (n + 1) (conjugationPower n z) = star z := by
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hn with hn | hn <;> simp [conjugationPower_eq_if_mod, Nat.add_mod, hn]

theorem norm_expect_conjugationPower {X : Type*} (S : Finset X) (n : ℕ) (f : X → ℂ) :
    ‖𝔼 x ∈ S, conjugationPower n (f x)‖ = ‖𝔼 x ∈ S, f x‖ := by
  by_cases hn : n % 2 = 0
  · simp only [conjugationPower_eq_if_mod, hn, ite_true]
  · simp only [conjugationPower_eq_if_mod, hn, ite_false]
    have hs : (𝔼 x ∈ S, star (f x)) = star (𝔼 x ∈ S, f x) := by
      simp [Finset.expect_eq_sum_div_card]
    rw [hs, norm_star]

theorem cubeProduct_swap_head {G : Type*} [AddCommGroup G]
    (f : G → ℂ) (h k : G) (hs : List G) (x : G) :
    cubeProduct f (h :: k :: hs) x = cubeProduct f (k :: h :: hs) x := by
  simp only [cubeProduct_cons_eq_derivative, multiplicativeDerivative_comm f h k]

theorem cubeProduct_comp_addHom {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (φ : G →+ H) (f : H → ℂ) (hs : List G) (x : G) :
    cubeProduct (fun y => f (φ y)) hs x = cubeProduct f (hs.map φ) (φ x) := by
  induction hs generalizing x with
  | nil => simp only [cubeProduct_nil, List.map_nil]
  | cons h hs ih => simp only [List.map_cons, cubeProduct_cons, ih, map_add]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BoundedRankIntegralModel
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (e : Basis (Fin d) ℚ L)
  (b : ∀ i : Fin (s + 1), Basis (Fin (finrank ℚ (F.associatedDegree.layer (i.val + 1))))
    ℚ (F.associatedDegree.layer (i.val + 1)))
  (c : ∀ i j : Fin (s + 1), Basis (Fin (finrank ℚ (F.layer i.val j.val)))
    ℚ (F.layer i.val j.val))
  (B : ℕ) (hB : 0 < B)
  (hstable : ∀ x ∈ coordinateGridModule e B, ∀ y ∈ coordinateGridModule e B,
    lieBCH s x y ∈ coordinateGridModule e B)

noncomputable def boundedRankIntegralModel : RationalFilteredNilmanifold L s d where
  filtration := F.associatedDegree
  basis := e
  layerBasis := b
  lattice := coordinateGridBCHSubgroup e B F.associatedDegree.lowerCentralSeries_eq_bot hstable
  grid := B
  grid_pos := hB
  inner_grid := by rw [coordinateGridBCHSubgroup_coordinates]
  outer_grid := by
    rw [coordinateGridBCHSubgroup_coordinates]
    exact scaledIntegerGrid_le_denominatorGrid B B

noncomputable def boundedRankIntegralStructure :
    (F.boundedRankIntegralModel e b B hB hstable).DegreeRankStructure r where
  filtration := F
  associated := rfl
  basis := c

theorem boundedRankIntegralModel_coordinates :
    bchSubgroupCoordinates (F.boundedRankIntegralModel e b B hB hstable).basis
      (F.boundedRankIntegralModel e b B hB hstable).lattice = scaledIntegerGrid B :=
  coordinateGridBCHSubgroup_coordinates e B F.associatedDegree.lowerCentralSeries_eq_bot hstable

theorem boundedRankIntegralStructure_complexity {H : ℕ}
    (hb : ∀ i a j, RationalHeightLE (e.repr (b i a).val j) H)
    (hc : ∀ i j a k, RationalHeightLE (e.repr (c i j a).val k) H)
    (hbracket : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    {p : ℝ} (hd : (d : ℝ) ≤ p) (hgrid : (B : ℝ) ≤ Real.exp p)
    (hheight : (H : ℝ) ≤ Real.exp p) :
    (F.boundedRankIntegralStructure e b c B hB hstable).ComplexityLE p :=
  ⟨⟨hd, hgrid, fun i j k => rationalLogHeight_le_of_height (hbracket i j k) hheight,
    fun i a j => rationalLogHeight_le_of_height (hb i a j) hheight⟩,
    fun i j a k => rationalLogHeight_le_of_height (hc i j a k) hheight⟩

omit B hB hstable in
theorem exists_bounded_rank_integral_model {H : ℕ}
    (hb : ∀ i a j, RationalHeightLE (e.repr (b i a).val j) H)
    (hc : ∀ i j a k, RationalHeightLE (e.repr (c i j a).val k) H)
    (hbracket : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (l : ℕ) (hl : 0 < l) :
    ∃ B : ℕ, 0 < B ∧ l ∣ B ∧ B ≤ bchIntegralDenominatorBound s * H ^ (d ^ 3) * l ∧
      ∃ D : RationalFilteredNilmanifold L s d, ∃ T : D.DegreeRankStructure r,
        T.filtration = F ∧ D.basis = e ∧ D.grid = B ∧
        bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid B ∧
        ∀ p : ℝ, (d : ℝ) ≤ p → (B : ℝ) ≤ Real.exp p → (H : ℝ) ≤ Real.exp p → T.ComplexityLE p := by
  obtain ⟨B, hB, hdiv, hbound, hstable⟩ :=
    exists_bch_stable_integral_grid e F.associatedDegree.lowerCentralSeries_eq_bot l hl hbracket
  exact ⟨B, hB, hdiv, by simpa only [Fintype.card_fin] using hbound,
    F.boundedRankIntegralModel e b B hB hstable,
    F.boundedRankIntegralStructure e b c B hB hstable, rfl, rfl, rfl,
    F.boundedRankIntegralModel_coordinates e b B hB hstable,
    fun _ hd hg hh => F.boundedRankIntegralStructure_complexity e b c B hB hstable
      hb hc hbracket hd hg hh⟩

omit B hB hstable in
theorem exists_bounded_rank_integral_model_with_frequency {H : ℕ}
    (hb : ∀ i a j, RationalHeightLE (e.repr (b i a).val j) H)
    (hc : ∀ i j a k, RationalHeightLE (e.repr (c i j a).val k) H)
    (hbracket : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (ξ : L →ₗ[ℚ] ℚ) (hξ : ∀ i, RationalHeightLE (ξ (e i)) H)
    (l : ℕ) (hl : 0 < l) :
    ∃ B : ℕ, 0 < B ∧ l ∣ B ∧
      B ≤ bchIntegralDenominatorBound s * H ^ (d ^ 3) * (l * H ^ d) ∧
      ∃ D : RationalFilteredNilmanifold L s d, ∃ T : D.DegreeRankStructure r,
        T.filtration = F ∧ D.basis = e ∧ D.grid = B ∧
        bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid B ∧
        (∀ z : D.filtration.Group, z ∈ D.lattice → ∃ n : ℤ, ξ z.coord = n) ∧
        ∀ p : ℝ, (d : ℝ) ≤ p → (B : ℝ) ≤ Real.exp p → (H : ℝ) ≤ Real.exp p → T.ComplexityLE p := by
  classical
  let k := arrayDenominator (fun i => ξ (e i))
  have hk : 0 < k := arrayDenominator_pos _
  have hkH : k ≤ H ^ d := by
    simpa only [Fintype.card_fin] using arrayDenominator_le (fun i => ξ (e i)) (fun i => (hξ i).2)
  obtain ⟨B, hB, hdiv, hbound, D, T, hTF, hDe, hDB, hcoords, hcomplex⟩ :=
    F.exists_bounded_rank_integral_model e b c hb hc hbracket (l * k) (Nat.mul_pos hl hk)
  refine ⟨B, hB, (dvd_mul_right l k).trans hdiv,
    hbound.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left l hkH)),
    D, T, hTF, hDe, hDB, hcoords, ?_, hcomplex⟩
  intro z hz
  have hgrid : D.basis.equivFun z.coord ∈ scaledIntegerGrid B := by
    rw [← hcoords]
    change (⟨D.basis.equivFun.symm (D.basis.equivFun z.coord)⟩ : D.filtration.Group) ∈ D.lattice
    simpa only [LinearEquiv.symm_apply_apply] using hz
  rw [hDe] at hgrid
  exact coordinateGrid_functional_integral e ξ k B ((dvd_mul_left k l).trans hdiv)
    (fun i => ⟨clearedArray (fun j => ξ (e j)) i, (clearedArray_cast _ i).symm⟩) hgrid

end Erdos3.DegreeRankLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MultidegreeIntegralModel
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
  (e : Basis (Fin d) ℚ L)
  (b : ∀ a, Basis (Fin (finrank ℚ (F.layer a))) ℚ (F.layer a))
  {H : ℕ} (hb : ∀ a i j, RationalHeightLE (e.repr ((b a) i).val j) H)
  (B : ℕ) (hB : 0 < B)
  (hstable : ∀ x ∈ coordinateGridModule e B, ∀ y ∈ coordinateGridModule e B,
    lieBCH s x y ∈ coordinateGridModule e B)

noncomputable def boundedIntegralModel : RationalFilteredNilmanifold L s d where
  filtration := F.ordinary
  basis := e
  layerBasis i := (F.exists_bounded_ordinaryLayer_basis b e hb (i.val + 1)).choose
  lattice := coordinateGridBCHSubgroup e B F.ordinary.lowerCentralSeries_eq_bot hstable
  grid := B
  grid_pos := hB
  inner_grid := by rw [coordinateGridBCHSubgroup_coordinates]
  outer_grid := by
    rw [coordinateGridBCHSubgroup_coordinates]
    exact scaledIntegerGrid_le_denominatorGrid B B

noncomputable def boundedIntegralStructure :
    (F.boundedIntegralModel e b hb B hB hstable).MultidegreeStructure bound where
  filtration := F
  ordinary := rfl
  basis a := b (fun i => (a i).val)

theorem boundedIntegralModel_coordinates :
    bchSubgroupCoordinates (F.boundedIntegralModel e b hb B hB hstable).basis
      (F.boundedIntegralModel e b hb B hB hstable).lattice = scaledIntegerGrid B :=
  coordinateGridBCHSubgroup_coordinates e B F.ordinary.lowerCentralSeries_eq_bot hstable

theorem boundedIntegralStructure_complexity {p : ℝ} (hd : (d : ℝ) ≤ p)
    (hgrid : (B : ℝ) ≤ Real.exp p) (hheight : (H : ℝ) ≤ Real.exp p)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) :
    (F.boundedIntegralStructure e b hb B hB hstable).ComplexityLE p := by
  refine ⟨⟨hd, hgrid, ?_, ?_⟩, ?_⟩
  · exact fun i j k => rationalLogHeight_le_of_height (hc i j k) hheight
  · intro i j k
    exact rationalLogHeight_le_of_height
      ((F.exists_bounded_ordinaryLayer_basis b e hb (i.val + 1)).choose_spec j k) hheight
  · intro a i j
    exact rationalLogHeight_le_of_height (hb (fun k => (a k).val) i j) hheight

omit B hB hstable in
include b hb in
theorem exists_bounded_integral_model
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (l : ℕ) (hl : 0 < l) :
    ∃ B : ℕ, 0 < B ∧ l ∣ B ∧ B ≤ bchIntegralDenominatorBound s * H ^ (d ^ 3) * l ∧
      ∃ D : RationalFilteredNilmanifold L s d, ∃ M : D.MultidegreeStructure bound,
        M.filtration = F ∧ D.basis = e ∧ D.grid = B ∧
        bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid B ∧
        ∀ p : ℝ, (d : ℝ) ≤ p → (B : ℝ) ≤ Real.exp p → (H : ℝ) ≤ Real.exp p → M.ComplexityLE p := by
  obtain ⟨B, hB, hdiv, hbound, hstable⟩ :=
    exists_bch_stable_integral_grid e F.ordinary.lowerCentralSeries_eq_bot l hl hc
  refine ⟨B, hB, hdiv, ?_, F.boundedIntegralModel e b hb B hB hstable,
    F.boundedIntegralStructure e b hb B hB hstable, rfl, rfl, rfl,
    F.boundedIntegralModel_coordinates e b hb B hB hstable, ?_⟩
  · simpa only [Fintype.card_fin] using hbound
  · intro p hd hgrid hheight
    exact F.boundedIntegralStructure_complexity e b hb B hB hstable hd hgrid hheight hc

end Erdos3.MultidegreeLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeZeroDegreeCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeVectorCorrelation

attribute [local instance] lie algebra topology topologicalAdd continuousSMul hausdorff

theorem mean_correlation_of_degree_zero {I : Type*} {N : ℕ} [NeZero N] {p : ℝ}
    {f : I → ZMod N → ℂ} (W : NativeVectorCorrelation 0 N p f) :
    Real.exp (-(2 * p)) ≤ ‖𝔼 x, f W.coordinate x‖ := by
  let c := W.test.observable (QuotientGroup.mk (1 : W.model.RealGroup))
  have hnorm : ‖c‖ ≤ Real.exp p := by
    have h := W.test.eval_budget W.complexity (0 : Unit → ℤ)
    rwa [RationalFilteredNilmanifold.Niltest.eval_step_zero] at h
  have heq : (𝔼 x, f W.coordinate x * star (W.test.evalCyclic N (fun _ => x))) =
      (𝔼 x, f W.coordinate x) * star c := by
    simp only [RationalFilteredNilmanifold.Niltest.evalCyclic,
      RationalFilteredNilmanifold.Niltest.eval_step_zero, ← Finset.expect_mul]
    rfl
  have h := W.correlation
  rw [heq, norm_mul, norm_star] at h
  have hbound : Real.exp (-(2 * p)) * Real.exp p ≤ ‖𝔼 x, f W.coordinate x‖ * Real.exp p := by
    rw [← Real.exp_add, show -(2 * p) + p = -p by ring]
    exact h.trans (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
  exact le_of_mul_le_mul_right hbound (Real.exp_pos p)

end NativeVectorCorrelation

namespace NativeMixedCorrelation

theorem exists_fixed_quadratic_coordinate {N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (W : NativeMixedCorrelation 1 N p f) :
    ∃ i : Fin W.mixed.outputDim, ∃ H ⊆ W.shifts, H.Nonempty ∧
      Real.exp (-(2 * p)) * N ≤ (H.card : ℝ) ∧
      ∀ h ∈ H, Real.exp (-(2 * p)) ≤
        ‖𝔼 x, multiplicativeDerivative f h x * star (W.mixed.evalCyclic N i (correlationInput h x))‖ := by
  obtain ⟨i, H, hsub, hH, hdense, hcorr⟩ := NativeVectorCorrelation.exists_fixed_coordinate
    W.shifts W.nonempty (nativeMixedResidual f W.mixed)
    (by simpa only [Fintype.card_fin] using W.mixed.output_bound) W.correlation
  refine ⟨i, H, hsub, hH, ?_, ?_⟩
  · have hW : Real.exp (-p) * N ≤ (W.shifts.card : ℝ) := by
      simpa only [ZMod.card] using W.density
    calc
      Real.exp (-(2 * p)) * N = Real.exp (-p) * (Real.exp (-p) * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-p) * W.shifts.card := mul_le_mul_of_nonneg_left hW (Real.exp_nonneg _)
      _ ≤ H.card := hdense
  · intro h hh
    obtain ⟨V⟩ := hcorr h hh
    exact V.mean_correlation_of_degree_zero

end NativeMixedCorrelation

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticCyclicIntegration
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

namespace NativeMultidegreeNilcharacter

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_quadratic_diagonal_niltest {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (i : Fin W.outputDim) :
    ∃ T : W.model.Niltest (fun _ : Unit => 1), T.normBound = 1 ∧ T.ComplexityLE (p + 4) ∧
      ∀ n : ℤ, T.eval (fun _ => n) = W.eval i (fun _ => n) := by
  obtain ⟨T, hT, hcomplexity, heval⟩ := W.exists_linear_niltest i
    (fun _ => { toFun := fun x : Unit → ℤ => x (), map_zero' := rfl, map_add' := fun _ _ => rfl })
  exact ⟨T, hT, hcomplexity, fun n => heval (fun _ => n)⟩

end NativeMultidegreeNilcharacter

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CubicResidualPhase
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

namespace NativeMixedCorrelation

theorem exists_fixed_residual_coordinate {s N : ℕ} [NeZero N] {p : ℝ}
    {f : ZMod N → ℂ} (W : NativeMixedCorrelation s N p f) :
    ∃ i : Fin W.mixed.outputDim, ∃ H ⊆ W.shifts, H.Nonempty ∧
      Real.exp (-(2 * p)) * N ≤ (H.card : ℝ) ∧
      ∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N p
        (fun _ : Unit => nativeMixedResidual f W.mixed h i)) := by
  obtain ⟨i, H, hsub, hH, hdense, hcorr⟩ := NativeVectorCorrelation.exists_fixed_coordinate
    W.shifts W.nonempty (nativeMixedResidual f W.mixed)
    (by simpa only [Fintype.card_fin] using W.mixed.output_bound) W.correlation
  refine ⟨i, H, hsub, hH, ?_, hcorr⟩
  have hW : Real.exp (-p) * N ≤ (W.shifts.card : ℝ) := by
    simpa only [ZMod.card] using W.density
  calc
    Real.exp (-(2 * p)) * N = Real.exp (-p) * (Real.exp (-p) * N) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-p) * W.shifts.card := mul_le_mul_of_nonneg_left hW (Real.exp_nonneg _)
    _ ≤ H.card := hdense

end NativeMixedCorrelation

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SelectedCenteredJointSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem selectedJointFiniteLaw_support {B K I : Type*} [Fintype K] [Fintype I]
    (A : Finset B) (hA : A.Nonempty)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (D : B → (K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass A modulus T W D)
    (z : A × rectangularWeightIndices 0 W 1)
    (hz : 0 < (selectedJointFiniteLaw A hA modulus T W hW hZ D hD0 hD).weight z) :
    columnResiduePattern modulus z.2.val ∈ T ∧ 0 < D z.1.val z.2.val := by
  rw [selectedJointFiniteLaw_weight] at hz
  constructor
  · by_contra h
    rw [selectedResidueSmoothPMF_toReal, selectedResidueSmoothWeight, if_neg h] at hz
    simp only [zero_div, mul_zero, zero_mul] at hz
    exact (lt_irrefl 0) hz
  · apply lt_of_le_of_ne (hD0 _ _)
    intro he
    rw [← he] at hz
    simp only [mul_zero, zero_div] at hz
    exact (lt_irrefl 0) hz

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedInactiveSupportBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem blockJetScaleBound_four_exp (q h b : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hq : (q : ℝ) ≤ D) (hh : (h : ℝ) ≤ D) (hb : (b : ℝ) ≤ D) :
    blockJetScaleBound q h b 4 ≤ Real.exp (D ^ 2 + 2 * D + 4) := by
  have hbexp : (b : ℝ) ≤ Real.exp D := hb.trans (by linarith [Real.add_one_le_exp D])
  have hqexp : ((q + 1 : ℕ) : ℝ) ≤ Real.exp D := by
    push_cast
    linarith [Real.add_one_le_exp D]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpowtwo : (2 : ℝ) ^ h ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo (by norm_num) h hh
  have hpowq := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg (q + 1)) hqexp hD h hh
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  unfold blockJetScaleBound
  calc
    _ ≤ Real.exp D * Real.exp D * Real.exp (D * D) * Real.exp 4 := by
      gcongr
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

namespace VectorPolynomial

def allocatedNaturalSupportLog {A : Type*} [Semiring A] (D : A) : A := D ^ 2 + 3 * D + 7

def allocatedNaturalSiteLog {A : Type*} [Semiring A] (D : A) : A := D ^ 2 + 4 * D + 8

def allocatedSiteCoefficientLog {A : Type*} [Semiring A] (D : A) : A := D ^ 2 + 5 * D + 8

theorem allocatedNaturalSupportLog_nonneg {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ allocatedNaturalSupportLog D := by unfold allocatedNaturalSupportLog; positivity

theorem allocatedSiteCoefficientLog_nonneg {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ allocatedSiteCoefficientLog D := by unfold allocatedSiteCoefficientLog; positivity

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
variable {D : ℝ} (h : AllocatedComparisonDimensions (G := G) B α (fun j => (rowSets j : Type _)) D)

include h

theorem allocatedIntegerBlock_card_le (j : Fin m) (i : Fin (n j)) :
    (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ D := by
  have hs : ((layerIntegerPrincipalSlots (G := G) B j i).card : ℝ) ≤ D :=
    (Nat.cast_le.mpr (Finset.card_le_univ _)).trans (h.coefficients j)
  simpa only [layerIntegerPrincipalSlots_card] using hs

theorem allocatedNaturalSupportRadius_exp_bound (j : Fin m) (i : Fin (n j)) :
    allocatedNaturalSupportRadius (G := G) B α j i ≤ Real.exp (allocatedNaturalSupportLog D) := by
  have hb := allocatedIntegerBlock_card_le B rowSets h j i
  have hs : ((layerIntegerPrincipalSlots (G := G) B j i).card : ℝ) ≤ D := by
    simpa only [layerIntegerPrincipalSlots_card] using hb
  have hblock := blockJetScaleBound_four_exp (Fintype.card α) (j.val + 1)
    (Fintype.card (B ⟨j, Sum.inr i⟩)) h.nonneg h.cube (h.layer_degree B j) hb
  have hD := h.nonneg
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hc : allocatedNaturalConstantRadius (G := G) B j i ≤ Real.exp (D + 1) := by
    unfold allocatedNaturalConstantRadius
    calc
      _ ≤ Real.exp 1 * Real.exp D := mul_le_mul htwo
        (by linarith [Real.add_one_le_exp D]) (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, add_comm]
  have ha := add_le_exp_add_one (by positivity : 0 ≤ D ^ 2 + 2 * D + 4)
    (by norm_num : (0 : ℝ) ≤ 0) hblock (by norm_num : (1 / 4 : ℝ) ≤ Real.exp 0)
  have ht := add_le_exp_add_one (by positivity : 0 ≤ (D ^ 2 + 2 * D + 4) + 0 + 1)
    (by positivity : 0 ≤ D + 1) ha hc
  exact ht.trans_eq (by
    congr 1
    unfold allocatedNaturalSupportLog
    ring)

theorem allocatedNaturalSiteRadius_exp_bound (j : Fin m) (i : Fin (n j)) :
    allocatedNaturalSiteRadius (G := G) B j i (rowSets j) + 1 / 4 ≤
      Real.exp (allocatedNaturalSiteLog D) := by
  have hD := h.nonneg
  have hrow : ((rowSets j).card : ℝ) ≤ D := by
    simpa only [Fintype.card_coe] using h.rows j
  have hr : ((rowSets j).card : ℝ) ≤ Real.exp D :=
    hrow.trans (show D ≤ Real.exp D by linarith [Real.add_one_le_exp D])
  have hs := allocatedNaturalSupportRadius_exp_bound B rowSets h j i
  have hm : allocatedNaturalSiteRadius (G := G) B j i (rowSets j) ≤
      Real.exp (D + allocatedNaturalSupportLog D) := by
    unfold allocatedNaturalSiteRadius
    exact (mul_le_mul hr hs (allocatedNaturalSupportRadius_nonneg B α j i)
      (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  have ht := add_le_exp_add_one (add_nonneg hD (allocatedNaturalSupportLog_nonneg hD))
    (by norm_num : (0 : ℝ) ≤ 0) hm (by norm_num : (1 / 4 : ℝ) ≤ Real.exp 0)
  exact ht.trans_eq (by
    congr 1
    unfold allocatedNaturalSiteLog allocatedNaturalSupportLog
    ring)

theorem allocatedSiteCoefficientRadius_exp_bound (a : Σ j : Fin m, Fin (n j)) :
    allocatedSiteCoefficientRadius (G := G) B rowSets a ≤ Real.exp (allocatedSiteCoefficientLog D) := by
  have hD := h.nonneg
  have hs := allocatedNaturalSupportRadius_exp_bound B rowSets h a.1 a.2
  have ht := allocatedNaturalSiteRadius_exp_bound B rowSets h a.1 a.2
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ) ^ (a.1.val + 1) ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo
      (by norm_num) (a.1.val + 1) (h.layer_degree B a.1)
  unfold allocatedSiteCoefficientRadius
  refine max_le (hs.trans (Real.exp_le_exp.mpr ?_)) ?_
  · unfold allocatedNaturalSupportLog allocatedSiteCoefficientLog
    linarith
  · have hh := (mul_le_mul hp ht
      (by have hn := allocatedNaturalSiteRadius_nonneg (G := G) B a.1 a.2 (rowSets a.1); positivity)
      (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
    exact hh.trans_eq (by
      congr 1
      unfold allocatedSiteCoefficientLog allocatedNaturalSiteLog
      ring)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

variable {D : ℝ} (h : AllocatedComparisonDimensions (G := G) B α (fun j => (rowSets j : Type _)) D)

include h

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCoverLogBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

def allocatedIdealCoverInputLog {A : Type*} [Semiring A] (m : ℕ) (D c : A) : A :=
  allocatedSiteCoefficientLog D + (m + 1 : ℕ) * D + c + 4

theorem allocatedIdealCoverInputLog_bounds (m : ℕ) {D c : ℝ}
    (hD : 0 ≤ D) (hc : 0 ≤ c) :
    let L := allocatedIdealCoverInputLog m D c
    0 ≤ L ∧ D ^ 2 + 2 * D ≤ L ∧ (m + 1 : ℕ) * D + 2 ≤ L ∧
      allocatedSiteCoefficientLog D + 1 ≤ L ∧ D ≤ L ∧ c ≤ L := by
  have hm : 0 ≤ (m + 1 : ℕ) * D := mul_nonneg (Nat.cast_nonneg _) hD
  dsimp only [allocatedIdealCoverInputLog, allocatedSiteCoefficientLog]
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · nlinarith [sq_nonneg D]
  constructor
  · linarith
  constructor <;> nlinarith [sq_nonneg D]

noncomputable def allocatedIdealCoverPrimitiveLog {A : Type*} [Semiring A]
    (m : ℕ) (p c : A) : A :=
  8 * allocatedIdealCoverInputLog m (allocatedComparisonDimension m p) c + 14

noncomputable def allocatedIdealCoverPrimitiveRadius (m : ℕ) (p c : ℝ) : ℝ :=
  Real.exp (-allocatedIdealCoverPrimitiveLog m p c)

theorem allocatedIdealCoverPrimitiveRadius_bounds (m : ℕ) {p c : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) :
    0 ≤ allocatedIdealCoverPrimitiveLog m p c ∧
      0 < allocatedIdealCoverPrimitiveRadius m p c ∧
      allocatedIdealCoverPrimitiveRadius m p c ≤ 1 ∧
      (allocatedIdealCoverPrimitiveRadius m p c)⁻¹ = Real.exp (allocatedIdealCoverPrimitiveLog m p c) := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hL := (allocatedIdealCoverInputLog_bounds m hD hc).1
  have hlog : 0 ≤ allocatedIdealCoverPrimitiveLog m p c := by
    unfold allocatedIdealCoverPrimitiveLog
    positivity
  refine ⟨hlog, Real.exp_pos _, ?_, ?_⟩
  · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hlog)
  · simp only [allocatedIdealCoverPrimitiveRadius, Real.exp_neg, inv_inv]

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

theorem allocatedIdealCoverRadius_inverse_from_dimensions {D c : ℝ}
    (h : AllocatedComparisonDimensions (G := G) B α (fun j => (rowSets j : Type _)) D)
    (hc : 0 ≤ c) (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ D)
    (hn : ∀ j, (n j : ℝ) ≤ D)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCc : ∀ j, C j ≤ Real.exp c) (j : Fin m) :
    (allocatedIdealCoverRadius (G := G) B rowSets C j)⁻¹ ≤
      Real.exp (8 * allocatedIdealCoverInputLog m D c + 14) := by
  obtain ⟨hL, hLA, hLI, hLW, hLD, hLc⟩ := allocatedIdealCoverInputLog_bounds m h.nonneg hc
  have hde : D ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have heL := Real.exp_le_exp.mpr hLD
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpowtwo : (2 : ℝ) ^ Fintype.card α ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo
      (by norm_num) (Fintype.card α) h.cube
  have hbase : (Fintype.card α : ℝ) + 1 ≤ Real.exp D := by
    linarith [Real.add_one_le_exp D, h.cube]
  have hpow := pow_le_exp_mul_of_le_exp (by positivity) hbase h.nonneg
    (j.val + 1) (h.layer_degree B j)
  have hA : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤
        Real.exp (D ^ 2 + 2 * D) := by
    calc
      _ ≤ Real.exp D * (Real.exp D * Real.exp (D * D)) := by
        gcongr
        exact (h.coefficients j).trans hde
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hIdeal : partitionedIdealRadius α m + 1 ≤ Real.exp (allocatedIdealCoverInputLog m D c) := by
    apply (partitionedIdealRadius_add_one_le_exp α m).trans
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul_of_nonneg_left h.cube (by positivity : 0 ≤ (m : ℝ) + 1)
    push_cast at hLI
    linarith
  have hWindow (i : Fin (n j)) : allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1 ≤
      Real.exp (allocatedIdealCoverInputLog m D c) := by
    have h1 := one_add_le_exp_succ (allocatedSiteCoefficientLog_nonneg h.nonneg)
      (allocatedSiteCoefficientRadius_exp_bound B rowSets h ⟨j, i⟩)
    have h2 : allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1 ≤
        Real.exp (allocatedSiteCoefficientLog D + 1) := by
      simpa only [add_comm] using h1
    exact h2.trans (Real.exp_le_exp.mpr hLW)
  have hrows : ((rowSets j).card : ℝ) ≤ D := by
    simpa only [Fintype.card_coe] using h.rows j
  exact allocatedIdealCoverRadius_inv_le_exp B rowSets hL C hC j
    (hA.trans (Real.exp_le_exp.mpr hLA)) hIdeal ((hn j).trans (hde.trans heL)) hWindow
    (hrows.trans (hde.trans heL)) ((hI j).trans (hde.trans heL))
    ((hCc j).trans (Real.exp_le_exp.mpr hLc))

theorem allocatedIdealCoverPrimitiveRadius_le {p c : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hq : Fintype.card α ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCc : ∀ j, C j ≤ Real.exp c) (j : Fin m) :
    allocatedIdealCoverPrimitiveRadius m p c ≤ allocatedIdealCoverRadius (G := G) B rowSets C j := by
  have h := allocatedComparisonDimensions_of_primitive (G := G) (α := α)
    (O := fun j => (rowSets j : Type _)) B
    (fun j => (Subtype.val : rowSets j → Finset α)) hq (fun _ => Subtype.val_injective) hp hvars hI hn
  have hpD := (allocatedComparisonDimension_bounds m hp).2.2.1
  have hi := allocatedIdealCoverRadius_inverse_from_dimensions B rowSets h hc
    (fun j => (hI j).trans hpD) (fun j => (hn j).trans hpD) C hC hCc j
  have hr := allocatedIdealCoverRadius_pos (G := G) B rowSets C hC j
  have hinv := (inv_le_inv₀ (Real.exp_pos (allocatedIdealCoverPrimitiveLog m p c)) (inv_pos.mpr hr)).2 hi
  simpa only [allocatedIdealCoverPrimitiveRadius, Real.exp_neg, inv_inv] using hinv

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial

theorem allocatedComparisonDimension_mono (m : ℕ) {p p' : ℝ}
    (hp : 0 ≤ p) (hpp : p ≤ p') :
    allocatedComparisonDimension m p ≤ allocatedComparisonDimension m p' := by
  unfold allocatedComparisonDimension
  gcongr

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

theorem allocatedIdealCoverRadius_half_le_physical
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (j : Fin m) :
    allocatedIdealCoverRadius (G := G) B rowSets C j / 2 ≤
      allocatedPhysicalChartRadius (G := G) B α C 1 j := by
  let N : ℝ := Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))
  let A : ℝ := (2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)
  let H := allocatedIdealCoverSupport (G := G) B rowSets j
  let D : ℝ := 4 * (C j + 1) * ((Fintype.card (I j) : ℝ) + 1)
  let r : ℝ := (rowSets j).card + 1
  let : Nonempty (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) :=
    ⟨⟨0, by simp⟩⟩
  have hN : 1 ≤ N := by
    dsimp only [N]
    exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos (α :=
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)))
  have hA : 0 < A := by dsimp [A]; positivity
  have hH : 0 ≤ H := allocatedIdealCoverSupport_nonneg B rowSets j
  have hNA : N * A ≤ H := allocatedIdealCoverSupport_inactive B rowSets j
  have hr : 1 ≤ r := by
    dsimp only [r]
    linarith [Nat.cast_nonneg (α := ℝ) (rowSets j).card]
  have hCj := hC j
  have hD : 0 < D := by dsimp [D]; positivity
  have hnum : (N + 1) * A ≤ 2 * (H + 1) := by nlinarith
  have hden : D * ((N + 1) * A) ≤ 2 * (D * r * (H + 1)) := by
    have hmul := mul_le_mul_of_nonneg_left hnum hD.le
    have hrow := mul_le_mul_of_nonneg_right hr (show 0 ≤ D * (H + 1) by positivity)
    nlinarith
  have hleft : 0 < D * r * (H + 1) := by positivity
  have hright : 0 < D * ((N + 1) * A) := by positivity
  have hi : 1 / (D * r * (H + 1)) ≤ 2 / (D * ((N + 1) * A)) :=
    (div_le_div_iff₀ hleft hright).mpr (by simpa only [one_mul] using hden)
  have hh : (1 / (D * r * (H + 1))) / 2 ≤ 1 / (D * ((N + 1) * A)) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hi
  convert hh using 1 <;>
    simp only [allocatedIdealCoverRadius, finiteRowChartRadius, allocatedPhysicalChartRadius,
      D, r, H, N, A, add_comm (1 : ℝ)] <;> ring

noncomputable def allocatedSourceCoverRadiusLog {A : Type*} [Semiring A]
    (m : ℕ) (p c : A) : A := allocatedIdealCoverPrimitiveLog m p c + 1

noncomputable def allocatedSourceCoverRadius (m : ℕ) (p c : ℝ) : ℝ :=
  Real.exp (-allocatedSourceCoverRadiusLog m p c)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialBoxDetection
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem exists_polynomial_box_detection.{u,v} (s : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type v} [Fintype σ] [DecidableEq σ] {L : Type u} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (p : ℝ), 0 ≤ p →
      (Fintype.card σ : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) p →
      ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (T : D.Niltest w), T.ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) p) →
      ∀ (a : σ → ℤ) (lengths : σ → ℕ) [∀ i, NeZero (lengths i)] (f : (σ → ℤ) → ℂ),
      (∀ x ∈ translatedIntegerBox a lengths, ‖f x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖finiteCorrelation (translatedIntegerBox a lengths) f T.eval‖ →
      Real.exp (-((p + C) ^ C)) ≤ finiteSupportGowersNorm (s + 1) (translatedIntegerBox a lengths) f := by
  obtain ⟨c, _, hc⟩ := exists_boxNiltestDetection s
  let R := (Polynomial.X + P + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro σ _ _ L _ _ d _ _ _ _ D p hp hσ w hw T hT a lengths _ f hf hcorr
  let q := p + P.eval₂ (Nat.castRingHom ℝ) p
  have hP : 0 ≤ P.eval₂ (Nat.castRingHom ℝ) p := natPolynomial_eval_nonneg P hp
  have hq : 0 ≤ q := add_nonneg hp hP
  have hPq : P.eval₂ (Nat.castRingHom ℝ) p ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hcorrq := (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hcorr
  have hn := hc D q hq (hσ.trans hPq) w hw T (hT.mono hPq) a lengths f hf hcorrq
  have hbudget : (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
  exact (Real.exp_le_exp.mpr (neg_le_neg hbudget)).trans hn

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.AllocatedNiltestSourceSelection
namespace OAI

universe u v w w₁ w₂ w₃ w₄

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_nested_box_niltest_detection (s : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {I : Type v} [Fintype I] [DecidableEq I] {L : Type u} [LieRing L] [LieAlgebra ℚ L] {dim : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s dim) (p : ℝ), 0 ≤ p →
      (Fintype.card I : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) p →
      ∀ (T : D.Niltest (fun _ : I => 1)), T.ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) p) →
      ∀ (c b : I → ℤ) (m d : ℕ) (H K : I → ℕ), 0 < m → 0 < d → (∀ i, 0 < K i) →
      commonStrideBox b d K ⊆ commonStrideBox c m H →
      ∀ f : (I → ℤ) → ℂ, (∀ x ∈ commonStrideBox b d K, ‖f x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖finiteCorrelation (commonStrideBox b d K) f
        (fun y => T.eval (commonStrideIndex c m y))‖ →
      Real.exp (-((p + C) ^ C)) ≤ finiteSupportGowersNorm (s + 1) (integerBox K)
        (fun x => f (commonStridePoint b d x)) := by
  obtain ⟨C, hC, hdetect⟩ := exists_polynomial_box_detection s P
  refine ⟨C, hC, ?_⟩
  intro I _ _ L _ _ dim _ _ _ _ D p hp hI T hT c b m d H K hm hd hK hsub f hf hcorr
  obtain ⟨U, hU, heval⟩ := T.exists_nested_box_restriction c b hm hd H K hK hsub
  let _ : ∀ i, NeZero (K i) := fun i => ⟨(hK i).ne'⟩
  have hzero : translatedIntegerBox (0 : I → ℤ) K = integerBox K := by
    simp [translatedIntegerBox, translateSupport]
  have hcorr' : Real.exp (-p) ≤ ‖finiteCorrelation (integerBox K)
      (fun x => f (commonStridePoint b d x)) U.eval‖ := by
    rw [finiteCorrelation_commonStrideBox b hd] at hcorr
    have he : finiteCorrelation (integerBox K) (fun x => f (commonStridePoint b d x)) U.eval =
        finiteCorrelation (integerBox K) (fun x => f (commonStridePoint b d x))
          (fun x => T.eval (commonStrideIndex c m (commonStridePoint b d x))) := by
      apply Finset.expect_congr rfl
      intro x hx
      rw [heval x hx]
    rwa [he]
  have hn := hdetect D p hp hI (fun _ : I => 1) (fun _ => zero_lt_one) U ((hU _).mpr hT)
    0 K (fun x => f (commonStridePoint b d x))
    (fun x hx => hf _ (commonStridePoint_mem b d K (hzero ▸ hx))) (hzero.symm ▸ hcorr')
  simpa only [hzero] using hn

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_finite_site_niltest_detection (s : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {I : Type v} [Fintype I] [DecidableEq I] {L : Type u} [LieRing L] [LieAlgebra ℚ L] {dim : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s dim) (p : ℝ), 0 ≤ p →
      (Fintype.card I : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) p →
      ∀ (U : D.Niltest (fun _ : I => 1)), U.ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) p) →
      ∀ {T : Type w} [Nonempty T] [DecidableEq T] (e : T → I → ℤ), Function.Injective e →
      ∀ (A S : Finset T) (c b : I → ℤ) (m d : ℕ) (H K : I → ℕ),
      0 < m → 0 < d → (∀ i, 0 < K i) → A ⊆ S →
      S.image e = commonStrideBox c m H → A.image e = commonStrideBox b d K →
      ∀ (f w : T → ℂ), (∀ t, ‖f t‖ ≤ 1) →
      (∀ t ∈ S, w t = star (U.eval (commonStrideIndex c m (e t)))) →
      Real.exp (-p) ≤ ‖𝔼 t ∈ A, f t * w t‖ →
      Real.exp (-((p + C) ^ C)) ≤ finiteSupportGowersNorm (s + 1) (integerBox K)
        (fun x => finiteSiteExtension e f (commonStridePoint b d x)) := by
  obtain ⟨C, hC, hdetect⟩ := exists_nested_box_niltest_detection s P
  refine ⟨C, hC, ?_⟩
  intro I _ _ L _ _ dim _ _ _ _ D p hp hI U hU T _ _ e he A S c b m d H K hm hd hK hAS hS hA f w hf hw hc
  have hsub : commonStrideBox b d K ⊆ commonStrideBox c m H := by
    rw [← hA, ← hS]
    exact Finset.image_subset_image hAS
  have heq := finiteSiteExtension_test_mean e he A f w
    (fun y => U.eval (commonStrideIndex c m y)) (fun t ht => hw t (hAS ht))
  rw [heq, hA] at hc
  exact hdetect D p hp hI U hU c b m d H K hm hd hK hsub (finiteSiteExtension e f)
    (fun x _ => finiteSiteExtension_norm_le e f hf x) hc

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

theorem exists_sampled_niltest_cube_detection_with_sides (s : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {I : Type v} [Fintype I] [DecidableEq I]
      {Ω : Type w₁} [Fintype Ω] [Nonempty Ω] {T : Type w₂} [Fintype T] [Nonempty T]
      {X : Type w₃} {J : Ω → Type w₄} [∀ z, Nonempty (J z)]
      {L : ∀ z, J z → Type u} [∀ z j, LieRing (L z j)] [∀ z j, LieAlgebra ℚ (L z j)]
      {dim : ∀ z, J z → ℕ}
      [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] L z j)] [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L z j)]
      [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] L z j)]
      (D : ∀ z j, RationalFilteredNilmanifold (L z j) s (dim z j))
      (U : ∀ z j, (D z j).Niltest (fun _ : I => 1))
      (μ : FiniteProbabilityWeights Ω) (F : Ω → T → X)
      (S : ∀ z, J z → Finset T) (e : T → I → ℤ), Function.Injective e →
      ∀ (c : ∀ z, J z → I → ℤ) (m : ∀ z, J z → ℕ) (H : ∀ z, J z → I → ℕ),
      (∀ z j, 0 < m z j) → (∀ z j, (S z j).image e = commonStrideBox (c z j) (m z j) (H z j)) →
      ∀ (p q : ℝ) (N : I → ℕ), 0 ≤ p → 0 ≤ q →
      (∀ z j, IsDenseCommonStrideBox N p ((S z j).image e)) →
      (Fintype.card I : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) q →
      (∀ z j, (U z j).ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) q)) →
      (∀ z j, ((U z j).normBound : ℝ) ≤ 1) →
      ∀ (v : X → ℂ) (α : ℝ), (∀ x, ‖v x‖ ≤ 1) → 0 < α → α ≤ 1 →
      Fintype.card I * Real.exp (-p) ≤ α / 8 → Real.exp (-q) ≤ α / 4 →
      α ≤ sampledSliceSeminorm μ F S
        (fun z j t => star ((U z j).eval (commonStrideIndex (c z j) (m z j) (e t)))) v →
      ∃ (b : I → ℤ) (d : ℕ) (K : I → ℕ), 0 < d ∧ (∀ i, 0 < K i) ∧
        (∀ i, integerProgressionSupport (b i) (d : ℤ) (K i) ⊆ Finset.Ico (0 : ℤ) (N i : ℤ)) ∧
        (∀ i, Real.exp (-(p + 1)) * N i ≤ (K i : ℝ)) ∧
        IsDenseCommonStrideBox N (p + 1) (commonStrideBox b d K) ∧
        commonStrideBox b d K ⊆ Finset.univ.image e ∧
        (Real.exp (-((5 * p + 20) * Fintype.card I + p + 2)) * (α / 2)) *
          Real.exp (-((q + C) ^ C)) ^ (2 ^ (s + 1)) ≤
          (μ.complexMean (fun z => normalizedSupportedCubeSum (s + 1) (integerBox K)
            (fun _ x => finiteSiteExtension e (fun t => v (F z t)) (commonStridePoint b d x)))).re := by
  obtain ⟨C, hC, hdetect⟩ := exists_finite_site_niltest_detection s P
  refine ⟨C, hC, ?_⟩
  intro I _ _ Ω _ _ T _ _ X J _ L _ _ dim _ _ _ _ D U μ F S e he c m H hm hS p q N hp hq
    hslice hI hU hcap v α hv hα hαone hmesh hthreshold hmean
  let w : ∀ z, J z → T → ℂ := fun z j t =>
    star ((U z j).eval (commonStrideIndex (c z j) (m z j) (e t)))
  have hw (z) (j) (t) : ‖w z j t‖ ≤ 1 := by
    simpa only [w, norm_star] using
      ((U z j).norm_eval_le (commonStrideIndex (c z j) (m z j) (e t))).trans (hcap z j)
  obtain ⟨A, hAn, hAdense, G, j, hmass, hcorr⟩ :=
    exists_dense_common_sampled_box_of_seminorm μ F S w e he hp N hslice hw v hv hα hαone hmesh hmean
  have hDense := hAdense
  obtain ⟨b, d, K, hd, hK, hsubsetK, hdenseK, hA⟩ := hAdense
  have hnorm (z : Ω) (hz : z ∈ G) :
      Real.exp (-((q + C) ^ C)) ≤ finiteSupportGowersNorm (s + 1) (integerBox K)
        (fun x => finiteSiteExtension e (fun t => v (F z t)) (commonStridePoint b d x)) := by
    exact hdetect (D z (j z)) q hq hI (U z (j z)) (hU z (j z)) e he A (S z (j z))
      (c z (j z)) b (m z (j z)) d (H z (j z)) K (hm z (j z)) hd hK
      (hcorr z hz).1 (hS z (j z)) hA (fun t => v (F z t)) (w z (j z))
      (fun t => hv _) (fun _ _ => rfl) (hthreshold.trans (hcorr z hz).2)
  refine ⟨b, d, K, hd, hK, hsubsetK, hdenseK, ?_, ?_, ?_⟩
  · rw [← hA]
    exact hDense
  · rw [← hA]
    exact Finset.image_subset_image (Finset.subset_univ A)
  · let _ : ∀ i, NeZero (K i) := fun i => ⟨(hK i).ne'⟩
    exact sampled_normalized_cube_lower_bound (boxReduction_reflectsPairSums K) μ G s
      (fun z x => finiteSiteExtension e (fun t => v (F z t)) (commonStridePoint b d x))
      (Real.exp_nonneg _) hmass hnorm

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

end Erdos3

end

section

namespace Erdos3

end Erdos3

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {s : ℕ} (X : Type) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)

local notation "kernelLaw" => FiniteProbabilityWeights.pi
  (fun _ : G => integerScalarCubeWeights (Fin (s + 2)) S.value S.positive)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3

end Erdos3

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {s : ℕ} (X : Type) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)

local notation "kernelLaw" => FiniteProbabilityWeights.pi
  (fun _ : G => integerScalarCubeWeights (Fin (s + 2)) S.value S.positive)


end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.AllocatedNiltestSupportedSlicedDetection
namespace OAI

section

namespace Erdos3

noncomputable def sampledSupportedSlicedDetectionConstant (s : ℕ) (P : Polynomial ℕ) : ℕ :=
  Classical.choose (exists_sampled_niltest_cube_detection_with_sides.{0,0,0,0,0,0} s P)

end Erdos3

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {s : ℕ} (X : Type) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)

local notation "kernelLaw" => FiniteProbabilityWeights.pi
  (fun _ : G => integerScalarCubeWeights (Fin (s + 2)) S.value S.positive)


end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedNestedEndpointDimensionBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_endpointDimension_local_budget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {x pnum : ℝ}, 0 ≤ x → pnum ∈ Set.Icc 0 x →
      ∀ nX M : ℕ, (nX : ℝ) ≤ x → (M : ℝ) ≤ x →
      allocatedComparisonDimension m pnum ≤ (x + C) ^ C ∧
        ((nX + m * M : ℕ) : ℝ) ≤ (x + C) ^ C := by
  let Q : Polynomial ℕ := allocatedComparisonDimension m Polynomial.X +
    Polynomial.C (m + 1) * Polynomial.X
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro x pnum hx hnum nX M hnX hM
  have htotal : allocatedComparisonDimension m x + (m + 1 : ℕ) * x ≤ (x + C) ^ C := by
    simpa [Q, allocatedComparisonDimension, Polynomial.eval₂_pow] using hbound x hx
  have hdim0 : 0 ≤ allocatedComparisonDimension m x := (allocatedComparisonDimension_bounds m hx).1
  have hmul0 : (0 : ℝ) ≤ (m + 1 : ℕ) * x := mul_nonneg (Nat.cast_nonneg _) hx
  have hmod : ((nX + m * M : ℕ) : ℝ) ≤ (m + 1 : ℕ) * x := by
    have hmul := mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    nlinarith only [hnX, hmul]
  exact ⟨(allocatedComparisonDimension_mono m hnum.1 hnum.2).trans
    (by linarith only [htotal, hmul0]), hmod.trans (by linarith only [htotal, hdim0])⟩

theorem exists_endpointDimension_uniform_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ m : ℕ, m ≤ s →
      ∀ {x pnum : ℝ}, 0 ≤ x → pnum ∈ Set.Icc 0 x →
      ∀ nX M : ℕ, (nX : ℝ) ≤ x → (M : ℝ) ≤ x →
      allocatedComparisonDimension m pnum ≤ (x + C) ^ C ∧
        ((nX + m * M : ℕ) : ℝ) ≤ (x + C) ^ C := by
  classical
  choose ex hex hb using fun j : Fin (s + 1) => exists_endpointDimension_local_budget j.val
  let C := 2 + ∑ j, ex j
  refine ⟨C, by dsimp only [C]; omega, ?_⟩
  intro m hm x pnum hx hnum nX M hnX hM
  let j : Fin (s + 1) := ⟨m, by omega⟩
  have hsum : ex j ≤ ∑ i, ex i :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have heC : ex j ≤ C := by dsimp only [C]; omega
  have hCReal : (2 : ℝ) ≤ C := Nat.cast_le.mpr ((hex j).trans heC)
  have hpow : (x + ex j) ^ ex j ≤ (x + C) ^ C :=
    (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl (Nat.cast_le.mpr heC)) _).trans
      (pow_le_pow_right₀ (by linarith only [hx, hCReal]) heC)
  have h := hb j hx hnum nX M hnX hM
  exact ⟨h.1.trans hpow, h.2.trans hpow⟩

noncomputable def preparedNestedEndpointDimensionExponent (s : ℕ) : ℕ :=
  (exists_endpointDimension_uniform_budget s).choose

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankIntegerDecay
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {N L : ℕ}

noncomputable def allocatedCongruenceIntegerPolynomial
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (v : LayerSamplerVariables G I n B → ℤ) :
    AllocatedCongruenceRankOutput X E inactive j →
      MvPolynomial (LayerSamplerLongVariables inactive G B) ℤ
  | .inl x => conditionPolynomial (allocatedLongEmbedding inactive)
      (allocatedLongEmbedding inactive).injective v
      (C (base x.val) + spatialRankPolynomial (fun d => noise (d, x.val)))
  | .inr (.inl i) => conditionPolynomial (allocatedLongEmbedding inactive)
      (allocatedLongEmbedding inactive).injective v
      (modularBoundedCoefficientPolynomial (j.val + 1) (fun q => r j q i))
  | .inr (.inr a) => conditionPolynomial (allocatedLongEmbedding inactive)
      (allocatedLongEmbedding inactive).injective v
      (modularBoundedCoefficientPolynomial (j.val + 1)
        (projection (allocatedCongruenceIntegerEmbedding inactive j a)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)

noncomputable def allocatedCongruenceIntegerSelectedCoefficients :
    AllocatedCongruenceScalarIndex X E inactive L → ℤ
  | ⟨_j, .inl x, l⟩ => noise (spatialKernelRankSlot spatial l, x.val)
  | ⟨j, .inr (.inl i), l⟩ => r j (kernelRankCoefficientSlot (layerSamplerDegree I n) (kernel j) l) i
  | ⟨j, .inr (.inr a), l⟩ => projection j (allocatedCongruenceIntegerEmbedding inactive j a)
      (canonicalPrincipalSubblockSlot (layerSamplerDegree I n)
        ⟨j, Sum.inr a.val⟩ (block j (allocatedCongruenceIntegerEmbedding inactive j a)) l)

local notation "selected" => allocatedCongruenceIntegerSelectedCoefficients
  inactive noise r projection spatial kernel block

omit [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ a, Fintype (B a)] in

theorem allocatedCongruenceIntegerSelectedCoefficients_reduce (N : ℕ)
    (j : Fin m) (o : AllocatedCongruenceRankOutput X E inactive j) (l : Fin L) :
    (selected ⟨j, (o,l)⟩ : ZMod N) =
      allocatedSelectedRankCoefficients inactive j (fun q => (noise q : ZMod N))
        (fun j q i => (r j q i : ZMod N)) (fun a q => (projection j a q : ZMod N))
        spatial (kernel j) (block j) (allocatedCongruenceOutputEmbedding inactive j o) l := by
  rcases o with x | i | a <;> rfl

noncomputable def allocatedCongruenceBadDepth
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (C : ℝ) : ℕ → ℕ :=
  fun p => largestTestedBadDepth A
    (allocatedCongruenceRankBad inactive noise r projection spatial kernel block P C) p selected

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativePresentPivotQuotientModel
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped Classical

theorem exists_nativePresentPivotQuotient_budget :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L M J : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {s d e r : ℕ} (D : RationalFilteredNilmanifold L s d)
      (b : Basis (Fin e) ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
      (eta : J → L →ₗ[ℚ] ℚ) (code : Fin r → Option J) (p : ℝ),
      1 ≤ s → 0 ≤ p → D.GeometryComplexityLE p → (e : ℝ) ≤ p → (r : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (b.repr (φ (D.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (eta i (D.basis j)) ≤ p) →
      let ideal := D.filtration.pivotAnnihilatorIdeal φ
        (fun k => eta (kernelProjectionSelectedPivot code k))
        (Finset.univ : Finset (KernelProjectionPresentPivot code)).toList
      let hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule := by
        rw [D.filtration.terminal]; exact bot_le
      ∃ n : ℕ, n ≤ d ∧ ∃ Q : RationalFilteredNilmanifold (L ⧸ ideal) s n,
        Q.filtration = D.filtration.quotientLie ideal hI ∧
        Q.lattice = D.lattice.map (D.filtration.quotientStepHom ideal hI) ∧
        Q.GeometryComplexityLE ((p + 2) ^ C) ∧
        ∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap ideal (D.basis j)) i) ≤
          (p + 2) ^ C := by
  obtain ⟨a, _ha, hspan⟩ := exists_nativeTopMarkKernel_spanning_budget
  obtain ⟨bexp, _hb, hquotient⟩ := exists_controlled_frequency_quotient_budget
  let X : Polynomial ℕ := Polynomial.X
  let q := X + (X + 2) ^ a + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget ((q + 2) ^ bexp)
  refine ⟨C, hC, ?_⟩
  intro L M J _ _ _ _ s d e r D b φ eta code p hs hp hD he hr hφ heta ideal hI
  let P := D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap
  obtain ⟨vP, hvP, hvPH⟩ := hspan D b φ p hs hp hD he hφ
  let p₀ := p + (p + 2) ^ a + 1
  have hpa : 0 ≤ (p + 2) ^ a := by positivity
  have hp₀ : 0 ≤ p₀ := by dsimp [p₀]; positivity
  have hpp₀ : p ≤ p₀ := by dsimp [p₀]; linarith
  have hap₀ : (p + 2) ^ a ≤ p₀ := by dsimp [p₀]; linarith
  have hbudget' : (p₀ + 2) ^ bexp ≤ (p + 2) ^ C := by
    simpa [X, q, p₀, Polynomial.eval₂_pow] using hbudget p hp
  have hresult := hquotient D hs P inf_le_left vP hvP eta code p₀ hp₀
    (hD.mono D hpp₀) (hr.trans hpp₀)
    (fun i j => (hvPH i j).trans hap₀) (fun i j => (heta i j).trans hpp₀)
  let K := frequencyCodeKernel P eta code
  let hK : K ≤ D.filtration.layer s := (finiteFrequencyKernel_le P _ _).trans inf_le_left
  let I := D.filtration.topSubspaceIdeal K hK
  have hIdeal : ideal = I := D.filtration.pivotAnnihilatorIdeal_presentPivots φ eta code hK
  revert hI
  rw [hIdeal]
  intro hI
  obtain ⟨n, hn, Q, hQF, hQL, hQ, hmap⟩ := hresult
  exact ⟨n, hn, Q, hQF, hQL, hQ.mono Q hbudget', fun i j => (hmap j i).trans hbudget'⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedJointWeightedReferenceComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem selectedJointFiniteLaw_weighted_reference_comparison
    {B K I : Type*} [Fintype K] [Fintype I]
    (A : Finset B) (hA : A.Nonempty)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (D : B → (K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass A modulus T V D)
    (f : B → (K × I → ℤ) → ℂ) (hf : ∀ a z, ‖f a z‖ ≤ 1)
    {ε η : ℝ}
    (hmass : ∀ a, |selectedResidueDensityMass modulus T V (D a) - 1| ≤ η)
    (htest : ∀ a,
      ‖(∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) *
          (f a z * (D a z : ℂ))) -
        ∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) * f a z‖ ≤ ε) :
    ‖(selectedJointFiniteLaw A hA modulus T V hV hZ D hD0 hD).complexMean
        (fun z => f z.1.val z.2.val) -
      (selectedJointReference A hA modulus T V hV hZ).complexMean
        (fun z => f z.1.val z.2.val)‖ ≤ η + ε := by
  let p := FiniteProbabilityWeights.uniformFinset A hA
  let q := selectedResidueFiniteLaw modulus T V hV hZ
  let test (z : A × rectangularWeightIndices 0 V 1) := f z.1.val z.2.val
  let density (z : A × rectangularWeightIndices 0 V 1) := D z.1.val z.2.val
  have hraw := p.norm_complexMean_sub_le
    (fun a => q.complexMean (fun z => (D a.val z.val : ℂ) * f a.val z.val))
    (fun a => q.complexMean (fun z => f a.val z.val)) (fun _ => ε) (by
      intro a _
      change ‖(selectedResidueFiniteLaw modulus T V hV hZ).complexMean
          (fun z => (D a.val z.val : ℂ) * f a.val z.val) -
        (selectedResidueFiniteLaw modulus T V hV hZ).complexMean
          (fun z => f a.val z.val)‖ ≤ ε
      rw [selectedResidueFiniteLaw_complexMean modulus T V hV hZ
          (fun z => (D a.val z : ℂ) * f a.val z),
        selectedResidueFiniteLaw_complexMean modulus T V hV hZ (f a.val)]
      simpa only [mul_comm (D a.val _ : ℂ)] using htest a.val)
  rw [p.mean_const] at hraw
  have hraw' : ‖(p.prod q).complexMean (fun z => (density z : ℂ) * test z) -
      (p.prod q).complexMean test‖ ≤ ε := by
    simpa only [FiniteProbabilityWeights.complexMean_prod, density, test] using hraw
  have hglobal : 0 < (selectedJointReference A hA modulus T V hV hZ).mean density := by
    rw [selectedJointReference_densityMass]
    exact hD
  have hnorm := (selectedJointReference A hA modulus T V hV hZ).normalizedDensityTest_remove_normalization
    density (fun z => hD0 z.1.val z.2.val) hglobal test (fun z => hf z.1.val z.2.val)
  rw [selectedJointReference_densityMass] at hnorm
  have hnorm' := hnorm.trans (selectedJointDensityMass_close A hA modulus T V D hmass)
  rw [selectedJointFiniteLaw_complexMean]
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hnorm' hraw')

theorem selectedJointFiniteLaw_weighted_reference_real_comparison
    {B K I : Type*} [Fintype K] [Fintype I]
    (A : Finset B) (hA : A.Nonempty)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (D : B → (K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass A modulus T V D)
    (f : B → (K × I → ℤ) → ℝ) (hf : ∀ a z, |f a z| ≤ 1)
    {ε η : ℝ}
    (hmass : ∀ a, |selectedResidueDensityMass modulus T V (D a) - 1| ≤ η)
    (htest : ∀ a,
      |(∑' z, (selectedResidueSmoothPMF modulus T V hV hZ z).toReal * (f a z * D a z)) -
        ∑' z, (selectedResidueSmoothPMF modulus T V hV hZ z).toReal * f a z| ≤ ε) :
    |(selectedJointFiniteLaw A hA modulus T V hV hZ D hD0 hD).mean
        (fun z => f z.1.val z.2.val) -
      (selectedJointReference A hA modulus T V hV hZ).mean
        (fun z => f z.1.val z.2.val)| ≤ η + ε := by
  have h := selectedJointFiniteLaw_weighted_reference_comparison A hA modulus T V hV hZ
    D hD0 hD (fun a z => (f a z : ℂ))
    (fun a z => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hf a z)
    hmass (fun a => by
      simpa only [← Complex.ofReal_mul, ← Complex.ofReal_tsum, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs] using htest a)
  simpa only [FiniteProbabilityWeights.complexMean_ofReal, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PreparedCoefficientTorusCompact
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem PreparedHeights.euclideanLayerTorus_compact
    {p : ℝ} {R : ℕ} (hL : L.PreparedHeights p R)
    (hp : 0 ≤ p) (hR : 1 ≤ R) (j : Fin m) :
    CompactSpace (euclideanSubspace (L j).space ⧸
      (latticeSection (standardEuclideanLattice (L j).Coord)
        (euclideanSubspace (L j).space)).toAddSubgroup) := by
  let Λ := latticeSection (standardEuclideanLattice (L j).Coord)
    (euclideanSubspace (L j).space)
  let : IsZLattice ℝ Λ := hL.lattice_full L hp hR j
  have hc := IsZLattice.isCompact_range_of_periodic Λ
    (QuotientAddGroup.mk' Λ.toAddSubgroup)
    (QuotientAddGroup.isQuotientMap_mk Λ.toAddSubgroup).continuous (by
      intro x z hz
      rw [map_add]
      have hz0 : QuotientAddGroup.mk' Λ.toAddSubgroup z = 0 :=
        (QuotientAddGroup.eq_zero_iff z).mpr hz
      rw [hz0, add_zero])
  rw [Set.range_eq_univ.mpr (QuotientAddGroup.mk'_surjective Λ.toAddSubgroup)] at hc
  exact ⟨hc⟩

end Erdos3.RankPreparationFamily

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueCutoffDomination
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {K I : Type*} [Fintype K] [Fintype I]
variable (q : I → ℕ) (T : Finset (ColumnResiduePattern K I q))
variable (V : K × I → ℝ)

theorem selectedResidueSmoothWeight_normalized_norm_le (z : K × I → ℤ)
    (hz : selectedResidueSmoothWeight q T V z ≠ 0) :
    ‖fun t => (z t : ℝ) / V t‖ ≤ 1 := by
  by_contra! hn
  have hp := smoothProductProfile_zero_outside (K × I) (fun t => (z t : ℝ) / V t) hn
  exact hz (by simp [selectedResidueSmoothWeight, hp])

theorem selectedResidueFiniteLaw_normalized_norm_le (hV : ∀ t, 0 < V t)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (z : rectangularWeightIndices 0 V 1)
    (hz : 0 < (selectedResidueFiniteLaw q T V hV hZ).weight z) :
    ‖fun t => (z.val t : ℝ) / V t‖ ≤ 1 := by
  apply selectedResidueSmoothWeight_normalized_norm_le q T V z.val
  intro he
  change 0 < selectedResidueSmoothWeight q T V z.val /
    (∑' x, selectedResidueSmoothWeight q T V x) at hz
  rw [he, zero_div] at hz
  exact (lt_irrefl 0) hz

theorem selectedJointFiniteLaw_normalized_norm_le {A : Type*}
    (bases : Finset A) (hbases : bases.Nonempty) (hV : ∀ t, 0 < V t)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (D : A → (K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass bases q T V D)
    (z : bases × rectangularWeightIndices 0 V 1)
    (hz : 0 < (selectedJointFiniteLaw bases hbases q T V hV hZ D hD0 hD).weight z) :
    ‖fun t => (z.2.val t : ℝ) / V t‖ ≤ 1 := by
  apply selectedResidueSmoothWeight_normalized_norm_le q T V z.2.val
  intro he
  rw [selectedJointFiniteLaw_weight, selectedResidueSmoothPMF_toReal, he, zero_div,
    mul_zero, zero_mul, zero_div] at hz
  exact (lt_irrefl 0) hz

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

namespace FiniteProbabilityWeights

theorem mean_mono_positive_support {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) {f g : X → ℝ}
    (h : ∀ x, 0 < p.weight x → f x ≤ g x) : p.mean f ≤ p.mean g := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : 0 < p.weight x
  · exact mul_le_mul_of_nonneg_left (h x hx) (p.nonneg x)
  · have hz : p.weight x = 0 := le_antisymm (le_of_not_gt hx) (p.nonneg x)
    simp only [hz, zero_mul, le_refl]

end FiniteProbabilityWeights

variable {K I : Type*} [Fintype K] [Fintype I]
variable (q : I → ℕ) (T : Finset (ColumnResiduePattern K I q))
variable (V : K × I → ℝ) (hV : ∀ t, 0 < V t)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)

theorem selectedResidueFiniteLaw_event_eq_map_true (bad : (K × I → ℤ) → Prop) :
    (selectedResidueFiniteLaw q T V hV hZ).eventProbability (fun z => bad z.val) =
      (((selectedResidueSmoothPMF q T V hV hZ).map (fun z => decide (bad z))) true).toReal := by
  have hoff (z : K × I → ℤ) (hz : z ∉ rectangularWeightIndices 0 V 1) :
      (selectedResidueSmoothPMF q T V hV hZ z).toReal = 0 := by
    rw [selectedResidueSmoothPMF_toReal, selectedResidueSmoothWeight_zero_off q T V hV z hz, zero_div]
  calc
    _ = (FiniteProbabilityWeights.ofSupportedPMF (selectedResidueSmoothPMF q T V hV hZ)
        (rectangularWeightIndices 0 V 1) hoff).eventProbability (fun z => bad z.val) := by
      unfold FiniteProbabilityWeights.eventProbability FiniteProbabilityWeights.mean
      apply Finset.sum_congr rfl
      intro z _
      change selectedResidueSmoothWeight q T V z.val / _ * _ =
        (selectedResidueSmoothPMF q T V hV hZ z.val).toReal * _
      rw [selectedResidueSmoothPMF_toReal]
    _ = _ := supportedPMF_event_eq_map_true _ _ hoff bad

theorem selectedResidueFiniteLaw_cutoff_le_event
    (F : (K × I → ℝ) → ℝ) (bad : (K × I → ℤ) → Prop)
    (hF : ∀ z : K × I → ℤ, ‖fun t => (z t : ℝ) / V t‖ ≤ 1 →
      F (fun t => (z t : ℝ) / V t) ≤ if bad z then 1 else 0) :
    (selectedResidueFiniteLaw q T V hV hZ).mean
        (fun z => F (fun t => (z.val t : ℝ) / V t)) ≤
      (((selectedResidueSmoothPMF q T V hV hZ).map (fun z => decide (bad z))) true).toReal := by
  rw [← selectedResidueFiniteLaw_event_eq_map_true]
  apply FiniteProbabilityWeights.mean_mono_positive_support
  intro z hz
  exact hF z.val (selectedResidueFiniteLaw_normalized_norm_le q T V hV hZ z hz)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SelectedJointSpatialCutoff
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem selectedJointFiniteLaw_spatial_cutoff_bound
    {B K I : Type*} [Fintype K] [Fintype I]
    (bases : Finset B) (hbases : bases.Nonempty)
    (q : I → ℕ) (T : Finset (ColumnResiduePattern K I q))
    (V : K × I → ℝ) (hV : ∀ t, 0 < V t)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (D : B → (K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass bases q T V D)
    (F : (K × I → ℝ) → ℝ) (hF : ∀ x, F x ∈ Set.Icc (0 : ℝ) 1)
    (small large : (K × I → ℤ) → Prop)
    (hcut : ∀ z, ‖fun t => (z t : ℝ) / V t‖ ≤ 1 →
      (if small z then (1 : ℝ) else 0) ≤ F (fun t => (z t : ℝ) / V t) ∧
      F (fun t => (z t : ℝ) / V t) ≤ if large z then 1 else 0)
    {ε η δ : ℝ}
    (hprior : (((selectedResidueSmoothPMF q T V hV hZ).map
      (fun z => decide (large z))) true).toReal ≤ δ)
    (hmass : ∀ a, |selectedResidueDensityMass q T V (D a) - 1| ≤ η)
    (htest : ∀ a,
      |(∑' z, (selectedResidueSmoothPMF q T V hV hZ z).toReal *
        (F (fun t => (z t : ℝ) / V t) * D a z)) -
        ∑' z, (selectedResidueSmoothPMF q T V hV hZ z).toReal *
          F (fun t => (z t : ℝ) / V t)| ≤ ε) :
    (selectedJointFiniteLaw bases hbases q T V hV hZ D hD0 hD).mean
      (fun z => if small z.2.val then (1 : ℝ) else 0) ≤ δ + (η + ε) := by
  have hdom := FiniteProbabilityWeights.mean_mono_positive_support
    (selectedJointFiniteLaw bases hbases q T V hV hZ D hD0 hD)
    (f := fun z => if small z.2.val then (1 : ℝ) else 0)
    (g := fun z => F (fun t => (z.2.val t : ℝ) / V t))
    (fun z hz => (hcut z.2.val
      (selectedJointFiniteLaw_normalized_norm_le q T V bases hbases hV hZ D hD0 hD z hz)).1)
  have hcmp := selectedJointFiniteLaw_weighted_reference_real_comparison
    bases hbases q T V hV hZ D hD0 hD
    (fun _ z => F (fun t => (z t : ℝ) / V t))
    (fun _ z => by rw [abs_of_nonneg (hF _).1]; exact (hF _).2) hmass htest
  have href : (selectedJointReference bases hbases q T V hV hZ).mean
      (fun z => F (fun t => (z.2.val t : ℝ) / V t)) =
      (selectedResidueFiniteLaw q T V hV hZ).mean
        (fun z => F (fun t => (z.val t : ℝ) / V t)) := by
    change ((FiniteProbabilityWeights.uniformFinset bases hbases).prod
      (selectedResidueFiniteLaw q T V hV hZ)).mean _ = _
    rw [FiniteProbabilityWeights.mean_prod]
    dsimp only
    rw [FiniteProbabilityWeights.mean_const]
  rw [href] at hcmp
  have hp := (selectedResidueFiniteLaw_cutoff_le_event q T V hV hZ F large
    (fun z hz => (hcut z hz).2)).trans hprior
  linarith [(abs_le.mp hcmp).2]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineScaleEnvelope
namespace OAI

section

namespace Erdos3

noncomputable def affineReferenceCoefficientLog {A : Type*} [Semiring A] (D L : A) : A :=
  8 * (D + 1) * (L + 1)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

def allocatedAffineL1Log {A : Type*} [Semiring A] (m : ℕ) (D P Prho Pk : A) : A :=
  P + ((m * 2 ^ (m + 1) : ℕ) * Pk + allocatedDensityEnvelope m D P) +
    allocatedSupportEnvelope m D P + allocatedIdealLipEnvelope D P Prho +
    ((m + 1 : ℕ) * D + 2) + scalarCubeRiemannLog D

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

theorem exists_allocatedAffineL1Log_bound (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ D P Prho Pk : ℝ,
      0 ≤ D → 0 ≤ P → 0 ≤ Prho → 0 ≤ Pk →
      allocatedAffineL1Log m D P Prho Pk ≤ (D + P + Prho + Pk + A) ^ A := by
  let X : Polynomial ℕ := Polynomial.X
  let poly := allocatedAffineL1Log m X X X X
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro D P Prho Pk hD hP hPrho hPk
  let Q := D + P + Prho + Pk
  have hQ : 0 ≤ Q := by dsimp [Q]; linarith
  have hDQ : D ≤ Q := by dsimp [Q]; linarith
  have hPQ : P ≤ Q := by dsimp [Q]; linarith
  have hrQ : Prho ≤ Q := by dsimp [Q]; linarith
  have hkQ : Pk ≤ Q := by dsimp [Q]; linarith
  have hkernel : kernelOutputEnvelope D (4 * (P + 8)) ≤ kernelOutputEnvelope Q (4 * (Q + 8)) := by
    unfold kernelOutputEnvelope kernelGeometryEnvelope kernelInverseEnvelope
    gcongr
  have hden : allocatedDensityEnvelope m D P ≤ allocatedDensityEnvelope m Q Q := by
    unfold allocatedDensityEnvelope
    gcongr
  have hsupp : allocatedSupportEnvelope m D P ≤ allocatedSupportEnvelope m Q Q := by
    unfold allocatedSupportEnvelope
    gcongr
  have hmono : allocatedAffineL1Log m D P Prho Pk ≤ allocatedAffineL1Log m Q Q Q Q := by
    unfold allocatedAffineL1Log allocatedIdealLipEnvelope scalarCubeRiemannLog
    gcongr
  apply hmono.trans
  simpa [poly, X, allocatedAffineL1Log, allocatedDensityEnvelope, allocatedSupportEnvelope,
    allocatedIdealLipEnvelope, scalarCubeRiemannLog, kernelOutputEnvelope,
    kernelGeometryEnvelope, kernelInverseEnvelope, Polynomial.eval₂_pow, Nat.cast_add, Nat.cast_mul]
    using hbound Q hQ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

noncomputable def allocatedAffineCoefficientAccuracyLog {A : Type*} [Semiring A]
    (m : ℕ) (D P Prho Pk target : A) : A :=
  target + 1 + coefficientReplacementErrorLog D (allocatedAffineL1Log m D P Prho Pk)

noncomputable def allocatedAffineReferenceAccuracyLog {A : Type*} [Semiring A]
    (m : ℕ) (D P Prho Pk target : A) : A :=
  target + 1 + affineReferenceCoefficientLog D (allocatedAffineL1Log m D P Prho Pk) + 4

noncomputable def allocatedAffineLengthLog {A : Type*} [Semiring A]
    (m : ℕ) (D P Prho Pk target F T : A) : A :=
  m * allocatedFrontEnvelope m D P (allocatedAffineCoefficientAccuracyLog m D P Prho Pk target) +
    progressionSliceLengthLog D (allocatedAffineReferenceAccuracyLog m D P Prho Pk target) F T

 theorem allocatedAffineL1Log_nonneg (m : ℕ) {D P Prho Pk : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hr : 0 ≤ Prho) (hk : 0 ≤ Pk) :
    0 ≤ allocatedAffineL1Log m D P Prho Pk := by
  have hd := allocatedDensityEnvelope_nonneg m hD hP
  have hs := allocatedSupportEnvelope_nonneg m hD hP
  dsimp only [allocatedAffineL1Log, allocatedIdealLipEnvelope, scalarCubeRiemannLog]
  positivity

 theorem allocatedAffineLengthLog_bounds (m : ℕ) {D P Prho Pk target F T : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hr : 0 ≤ Prho) (hk : 0 ≤ Pk)
    (ht : 0 ≤ target) (hF : 0 ≤ F) (hT : 0 ≤ T) :
    let e := allocatedAffineCoefficientAccuracyLog m D P Prho Pk target
    let E := allocatedAffineReferenceAccuracyLog m D P Prho Pk target
    let L := allocatedAffineLengthLog m D P Prho Pk target F T
    0 ≤ e ∧ 0 ≤ E ∧ 0 ≤ L ∧ E ≤ L ∧
      (m : ℝ) * allocatedFrontEnvelope m D P e ≤ L ∧
      progressionSliceLengthLog D E F T ≤ L := by
  intro e E L
  have hb := allocatedAffineL1Log_nonneg m hD hP hr hk
  have he : 0 ≤ e := by dsimp [e, allocatedAffineCoefficientAccuracyLog, coefficientReplacementErrorLog]; positivity
  have hE : 0 ≤ E := by dsimp [E, allocatedAffineReferenceAccuracyLog, affineReferenceCoefficientLog]; positivity
  have hki := kernelInverseEnvelope_nonneg hD hP
  have hf : 0 ≤ (m : ℝ) * allocatedFrontEnvelope m D P e := by
    dsimp [allocatedFrontEnvelope, allocatedKernelEnvelope]; positivity
  have hs : 0 ≤ progressionSliceLengthLog D E F T := by
    dsimp [progressionSliceLengthLog, scalarCubeRiemannLog]; positivity
  have hEL : E ≤ progressionSliceLengthLog D E F T := by
    have hB : 0 ≤ scalarCubeRiemannLog D := by unfold scalarCubeRiemannLog; positivity
    dsimp only [progressionSliceLengthLog]; linarith
  refine ⟨he, hE, add_nonneg hf hs, ?_, le_add_of_nonneg_right hs, le_add_of_nonneg_left hf⟩
  exact hEL.trans (le_add_of_nonneg_left hf)

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

noncomputable def allocatedAffineScale (D P Prho Pk target F T : ℝ) :
    LayerSamplerScale (G := G) B U basis R σ :=
  selectedLayerSamplerScale B U basis R σ hR hσ
    ⌈Real.exp (allocatedAffineLengthLog m D P Prho Pk target F T)⌉₊

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedAffineScalePolynomial {A : Type*} [Semiring A]
    (m : ℕ) (D P Lb target F T : A) : A :=
  let e := target + 1 + coefficientReplacementErrorLog D Lb
  let E := target + 1 + affineReferenceCoefficientLog D Lb + 4
  let Q := D + P + (m * allocatedFrontEnvelope m D P e + progressionSliceLengthLog D E F T) + 1
  (1 + Q ^ 2) * (5 * Q + 49)

 theorem exists_allocatedAffineScaleLog_bound (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ D P Prho Pk target F T : ℝ,
      0 ≤ D → 0 ≤ P → 0 ≤ Prho → 0 ≤ Pk → 0 ≤ target → 0 ≤ F → 0 ≤ T →
      allocatedScaleLog (D + P + allocatedAffineLengthLog m D P Prho Pk target F T + 1) ≤
        (D + P + Prho + Pk + target + F + T + A) ^ A := by
  obtain ⟨b, hb, hLb⟩ := exists_allocatedAffineL1Log_bound m
  let X : Polynomial ℕ := Polynomial.X
  let poly := allocatedAffineScalePolynomial m X X ((X + Polynomial.C b) ^ b) X X X
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro D P Prho Pk target F T hD hP hr hk ht hF hT
  let Q := D + P + Prho + Pk + target + F + T
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hDQ : D ≤ Q := by dsimp [Q]; linarith
  have hPQ : P ≤ Q := by dsimp [Q]; linarith
  have htQ : target ≤ Q := by dsimp [Q]; linarith
  have hFQ : F ≤ Q := by dsimp [Q]; linarith
  have hTQ : T ≤ Q := by dsimp [Q]; linarith
  have hl0 := allocatedAffineL1Log_nonneg m hD hP hr hk
  have hl : allocatedAffineL1Log m D P Prho Pk ≤ (Q + b) ^ b := by
    apply (hLb D P Prho Pk hD hP hr hk).trans
    apply pow_le_pow_left₀ (by positivity)
    dsimp [Q]; linarith
  have he : allocatedAffineCoefficientAccuracyLog m D P Prho Pk target ≤
      Q + 1 + coefficientReplacementErrorLog Q ((Q + b) ^ b) := by
    dsimp only [allocatedAffineCoefficientAccuracyLog, coefficientReplacementErrorLog]
    gcongr
  have hE : allocatedAffineReferenceAccuracyLog m D P Prho Pk target ≤
      Q + 1 + affineReferenceCoefficientLog Q ((Q + b) ^ b) + 4 := by
    dsimp only [allocatedAffineReferenceAccuracyLog, affineReferenceCoefficientLog]
    gcongr
  have hi : kernelInverseEnvelope D P ≤ kernelInverseEnvelope Q Q := by
    unfold kernelInverseEnvelope
    gcongr
  have hfront : allocatedFrontEnvelope m D P (allocatedAffineCoefficientAccuracyLog m D P Prho Pk target) ≤
      allocatedFrontEnvelope m Q Q (Q + 1 + coefficientReplacementErrorLog Q ((Q + b) ^ b)) := by
    have hki := kernelInverseEnvelope_nonneg hD hP
    dsimp only [allocatedFrontEnvelope, allocatedKernelEnvelope]
    gcongr
  have hslice : progressionSliceLengthLog D (allocatedAffineReferenceAccuracyLog m D P Prho Pk target) F T ≤
      progressionSliceLengthLog Q (Q + 1 + affineReferenceCoefficientLog Q ((Q + b) ^ b) + 4) Q Q := by
    dsimp only [progressionSliceLengthLog, scalarCubeRiemannLog]
    gcongr
  have hL0 := (allocatedAffineLengthLog_bounds m hD hP hr hk ht hF hT).2.2.1
  have hL : allocatedAffineLengthLog m D P Prho Pk target F T ≤
      (m : ℝ) * allocatedFrontEnvelope m Q Q (Q + 1 + coefficientReplacementErrorLog Q ((Q + b) ^ b)) +
        progressionSliceLengthLog Q (Q + 1 + affineReferenceCoefficientLog Q ((Q + b) ^ b) + 4) Q Q := by
    exact add_le_add (mul_le_mul_of_nonneg_left hfront (Nat.cast_nonneg _)) hslice
  have hmono : allocatedScaleLog (D + P + allocatedAffineLengthLog m D P Prho Pk target F T + 1) ≤
      allocatedAffineScalePolynomial m Q Q ((Q + b) ^ b) Q Q Q := by
    dsimp only [allocatedScaleLog, allocatedAffineScalePolynomial]
    gcongr
  apply hmono.trans
  simpa [poly, X, allocatedAffineScalePolynomial, allocatedFrontEnvelope, allocatedKernelEnvelope,
    kernelInverseEnvelope, kernelGeometryEnvelope, coefficientReplacementErrorLog,
    affineReferenceCoefficientLog, progressionSliceLengthLog, scalarCubeRiemannLog,
    Polynomial.eval₂_pow] using hbound Q hQ

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FrozenMarkedRightOrbitGrid
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_frozenMarkedRightOrbit_grid_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ ι κ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [DecidableEq κ]
        [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
        {t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
        (b : Basis ι ℚ L) (c : Basis κ ℚ M) (w : σ → ℕ) (S : M →ₗ[ℚ] L)
        (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j) (H : ℕ) (p : ℝ),
        0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
        (∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H) →
        ∀ q r : ℕ, 0 < q → 0 < r →
          ((matrixDenominator (LinearMap.toMatrix c b S) * q * r : ℕ) : ℝ) ≤ Real.exp p →
          ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
            matrixDenominator (LinearMap.toMatrix c b S) * q * r ∣ m ∧
            ∀ marked : G.realification.PolynomialOrbit w,
              CoefficientGrid (c.baseChange ℝ) q marked.log →
              ∀ center : F.realification.Group,
                (b.baseChange ℝ).equivFun center.coord ∈ realDenominatorGrid r →
                ∀ x : σ → ℤ,
                  (b.baseChange ℝ).equivFun
                    (F.realification.polynomialOrbitEval w x
                      (F.frozenMarkedRightOrbit G w S hS marked center)).coord ∈
                    realDenominatorGrid m := by
  obtain ⟨C, hC, hclosure⟩ := exists_real_bch_rational_closure s
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L M _ _ _ _ _ _ _ _ t F G b c w S hS H p hp hd hH hb q r hq hr hlp
  have hDq : 0 < matrixDenominator (LinearMap.toMatrix c b S) * q :=
    Nat.mul_pos (matrixDenominator_pos _) hq
  obtain ⟨m, hm, hmp, hlm, hmul, _⟩ :=
    hclosure b H p F.lowerCentralSeries_eq_bot hp hd hH hb
      (matrixDenominator (LinearMap.toMatrix c b S) * q * r)
      (Nat.mul_pos hDq hr) hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro marked hmarked center hcenter x
  rw [← polynomialOrbitRealEval_integer, frozenMarkedRightOrbit_realEval,
    polynomialOrbitRealEval_integer]
  apply hmul
  · exact realDenominatorGrid_subset_of_dvd hDq (dvd_mul_right _ _)
      (realified_linear_coordinate_grid c b S q _
        (G.polynomialOrbit_coefficient_grid_value c w q marked hmarked x))
  · exact realDenominatorGrid_subset_of_dvd hr (dvd_mul_left _ _) hcenter

end Erdos3.NilpotentLieFiltration

end

end OAI

end


