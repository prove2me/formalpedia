-- Prove2me | Definitions.Def_OAIErdos3B190
-- name    : OAIErdos3B190
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T08:32:08.412899+00:00
-- url     : https://prove2.me/theorems/5ab0ab80-cb89-4ffc-a2da-3a644e2dcf5d
-- title:
--   OpenAI Erdős-3 split, definitions bundle 191 of 204
-- statement:
--   Definitions bundle 191 of 204 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B189`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 191 available.
--
--   Modules: `OAI.Erdos3.MarkedShiftGeneratorIndex`, `OAI.Erdos3.MarkedShiftQuotient`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.dependentWordLayer_top_le_ker`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.dependent_word_frequency_zero`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.exists_dependentQuotient_integral_model`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.top_inter_dependentWordIdeal_le_ker`, `OAI.Erdos3.NativeRankRelation.CommonData.DependentQuotient`, `OAI.Erdos3.NativeRankRelation.CommonData.coefficientFreeSpan_le_dependentWordLayer`, `OAI.Erdos3.NativeRankRelation.CommonData.dependentPolynomialLayer`, `OAI.Erdos3.NativeRankRelation.CommonData.dependentQuotientFiltration`, `OAI.Erdos3.NativeRankRelation.CommonData.dependentQuotientMap`, `OAI.Erdos3.NativeRankRelation.CommonData.dependentQuotientMap_mem_layer`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_controlled_shared_free_equations`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_controlled_shared_free_refinement`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_correlation_refined_annihilator`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_correlation_refined_basis`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_native_full_coefficient_corrections`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_uniform_dependentQuotient_comparison`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_uniform_shared_refinement`, `OAI.Erdos3.NativeRankRelation.CommonData.markedQuotientMultidegree`, `OAI.Erdos3.NativeRankRelation.CommonData.native_full_scaled_correction`, `OAI.Erdos3.NativeRankRelation.CommonData.native_shared_scaled_correction`, `OAI.Erdos3.NativeRankRelation.CommonData.top_inter_dependentWordIdeal`, `OAI.Erdos3.exists_markedLieSpan_bounded_basis`, `OAI.Erdos3.exists_sharedFreeRecoveryThreshold_bound`, `OAI.Erdos3.exists_zero_phase_lift`, `OAI.Erdos3.finiteMarkedLieValues`, `OAI.Erdos3.finiteMarkedLieValues_coordinate_height`, `OAI.Erdos3.finiteMarkedLieValues_mem`, `OAI.Erdos3.finiteMarkedPolynomialValues`, `OAI.Erdos3.finiteMarkedPolynomialValues_coefficient_height`, `OAI.Erdos3.finiteMarkedPolynomialValues_mem`, `OAI.Erdos3.markedBaseEvaluation`, `OAI.Erdos3.markedBaseEvaluationLie`, `OAI.Erdos3.markedBaseEvaluation_lie`, `OAI.Erdos3.markedBaseEvaluation_map`, `OAI.Erdos3.markedBaseEvaluation_real_incl`, `OAI.Erdos3.markedBaseEvaluation_real_map`, `OAI.Erdos3.markedBaseEvaluation_zero_coordinate_height`, `OAI.Erdos3.markedDirection_mem_realLattice_of_smul`, `OAI.Erdos3.markedEvaluationHeight`, `OAI.Erdos3.markedLieSpan_degree_zero_eq_one`, `OAI.Erdos3.markedLieSpan_eq_finite_span`, `OAI.Erdos3.markedLieSpan_le_markedDegree`, `OAI.Erdos3.markedParameterExponents`, `OAI.Erdos3.markedPolynomialAlgebra`, `OAI.Erdos3.markedPolynomialAlgebra_le_adapted`, `OAI.Erdos3.markedPolynomialGeneratorFamily`, `OAI.Erdos3.markedPolynomialGeneratorFamily_span`, `OAI.Erdos3.markedPolynomialLayer`, `OAI.Erdos3.markedPolynomialLayer_antitone`, `OAI.Erdos3.markedPolynomialLayer_degreeLE`, `OAI.Erdos3.markedPolynomialLayer_degree_terminal`, `OAI.Erdos3.markedPolynomialLayer_degree_zero_eq_one`, `OAI.Erdos3.markedPolynomialLayer_directionalDerivative`, `OAI.Erdos3.markedPolynomialLayer_eq_finite_span`, `OAI.Erdos3.markedPolynomialLayer_eval_mem`, `OAI.Erdos3.markedPolynomialLayer_lie_mem`, `OAI.Erdos3.markedPolynomialLayer_shiftDerivative`, `OAI.Erdos3.markedPolynomialLayer_taylorRemainder`, `OAI.Erdos3.markedPolynomialLayer_translate`, `OAI.Erdos3.markedPureEvaluation`, `OAI.Erdos3.markedPureEvaluationHom`, `OAI.Erdos3.markedPureEvaluationHom_lattice`, `OAI.Erdos3.markedPureEvaluation_inclusion`, `OAI.Erdos3.markedPureSpaceMap`, `OAI.Erdos3.markedQuotientDirection`, `OAI.Erdos3.markedQuotientDirectionLinear`, `OAI.Erdos3.markedQuotientDirection_coordinate_height`, `OAI.Erdos3.markedQuotientDirection_mem_first`, `OAI.Erdos3.markedQuotientDirection_smul`, `OAI.Erdos3.markedQuotientHeight`, `OAI.Erdos3.markedQuotientPhase`, `OAI.Erdos3.markedQuotientPhase_coordinate_height`, `OAI.Erdos3.markedQuotientPhase_direction`, `OAI.Erdos3.markedQuotientPolynomialAlgebra`, `OAI.Erdos3.markedQuotientTranslate`, `OAI.Erdos3.markedQuotientTranslate_first_order`, `OAI.Erdos3.markedShiftBasis_structure_height`, `OAI.Erdos3.markedShiftBiLayer`, `OAI.Erdos3.markedShiftBiLayer_antitone`, `OAI.Erdos3.markedShiftBiLayer_degree_terminal`, `OAI.Erdos3.markedShiftBiLayer_eq_polynomialSubmodule`, `OAI.Erdos3.markedShiftBiLayer_lie_mem`, `OAI.Erdos3.markedShiftBiLayer_positive`, `OAI.Erdos3.markedShiftBiLayer_second`, `OAI.Erdos3.markedShiftBiLayer_zero`, `OAI.Erdos3.markedShiftDirection`, `OAI.Erdos3.markedShiftDirectionLinear`, `OAI.Erdos3.markedShiftDirectionMap`, `OAI.Erdos3.markedShiftDirection_ambient_height`, `OAI.Erdos3.markedShiftDirection_coordinate_height`, `OAI.Erdos3.markedShiftDirection_lie_left`, `OAI.Erdos3.markedShiftDirection_lie_right`, `OAI.Erdos3.markedShiftEval`, `OAI.Erdos3.markedShiftEval_lie_of_zero_phase`, `OAI.Erdos3.markedShiftEval_translate`, `OAI.Erdos3.markedShiftEval_zero_coordinate_height`, `OAI.Erdos3.markedShiftGenerator`, `OAI.Erdos3.markedShiftGenerator_coordinate_height`, `OAI.Erdos3.markedShiftGenerator_mem`, `OAI.Erdos3.markedShiftGenerator_span`, `OAI.Erdos3.markedShiftLayerPolynomialMap`, `OAI.Erdos3.markedShiftMultidegree`, `OAI.Erdos3.markedShiftMultidegree_layer`, `OAI.Erdos3.markedShiftPhase`, `OAI.Erdos3.markedShiftPhase_coordinate_height`, `OAI.Erdos3.markedShiftPolynomialSubmodule`, `OAI.Erdos3.markedShiftQuotientLayer`, `OAI.Erdos3.markedShiftQuotientLayer_antitone`, `OAI.Erdos3.markedShiftQuotientLayer_eq_bot_of_le`, `OAI.Erdos3.markedShiftQuotientLayer_lie_mem`, `OAI.Erdos3.markedShiftQuotientLayer_positive`, `OAI.Erdos3.markedShiftQuotientLayer_terminal`, `OAI.Erdos3.markedShiftQuotientLayer_total_one`, `OAI.Erdos3.markedShiftQuotientLayer_zero`, `OAI.Erdos3.markedShiftSecondIdeal`, `OAI.Erdos3.markedShiftSubalgebra`, `OAI.Erdos3.markedShiftSubalgebra_contains_direction`, `OAI.Erdos3.markedShiftTranslate`, `OAI.Erdos3.markedShiftTranslate_first_order`, `OAI.Erdos3.markedShiftTranslate_quotient`, `OAI.Erdos3.markedShiftTranslate_second_mem`, `OAI.Erdos3.marked_first_layer_bracket_zero`, `OAI.Erdos3.mem_markedParameterExponents`, `OAI.Erdos3.mixedCorrelationDegree_sum`, `OAI.Erdos3.monoidHomOfSurjectiveComposition`, `OAI.Erdos3.monomial_mem_markedPolynomialLayer`, `OAI.Erdos3.monomial_mem_span_finiteMarkedPolynomialValues`, `OAI.Erdos3.normalizedMarkedPhase`, `OAI.Erdos3.normalizedMarkedPhase_apply`, `OAI.Erdos3.normalizedMarkedPhase_height`, `OAI.Erdos3.normalizedMarkedPhase_scaled_direction`, `OAI.Erdos3.rationalLogHeight_nat_inv_mul_exp_bound`, `OAI.Erdos3.rationalMarkedDirectionMap`, `OAI.Erdos3.rationalMarkedDirectionMap_apply`, `OAI.Erdos3.realMarkedDirection`, `OAI.Erdos3.realMarkedDirection_mem_first`, `OAI.Erdos3.realMarkedParameterDirection`, `OAI.Erdos3.realMarkedParameterDirection_apply`, `OAI.Erdos3.realMarkedParameterDirection_double_lie`, `OAI.Erdos3.realMarkedParameterDirection_lie`, `OAI.Erdos3.realMarkedParameterDirection_mem_first`, `OAI.Erdos3.realMarkedParameterDirection_rat`, `OAI.Erdos3.realMarkedParameterElement`, `OAI.Erdos3.realMarkedParameterElement_conjugation`, `OAI.Erdos3.realMarkedParameterElement_inv`, `OAI.Erdos3.realMarkedParameterElement_mul`, `OAI.Erdos3.realMarkedShiftEval_translate`, `OAI.Erdos3.realMarkedTranslate_first_order`, `OAI.Erdos3.realMarkedTranslate_quotient`, `OAI.Erdos3.sharedFreeEquationInputBudget`, `OAI.Erdos3.sharedFreeEquationInputBudget_bounds`, `OAI.Erdos3.sharedFreeRecoveryThreshold`, `OAI.Erdos3.sharedFreeRecoveryThreshold_spec`, `OAI.Erdos3.sharedFree_rounding_small`, `OAI.Erdos3.sharedLogCoefficientTuple`, `OAI.Erdos3.sharedLogCoefficientTuple_annihilator_decomposition`, `OAI.Erdos3.sharedLogCoefficientTuple_mem_common`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B191

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeRoundingThreshold
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem exists_native_full_coefficient_corrections (hs : 1 ≤ s) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ D.quadruples) :
    let I := R.interval ⟨t, D.subset ht⟩
    let V : I.SunflowerWitness P := D.witness t ht
    ∃ E Q : ∀ α : Unit →₀ ℕ,
        (W.rank.filtration.fourHorizontalLayer (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ,
      (∀ α j, |(W.fourRankBasis.baseChange ℝ).repr (E α).val j| ≤
        Real.exp ((P + 3) ^ 2) / monomialScale (fun _ : Unit => (I.length : ℝ)) α) ∧
      (∀ α, (W.fourRankBasis.baseChange ℝ).equivFun (Q α).val ∈
        realDenominatorGrid V.projectedDenominator) ∧
      ∀ (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s),
        (fun k => coefficients
          (W.orbit (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))).log α) -
          (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) (E α).val -
          (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) (Q α).val ∈
            D.realCoefficientFourSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ := by
  intro I V
  obtain ⟨E, Q, hE, hQ, hres⟩ := D.exists_bounded_coefficient_corrections hs hP t ht
  refine ⟨E, Q, hE, hQ, ?_⟩
  intro α hα
  let d : Fin (s + 1) := ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩
  let e4 := TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)
  let u := e4 (V.projectedOrbitCoefficient α).val
  let β : Fin 4 → ℝ ⊗[ℚ] W.L := fun k => coefficients
    (W.orbit (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))).log α
  let e := e4 (E α).val
  let a := e4 (Q α).val
  have hu : u - e - a ∈ D.realCoefficientFourSpace d := by
    have h := (D.mem_real_coefficientFourSpace d (V.projectedOrbitCoefficient α - E α - Q α)).mpr
      (hres α hα)
    simpa only [Submodule.coe_sub, map_sub] using h
  have hk (k : Fin 4) : (u - e - a) k - (β - e - a) k ∈
      (W.rank.filtration.layer d.val 2).baseChange ℝ := by
    have heq : (u - e - a) k - (β - e - a) k = u k - β k := by
      simp only [Pi.sub_apply]
      abel
    rw [heq]
    exact V.projectedOrbitCoefficient_native_log_mod_kernel hs c τ hG α k
  exact (D.realCoefficientFourSpace_congr_mod_kernel d _ _ hk).mp hu

theorem native_full_scaled_correction (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (l : ℕ) (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator = l)
    (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s)
    (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ D.quadruples) :
    ∃ E Q : ℝ ⊗[ℚ] (Fin 4 → W.L),
      ‖(W.fourRankBasis.baseChange ℝ).equivFun E‖ ≤
        Real.exp ((P + 3) ^ 2 + (s : ℝ) * p) / monomialScale (fun _ : Unit => (N : ℝ)) α ∧
      (W.fourRankBasis.baseChange ℝ).equivFun Q ∈ realDenominatorGrid l ∧
      (fun k => coefficients
        (W.orbit (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))).log α) -
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) E -
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) Q ∈
          D.realCoefficientFourSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ := by
  obtain ⟨E, Q, hE, hQ, hres⟩ := D.exists_native_full_coefficient_corrections hs hP c τ hG t ht
  let I := R.interval ⟨t, D.subset ht⟩
  have hlength : (0 : ℝ) < I.length := by exact_mod_cast I.length_pos
  have hnorm : ‖(W.fourRankBasis.baseChange ℝ).equivFun (E α).val‖ ≤
      Real.exp ((P + 3) ^ 2) / monomialScale (fun _ : Unit => (I.length : ℝ)) α := by
    apply (pi_norm_le_iff_of_nonneg (div_nonneg (Real.exp_pos _).le
      (monomialScale_pos _ (fun _ => hlength) α).le)).mpr
    exact fun j => hE α j
  refine ⟨(E α).val, (Q α).val, ?_, ?_, hres α hα⟩
  · have h := I.norm_bound_on_modulus hp α hα (Real.exp_pos _).le
      ((W.fourRankBasis.baseChange ℝ).equivFun (E α).val) hnorm
    simpa only [Real.exp_add] using h
  · simpa only [hdenom t ht] using hQ α

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

noncomputable def sharedLogCoefficientTuple
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s N : ℕ}
    (F : NilpotentLieFiltration L s)
    (ξ : F.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → F.realification.PolynomialOrbit (fun _ : Unit => 1))
    (α : Unit →₀ ℕ) (t : ZMod N × ZMod N × ZMod N) : Fin 4 → ℝ ⊗[ℚ] L :=
  fun k => coefficients ξ.log α + coefficients
    (v (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))).log α

theorem sharedLogCoefficientTuple_mem_common
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s N : ℕ}
    (F : NilpotentLieFiltration L s) (C D : Submodule ℚ L) (hDC : D ≤ C)
    (ξ : F.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → F.realification.PolynomialOrbit (fun _ : Unit => 1))
    (α : Unit →₀ ℕ) (t : ZMod N × ZMod N × ZMod N)
    (hξ : coefficients ξ.log α ∈ C.baseChange ℝ)
    (hv : ∀ h, coefficients (v h).log α ∈ D.baseChange ℝ) :
    sharedLogCoefficientTuple F ξ v α t ∈ fourCommonModulo (C.baseChange ℝ) (D.baseChange ℝ) := by
  apply (mem_fourCommonModulo _ _ _).mpr
  constructor
  · intro k
    exact (C.baseChange ℝ).add_mem hξ (Submodule.baseChange_mono ℝ hDC (hv _))
  · intro k
    change (coefficients ξ.log α + coefficients (v _).log α) -
      (coefficients ξ.log α + coefficients (v _).log α) ∈ D.baseChange ℝ
    rw [add_sub_add_left_eq_sub]
    exact (D.baseChange ℝ).sub_mem (hv _) (hv _)

namespace NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem native_shared_scaled_correction (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (ξ : W.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → W.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (horbit : ∀ h, W.orbit h = ξ * v h)
    (l : ℕ) (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator = l)
    (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s)
    (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ D.quadruples) :
    ∃ E Q : ℝ ⊗[ℚ] (Fin 4 → W.L),
      ‖(W.fourRankBasis.baseChange ℝ).equivFun E‖ ≤
        Real.exp ((P + 3) ^ 2 + (s : ℝ) * p) / monomialScale (fun _ : Unit => (N : ℝ)) α ∧
      (W.fourRankBasis.baseChange ℝ).equivFun Q ∈ realDenominatorGrid l ∧
      sharedLogCoefficientTuple W.model.filtration ξ v α t -
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) E -
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) Q ∈
          D.realCoefficientFourSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ := by
  obtain ⟨E, Q, hE, hQ, hres⟩ := D.native_full_scaled_correction hs hp hP c τ hG
    l hdenom α hα t ht
  refine ⟨E, Q, hE, hQ, ?_⟩
  apply (D.realCoefficientFourSpace_congr_mod_kernel _ _ _ ?_).mp hres
  intro k
  let a := rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)
  let e := (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) E k
  let z := (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) Q k
  change (coefficients (W.orbit a).log α - e - z) -
    (coefficients ξ.log α + coefficients (v a).log α - e - z) ∈ _
  rw [horbit a]
  have heq : (coefficients (ξ * v a).log α - e - z) -
      (coefficients ξ.log α + coefficients (v a).log α - e - z) =
      coefficients (ξ * v a).log α - (coefficients ξ.log α + coefficients (v a).log α) := by abel
  rw [heq]
  exact W.rank.orbit_log_mul_mod_rank_two hs c τ hG (fun _ : Unit => 1) α ξ (v a)

end NativeRankRelation.CommonData
end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

theorem sharedLogCoefficientTuple_annihilator_decomposition
    {L J : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype J] {s N : ℕ}
    (F : NilpotentLieFiltration L s) (C D : Submodule ℚ L) (hDC : D ≤ C)
    (ℓ : (Fin 4 → L) →ₗ[ℚ] (J → ℚ))
    (hℓ : fourBalancedDependent D ≤ LinearMap.ker ℓ)
    (ξ : F.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → F.realification.PolynomialOrbit (fun _ : Unit => 1))
    (α : Unit →₀ ℕ) (t : ZMod N × ZMod N × ZMod N)
    (hξ : coefficients ξ.log α ∈ C.baseChange ℝ)
    (hv : ∀ h, coefficients (v h).log α ∈ D.baseChange ℝ) :
    let φ := ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => L) 0)
    let a := fun h => realifyCoordinateMap φ (coefficients (v h).log α)
    realFourCoordinateMap ℓ (sharedLogCoefficientTuple F ξ v α t) =
      realifyCoordinateMap (ℓ.comp (fourDiagonalMap (R := ℚ))) (coefficients ξ.log α) +
        (a (rankQuadrupleParameters t 1) + a (rankQuadrupleParameters t 2) -
          a (rankQuadrupleParameters t 0) - a (rankQuadrupleParameters t 3)) := by
  intro φ a
  have h := realFourCoordinateMap_shared_decomposition C D hDC ℓ hℓ
    (coefficients ξ.log α) hξ
    (fun k => coefficients (v (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))).log α)
    (fun k => hv _)
  change realFourCoordinateMap ℓ (sharedLogCoefficientTuple F ξ v α t) =
    realifyCoordinateMap (ℓ.comp (fourDiagonalMap (R := ℚ))) (coefficients ξ.log α) +
      realifyCoordinateMap φ
        (coefficients (v (rankQuadrupleParameters t 1)).log α +
          coefficients (v (rankQuadrupleParameters t 2)).log α -
          coefficients (v (rankQuadrupleParameters t 0)).log α -
          coefficients (v (rankQuadrupleParameters t 3)).log α) at h
  simpa only [map_add, map_sub] using h

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem exists_uniform_shared_refinement
    (hs : 2 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P) (hbP : b ≤ P) (hpP : p ≤ P)
    (U V : Fin s → Submodule ℚ W.L) (hVU : ∀ d, V d ≤ U d)
    (u : ∀ d, Basis (Fin (finrank ℚ (U d))) ℚ (U d))
    (v : ∀ d, Basis (Fin (finrank ℚ (V d))) ℚ (V d))
    (hu : ∀ d a i, rationalLogHeight (W.model.basis.repr (u d a : W.L) i) ≤ P)
    (hv : ∀ d a i, rationalLogHeight (W.model.basis.repr (v d a : W.L) i) ≤ P)
    (ξ : W.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (g : ZMod N → W.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (horbit : ∀ h, W.orbit h = ξ * g h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈ (U d).baseChange ℝ)
    (hg : ∀ h (d : Fin s), coefficients (g h).log (Finsupp.single () (d.val + 1)) ∈
      (V d).baseChange ℝ)
    (hN : Real.exp (separationBudget (8 * sharedRefinementInputBudget s P + 1)) ≤ (N : ℝ)) :
    let B := (P + 2) ^ 3 + 2 * P
    let z := 8 * sharedRefinementInputBudget s P + 1
    ∃ D₁ : R.CommonData B, D₁.quadruples ⊆ D.quadruples ∧ D₁.spaces = D.spaces ∧
      ∀ d : Fin s, ∃ m : ℕ, 0 < m ∧
        (m : ℝ) ≤ Real.exp (z + ((z + 2) ^ 3 + (z + 2) ^ 36)) ∧
        ∀ t ∈ D₁.quadruples, ∃ E Q : ℝ ⊗[ℚ] (Fin 4 → W.L),
          ‖(W.fourRankBasis.baseChange ℝ).equivFun E‖ ≤
            (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) /
              monomialScale (fun _ : Unit => (N : ℝ)) (Finsupp.single () (d.val + 1)) ∧
          (W.fourRankBasis.baseChange ℝ).equivFun Q ∈ realDenominatorGrid m ∧
          (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)).symm
              (sharedLogCoefficientTuple W.model.filtration ξ g (Finsupp.single () (d.val + 1)) t) -
            E - Q ∈ (fourRefinedRelation (U d) (V d)
              (D.coefficientFourSpace ⟨d.val + 1, by omega⟩)).baseChange ℝ := by
  intro B z
  classical
  let A := sharedRefinementInputBudget s P
  obtain ⟨hB, hPB, hA, hPA, hHA, hEA, hLA⟩ := sharedRefinementInputBudget_bounds s hP
  have hAz : A ≤ z := by dsimp only [z, A]; linarith
  have hdim : (Fintype.card (Fin W.dim) : ℝ) ≤ A := by
    simpa only [Fintype.card_fin] using W.complexity.1.1.trans (hbP.trans hPA)
  let : FiniteDimensional ℚ W.L := W.model.basis.finiteDimensional_of_finite
  obtain ⟨c, τ, _, _, hF⟩ := W.rank.filtration.associatedDegree.exists_sorted_adapted_basis
  obtain ⟨D₁, l, hsub, hspaces, hl, hlbound, hdenom⟩ := D.exists_common_projected_denominator hP
  refine ⟨D₁, hsub, hspaces, ?_⟩
  intro d
  let δ : Fin (s + 1) := ⟨d.val + 1, by omega⟩
  let α : Unit →₀ ℕ := Finsupp.single () (d.val + 1)
  have hα : Finsupp.weight (fun _ : Unit => 1) α = δ.val := by
    simp only [α, δ, Finsupp.weight_single, smul_eq_mul, mul_one]
  have hαs : Finsupp.weight (fun _ : Unit => 1) α ≤ s := by rw [hα]; exact Nat.le_of_lt_succ δ.isLt
  have hα0 : α ≠ 0 := by simp [α]
  obtain ⟨k, hk⟩ := D₁.exists_coefficientFour_basis hs hB (hbP.trans hPB) δ
  have hlA : (l : ℝ) ≤ Real.exp A := hlbound.trans (Real.exp_le_exp.mpr hLA)
  obtain ⟨m, hm, hmp, _, hsolve⟩ := exists_fourRefinedRelation_correction W.model.basis
    (U d) (V d) (hVU d) (D₁.coefficientFourSpace δ) (u d) (v d) k hA hdim
    (fun a i => (hu d a i).trans hPA) (fun a i => (hv d a i).trans hPA)
    (fun a i => (hk a i).trans hHA) l hl hlA (fun _ : Unit => (N : ℝ)) (fun _ => hN)
  refine ⟨m, hm, hmp, ?_⟩
  intro t ht
  obtain ⟨E₀, Q₀, hE₀, hQ₀, hres⟩ := D₁.native_shared_scaled_correction (by omega) hp hB
    c τ hF ξ g horbit l hdenom α hαs t ht
  have hδ : (⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hαs⟩ : Fin (s + 1)) = δ :=
    Fin.ext hα
  rw [hδ] at hres
  let e4 := TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)
  let β := sharedLogCoefficientTuple W.model.filtration ξ g α t
  let x := e4.symm β
  have hxK : x - E₀ - Q₀ ∈ (D₁.coefficientFourSpace δ).baseChange ℝ := by
    change β - e4 E₀ - e4 Q₀ ∈ ((D₁.coefficientFourSpace δ).baseChange ℝ).map e4.toLinearMap at hres
    have h := (Submodule.mem_map_equiv _).mp hres
    change e4.symm (β - e4 E₀ - e4 Q₀) ∈ _ at h
    rw [map_sub, map_sub, e4.symm_apply_apply, e4.symm_apply_apply] at h
    exact h
  have hxS : x ∈ (fourCommonModulo (U d) (V d)).baseChange ℝ := by
    have h := sharedLogCoefficientTuple_mem_common W.model.filtration (U d) (V d) (hVU d)
      ξ g α t (hξ d) (fun h => hg h d)
    rw [← realification_fourCommonModulo] at h
    exact (Submodule.mem_map_equiv _).mp h
  have herror : (B + 3) ^ 2 + (s : ℝ) * p ≤ z := by
    have hmul := mul_le_mul_of_nonneg_left hpP (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
    exact (add_le_add_right hmul _).trans (hEA.trans hAz)
  have hEbound : ‖(W.fourRankBasis.baseChange ℝ).equivFun E₀‖ ≤
      Real.exp z / monomialScale (fun _ : Unit => (N : ℝ)) α := by
    apply hE₀.trans
    apply div_le_div_of_nonneg_right (Real.exp_le_exp.mpr herror)
    exact (monomialScale_pos _ (fun _ => by exact_mod_cast NeZero.pos N) α).le
  obtain ⟨E, Q, hE, hQ, hmem⟩ := hsolve α hα0 x E₀ Q₀ hxK hxS hEbound hQ₀
  have hK : D₁.coefficientFourSpace δ = D.coefficientFourSpace δ := by
    rw [D₁.coefficientFourSpace_eq_sup, D.coefficientFourSpace_eq_sup, hspaces]
  rw [hK] at hmem
  exact ⟨E, Q, hE, hQ, hmem⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_correlation_refined_basis (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P')
    (d : Fin s) :
    ∃ a : Basis (Fin (finrank ℚ (fourRefinedRelation (D.coefficientFreeSpan d)
        (D.dependentFreeSpan d) (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)))) ℚ
        (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)),
      ∀ j i, rationalLogHeight ((Pi.basis (fun _ : Fin 4 => E.basis)).repr
        (a j : Fin 4 → D.CoefficientFreeLieAlgebra) i) ≤
          fourRefinementBasisBudget (Q + coefficientFourHeightBudget P') := by
  obtain ⟨c, hc⟩ := D.exists_coefficientFreeSpan_basis E.basis F (by omega) d
  obtain ⟨b, hb⟩ := D.exists_dependentFreeSpan_basis E.basis F (by omega) d
  obtain ⟨k, hk⟩ := D'.exists_coefficientFour_basis hs hP' hQP' ⟨d.val + 1, by omega⟩
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  have hB := coefficientFourHeightBudget_nonneg hP'
  have hQA : Q ≤ Q + coefficientFourHeightBudget P' := le_add_of_nonneg_right hB
  have hBA : coefficientFourHeightBudget P' ≤ Q + coefficientFourHeightBudget P' :=
    le_add_of_nonneg_left hQ
  apply exists_fourRefinedRelation_basis_logHeight E.basis _ _
    (D.dependentFreeSpan_le_coefficientFreeSpan d) _ c b k (add_nonneg hQ hB)
    (by simpa only [Fintype.card_fin] using hT.1.1.trans hQA)
    (fun a i => (hc a i).trans hQA) (fun a i => (hb a i).trans hQA)
  exact fun a i => (hk a i).trans hBA

theorem exists_correlation_refined_annihilator (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P')
    (d : Fin s) :
    ∃ m : ℕ, m ≤ 4 * finrank ℚ D.CoefficientFreeLieAlgebra ∧
      ∃ ℓ : (Fin 4 → D.CoefficientFreeLieAlgebra) →ₗ[ℚ] (Fin m → ℚ),
        Function.Surjective ℓ ∧ LinearMap.ker ℓ =
          fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
            (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩) ∧
        (∀ k i j, rationalLogHeight (ℓ (LinearMap.single ℚ
          (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) k (E.basis i)) j) ≤
            fourRefinementAnnihilatorBudget (Q + coefficientFourHeightBudget P')) ∧
        (∀ x ∈ D.dependentFreeSpan d, ℓ (fourDiagonalMap (R := ℚ) x) = 0) ∧
        (∀ z ∈ fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩),
          ℓ (fourDiagonalMap (R := ℚ) (z 0)) +
            ℓ (LinearMap.single ℚ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0
              (z 0 + z 1 - z 2 - z 3)) = 0) ∧
        fourPetalSpace (D.dependentFreeSpan d)
          (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
            (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)) =
          D.dependentFreeSpan d ⊓ LinearMap.ker
            (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0)) := by
  obtain ⟨c, hc⟩ := D.exists_coefficientFreeSpan_basis E.basis F (by omega) d
  obtain ⟨b, hb⟩ := D.exists_dependentFreeSpan_basis E.basis F (by omega) d
  obtain ⟨k, hk⟩ := D'.exists_coefficientFour_basis hs hP' hQP' ⟨d.val + 1, by omega⟩
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  have hB := coefficientFourHeightBudget_nonneg hP'
  have hQA : Q ≤ Q + coefficientFourHeightBudget P' := le_add_of_nonneg_right hB
  have hBA : coefficientFourHeightBudget P' ≤ Q + coefficientFourHeightBudget P' :=
    le_add_of_nonneg_left hQ
  simpa only [Fintype.card_fin] using
    exists_fourRefinedRelation_annihilator E.basis _ _
      (D.dependentFreeSpan_le_coefficientFreeSpan d) _ c b k (add_nonneg hQ hB)
      (by simpa only [Fintype.card_fin] using hT.1.1.trans hQA)
      (fun a i => (hc a i).trans hQA) (fun a i => (hb a i).trans hQA)
      (fun a i => (hk a i).trans hBA)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_controlled_shared_free_refinement
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp (separationBudget (8 * sharedRefinementInputBudget s P' + 1)) ≤ (N : ℝ)) :
    let B := (P' + 2) ^ 3 + 2 * P'
    let z := 8 * sharedRefinementInputBudget s P' + 1
    ∃ D₁ : R'.CommonData B, D₁.quadruples ⊆ D'.quadruples ∧ D₁.spaces = D'.spaces ∧
      ∀ d : Fin s, ∃ m : ℕ, 0 < m ∧
        (m : ℝ) ≤ Real.exp (z + ((z + 2) ^ 3 + (z + 2) ^ 36)) ∧
        ∀ t ∈ D₁.quadruples, ∃ A S : ℝ ⊗[ℚ] (Fin 4 → D.CoefficientFreeLieAlgebra),
          ‖((Pi.basis (fun _ : Fin 4 => E.basis)).baseChange ℝ).equivFun A‖ ≤
            (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) /
              monomialScale (fun _ : Unit => (N : ℝ)) (Finsupp.single () (d.val + 1)) ∧
          ((Pi.basis (fun _ : Fin 4 => E.basis)).baseChange ℝ).equivFun S ∈ realDenominatorGrid m ∧
          (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra)).symm
              (sharedLogCoefficientTuple E.filtration ξ v (Finsupp.single () (d.val + 1)) t) - A - S ∈
            (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
              (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).baseChange ℝ := by
  have hC := fun d : Fin s => D.exists_coefficientFreeSpan_basis E.basis F (by omega) d
  have hD := fun d : Fin s => D.exists_dependentFreeSpan_basis E.basis F (by omega) d
  choose c hc using hC
  choose a ha using hD
  exact D'.exists_uniform_shared_refinement hs hp' hP' hQP' hpp'
    D.coefficientFreeSpan D.dependentFreeSpan D.dependentFreeSpan_le_coefficientFreeSpan c a
    (fun d j i => (hc d j i).trans hQP') (fun d j i => (ha d j i).trans hQP') ξ v hsplit
    (fun d => Submodule.baseChange_mono ℝ (D.commonFreeSpan_le_coefficientFreeSpan d) (hξ d)) hv hN

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

noncomputable def sharedFreeEquationInputBudget (s : ℕ) (q p : ℝ) : ℝ :=
  let z := 8 * sharedRefinementInputBudget s p + 1
  4 * p + (fourRefinementAnnihilatorBudget (q + coefficientFourHeightBudget p) + 1) +
    (z + ((z + 2) ^ 3 + (z + 2) ^ 36))

theorem sharedFreeEquationInputBudget_bounds (s : ℕ) {q p : ℝ} (hq : 0 ≤ q) (hp : 0 ≤ p) :
    let z := 8 * sharedRefinementInputBudget s p + 1
    let a := fourRefinementAnnihilatorBudget (q + coefficientFourHeightBudget p)
    let A := sharedFreeEquationInputBudget s q p
    0 ≤ A ∧ 4 * p ≤ A ∧ a + 1 ≤ A ∧ z + ((z + 2) ^ 3 + (z + 2) ^ 36) ≤ A := by
  intro z a A
  have hi := (sharedRefinementInputBudget_bounds s hp).2.2.1
  have hz : 0 ≤ z := by dsimp only [z]; linarith
  have ha : 0 ≤ a :=
    fourRefinementAnnihilatorBudget_nonneg (add_nonneg hq (coefficientFourHeightBudget_nonneg hp))
  have hZ : 0 ≤ z + ((z + 2) ^ 3 + (z + 2) ^ 36) := by positivity
  have hA : A = 4 * p + (a + 1) + (z + ((z + 2) ^ 3 + (z + 2) ^ 36)) := rfl
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

namespace NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_controlled_shared_free_equations
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp (separationBudget (8 * sharedRefinementInputBudget s P' + 1)) ≤ (N : ℝ)) :
    let B := (P' + 2) ^ 3 + 2 * P'
    let z := 8 * sharedRefinementInputBudget s P' + 1
    let A := sharedFreeEquationInputBudget s Q P'
    ∃ D₁ : R'.CommonData B, D₁.quadruples ⊆ D'.quadruples ∧ D₁.spaces = D'.spaces ∧
      ∀ d : Fin s, ∃ n : ℕ, n ≤ 4 * finrank ℚ D.CoefficientFreeLieAlgebra ∧
        ∃ ℓ : (Fin 4 → D.CoefficientFreeLieAlgebra) →ₗ[ℚ] (Fin n → ℚ),
          Function.Surjective ℓ ∧ LinearMap.ker ℓ =
            fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
              (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩) ∧
          (∀ k i j, rationalLogHeight (ℓ (LinearMap.single ℚ
            (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) k (E.basis i)) j) ≤
              fourRefinementAnnihilatorBudget (Q + coefficientFourHeightBudget P')) ∧
          ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((A + 2) ^ 4) ∧
            let α := Finsupp.single () (d.val + 1)
            let φ := ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0)
            let a := fun h => realifyCoordinateMap φ (coefficients (v h).log α)
            let c := realifyCoordinateMap (ℓ.comp (fourDiagonalMap (R := ℚ))) (coefficients ξ.log α)
            ∀ t ∈ D₁.quadruples, ∃ q ∈ realDenominatorGrid m,
              ‖c + (a (rankQuadrupleParameters t 1) + a (rankQuadrupleParameters t 2) -
                a (rankQuadrupleParameters t 0) - a (rankQuadrupleParameters t 3)) - q‖ ≤
                Real.exp ((A + 2) ^ 3) *
                  ((Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) /
                    monomialScale (fun _ : Unit => (N : ℝ)) α) := by
  intro B z A
  classical
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  obtain ⟨hA, hdimA, hheightA, hdenomA⟩ := sharedFreeEquationInputBudget_bounds s hQ hP'
  obtain ⟨D₁, hsub, hspaces, hcorr⟩ :=
    D.exists_controlled_shared_free_refinement E T hbQ hT F V g hg D'
      hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  refine ⟨D₁, hsub, hspaces, ?_⟩
  intro d
  obtain ⟨n, hn, ℓ, hsurj, hker, hheight, _, _, _⟩ :=
    D.exists_correlation_refined_annihilator E T hbQ hT F V g hg D' hs hP' hQP' d
  obtain ⟨l, hl, hlp, hcorr⟩ := hcorr d
  let e4 := Pi.basis (fun _ : Fin 4 => E.basis)
  let H := ⌈Real.exp (fourRefinementAnnihilatorBudget (Q + coefficientFourHeightBudget P'))⌉₊
  have hheightH : ∀ j i, RationalHeightLE (ℓ (e4 i) j) H := by
    intro j i
    apply rationalHeightLE_ceil_exp
    have he : e4 i = LinearMap.single ℚ
        (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) i.1 (E.basis i.2) := by
      simp only [e4, Pi.basis_apply, LinearMap.single_apply]
    rw [he]
    exact hheight i.1 i.2 j
  have hdim : (4 : ℝ) * finrank ℚ D.CoefficientFreeLieAlgebra ≤ 4 * P' :=
    mul_le_mul_of_nonneg_left (hT.1.1.trans hQP') (by norm_num)
  have hI : (Fintype.card (Σ _ : Fin 4, Fin (finrank ℚ D.CoefficientFreeLieAlgebra)) : ℝ) ≤ A := by
    simpa only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] using hdim.trans hdimA
  have hJ : (Fintype.card (Fin n) : ℝ) ≤ A := by
    have hn' := (Nat.cast_le (α := ℝ)).mpr hn
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hn'
    simpa only [Fintype.card_fin] using hn'.trans (hdim.trans hdimA)
  have hH : (H : ℝ) ≤ Real.exp A :=
    (ceil_exp_le_exp_add_one (fourRefinementAnnihilatorBudget_nonneg
      (add_nonneg hQ (coefficientFourHeightBudget_nonneg hP')))).trans
        (Real.exp_le_exp.mpr hheightA)
  have hlA : (l : ℝ) ≤ Real.exp A := hlp.trans (Real.exp_le_exp.mpr hdenomA)
  obtain ⟨m, hm, hmA, _, hsolve⟩ :=
    exists_real_annihilator_correction e4 ℓ hheightH hA hI hJ hH hl hlA
  refine ⟨n, hn, ℓ, hsurj, hker, hheight, m, hm, hmA, ?_⟩
  intro α φ a c t ht
  obtain ⟨E₀, Q₀, hE₀, hQ₀, hmem⟩ := hcorr t ht
  rw [← hker] at hmem
  obtain ⟨q, hq, hbound⟩ := hsolve _ E₀ Q₀ _ hmem hE₀ hQ₀
  refine ⟨q, hq, ?_⟩
  have hbalanced : fourBalancedDependent (D.dependentFreeSpan d) ≤ LinearMap.ker ℓ := by
    rw [hker]
    exact fourBalancedDependent_le_refined _ _ _
  have hdecomp := sharedLogCoefficientTuple_annihilator_decomposition E.filtration
    (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
    (D.dependentFreeSpan_le_coefficientFreeSpan d) ℓ hbalanced ξ v α t
    (Submodule.baseChange_mono ℝ (D.commonFreeSpan_le_coefficientFreeSpan d) (hξ d))
    (fun h => hv h d)
  change realFourCoordinateMap ℓ (sharedLogCoefficientTuple E.filtration ξ v α t) =
    c + (a (rankQuadrupleParameters t 1) + a (rankQuadrupleParameters t 2) -
      a (rankQuadrupleParameters t 0) - a (rankQuadrupleParameters t 3)) at hdecomp
  change ‖realFourCoordinateMap ℓ (sharedLogCoefficientTuple E.filtration ξ v α t) - q‖ ≤ _ at hbound
  rw [hdecomp] at hbound
  exact hbound

end NativeRankRelation.CommonData
end Erdos3

end

section

namespace Erdos3

theorem sharedFree_rounding_small {A z : ℝ} (hA : 0 ≤ A) (hz : 0 ≤ z)
    (hbudget : z + ((z + 2) ^ 3 + (z + 2) ^ 36) ≤ A)
    (N l d : ℕ) [NeZero N] (hd : 1 ≤ d)
    (hl : (l : ℝ) ≤ Real.exp ((A + 2) ^ 4))
    (hN : Real.exp ((A + 2) ^ 5) ≤ (N : ℝ)) :
    2 * (l : ℝ) * (Real.exp ((A + 2) ^ 3) *
      ((Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) / (N : ℝ) ^ d)) ≤ 1 := by
  have hzA : z ≤ A := by
    have h3 : 0 ≤ (z + 2) ^ 3 := by positivity
    have h36 : 0 ≤ (z + 2) ^ 36 := by positivity
    linarith
  have h18 : (z + 2) ^ 18 ≤ (z + 2) ^ 36 :=
    pow_le_pow_right₀ (by linarith) (by decide)
  have hwA : (z + 2) ^ 3 + (z + 2) ^ 18 + z ≤ A := by linarith
  have hsum : Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z) ≤
      2 * Real.exp A := by
    linarith [Real.exp_le_exp.mpr hzA, Real.exp_le_exp.mpr hwA]
  have hpoly : (A + 2) ^ 4 + (A + 2) ^ 3 + A + 4 ≤ (A + 2) ^ 5 := by
    have hh : 0 ≤ A ^ 5 + 9 * A ^ 4 + 31 * A ^ 3 + 50 * A ^ 2 + 35 * A + 4 := by positivity
    nlinarith
  have hnum : 2 * (l : ℝ) * (Real.exp ((A + 2) ^ 3) *
      (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z))) ≤
        Real.exp ((A + 2) ^ 5) := by
    calc
      _ ≤ 2 * Real.exp ((A + 2) ^ 4) * (Real.exp ((A + 2) ^ 3) * (2 * Real.exp A)) := by
        gcongr
      _ = 4 * Real.exp ((A + 2) ^ 4 + (A + 2) ^ 3 + A) := by
        simp only [Real.exp_add]
        ring
      _ ≤ Real.exp 4 * Real.exp ((A + 2) ^ 4 + (A + 2) ^ 3 + A) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        linarith [Real.add_one_le_exp (4 : ℝ)]
      _ = Real.exp ((A + 2) ^ 4 + (A + 2) ^ 3 + A + 4) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hpoly
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hpower : (N : ℝ) ≤ (N : ℝ) ^ d := by
    simpa only [pow_one] using pow_le_pow_right₀ hN1 hd
  have hdenpos : (0 : ℝ) < (N : ℝ) ^ d := by positivity
  have hquot := (div_le_one hdenpos).mpr (hnum.trans (hN.trans hpower))
  simpa only [mul_div_assoc] using hquot

noncomputable def sharedFreeRecoveryThreshold (s : ℕ) (q p : ℝ) : ℝ :=
  max (separationBudget (8 * sharedRefinementInputBudget s p + 1))
    ((sharedFreeEquationInputBudget s q p + 2) ^ 5)

theorem sharedFreeRecoveryThreshold_spec (s : ℕ) {q p : ℝ} (hq : 0 ≤ q) (hp : 0 ≤ p)
    (N : ℕ) [NeZero N] (hN : Real.exp (sharedFreeRecoveryThreshold s q p) ≤ (N : ℝ)) :
    let z := 8 * sharedRefinementInputBudget s p + 1
    let A := sharedFreeEquationInputBudget s q p
    Real.exp (separationBudget z) ≤ (N : ℝ) ∧
      ∀ (l d : ℕ), 1 ≤ d → (l : ℝ) ≤ Real.exp ((A + 2) ^ 4) →
        2 * (l : ℝ) * (Real.exp ((A + 2) ^ 3) *
          ((Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) / (N : ℝ) ^ d)) ≤ 1 := by
  intro z A
  constructor
  · exact (Real.exp_le_exp.mpr (le_max_left _ _)).trans hN
  · intro l d hd hl
    have hb := sharedFreeEquationInputBudget_bounds s hq hp
    have hz : 0 ≤ z := by
      have h := (sharedRefinementInputBudget_bounds s hp).2.2.1
      dsimp only [z]
      linarith
    exact sharedFree_rounding_small hb.1 hz hb.2.2.2 N l d hd hl
      ((Real.exp_le_exp.mpr (le_max_right _ _)).trans hN)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SharedFreeRecoveryBudget
namespace OAI

section

namespace Erdos3

theorem exists_sharedFreeRecoveryThreshold_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      sharedFreeRecoveryThreshold s q p ≤ (p + C) ^ C := by
  let R (X : Polynomial ℕ) := ((X + 1 + (X + 3) ^ 7 + 2) ^ 9 + X + 4) ^ 4
  let H (X : Polynomial ℕ) := X + R X + 2
  let G (X : Polynomial ℕ) := X + X * ((X + 2) ^ 7 + X)
  let V (X : Polynomial ℕ) := G (X + (X + (X + 3) ^ 7 + 2) ^ 4 + 1)
  let F (X : Polynomial ℕ) := (4 * X + (X + V (4 * X)) + 3) ^ 7
  let B : Polynomial ℕ := (Polynomial.X + 2) ^ 3 + 2 * Polynomial.X
  let I : Polynomial ℕ := Polynomial.X + H B +
    ((B + 3) ^ 2 + Polynomial.C s * Polynomial.X) + ((Polynomial.X + 2) ^ 3 + Polynomial.X)
  let Z : Polynomial ℕ := 8 * I + 1
  let A : Polynomial ℕ := 4 * Polynomial.X + (F (Polynomial.X + H Polynomial.X) + 1) +
    (Z + ((Z + 2) ^ 3 + (Z + 2) ^ 36))
  let T : Polynomial ℕ := (Z + 2) ^ 48 + (Z + 2) ^ 24 + Z + 1 + (A + 2) ^ 5
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp
  have hH : 0 ≤ coefficientFourHeightBudget p := coefficientFourHeightBudget_nonneg hp
  have hF : fourRefinementAnnihilatorBudget (q + coefficientFourHeightBudget p) ≤
      fourRefinementAnnihilatorBudget (p + coefficientFourHeightBudget p) := by
    unfold fourRefinementAnnihilatorBudget fourRefinementBasisBudget preimageBasisBudget
      sparseGeneratorBudget
    gcongr
  have hA : sharedFreeEquationInputBudget s q p ≤ sharedFreeEquationInputBudget s p p := by
    unfold sharedFreeEquationInputBudget
    linarith
  have hA0 := (sharedFreeEquationInputBudget_bounds s hq hp).1
  have hAp0 := (sharedFreeEquationInputBudget_bounds s hp hp).1
  have hz : 0 ≤ 8 * sharedRefinementInputBudget s p + 1 := by
    have h := (sharedRefinementInputBudget_bounds s hp).2.2.1
    linarith
  have hsep := separationBudget_nonneg hz
  have hupper : sharedFreeRecoveryThreshold s q p ≤
      separationBudget (8 * sharedRefinementInputBudget s p + 1) +
        (sharedFreeEquationInputBudget s p p + 2) ^ 5 := by
    unfold sharedFreeRecoveryThreshold
    apply max_le
    · exact le_add_of_nonneg_right (by positivity)
    · apply le_trans (pow_le_pow_left₀ (by positivity) (by linarith :
        sharedFreeEquationInputBudget s q p + 2 ≤ sharedFreeEquationInputBudget s p p + 2) 5)
      exact le_add_of_nonneg_left hsep
  apply hupper.trans
  simpa [T, A, Z, I, B, F, V, G, H, R, sharedFreeEquationInputBudget,
    sharedRefinementInputBudget, coefficientFourHeightBudget, refiltrationCoordinateBudget,
    fourRefinementAnnihilatorBudget, fourRefinementBasisBudget, preimageBasisBudget,
    sparseGeneratorBudget, separationBudget, Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CommonDependentWordFrequency
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.dependent_word_frequency_zero (a : FreeMagma D.CoefficientAlphabet)
    (hd : lieTreeWeight D.coefficientWeight a = s) (hr : a.length = r)
    (ha : 2 ≤ lieTreeMarkedCount D.coefficientIsDependent a) :
    B.freeFrequency D (lieTreeEval D.coefficientFreeGenerator a) = 0 := by
  obtain ⟨i, j, hij, hi, hj⟩ := exists_two_marked_occurrences D.coefficientIsDependent a ha
  have hweight :
      lieTreeWeight (fun k => (D.coefficientLayerIndex (lieTreeOccurrenceLabel a k)).val + 1)
        (lieTreeOccurrenceTree a) = s := by
    simp only [← D.coefficientWeight_eq_layerIndex]
    exact (lieTreeOccurrenceTree_weight D.coefficientWeight a).trans hd
  have h := B.finite_combined_free_sunflower D
    (fun k => D.coefficientLayerIndex (lieTreeOccurrenceLabel a k))
    (lieTreeOccurrenceTree a) hweight ((lieTreeOccurrenceTree_length a).trans hr)
    (D.coefficientFreeGenerator ∘ lieTreeOccurrenceLabel a)
    (fun k => D.coefficientFreeGenerator_mem_combined (lieTreeOccurrenceLabel a k))
    i j hij (by rw [lieTreeOccurrenceTree_support]; trivial)
    (by rw [lieTreeOccurrenceTree_support]; trivial)
    (D.coefficientFreeGenerator_mem_dependent _ hi)
    (D.coefficientFreeGenerator_mem_dependent _ hj)
  rwa [lieTreeOccurrenceTree_eval] at h

theorem CoefficientBases.dependentWordLayer_top_le_ker :
    D.dependentWordLayer s 2 r ≤ (B.freeFrequency D).ker :=
  markedLieSpan_top_le_ker D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientFreeGenerator_mem_layer
    2 (B.freeFrequency D) (B.dependent_word_frequency_zero D)

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonDependentIntegralModel
namespace OAI

section

namespace Erdos3

open Module

variable {I L : Type*} [Fintype I] [LieRing L] [LieAlgebra ℚ L]

noncomputable def finiteMarkedLieValues (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (s d k l : ℕ) : Finset L := by
  classical
  exact ((finiteLieTrees I s).filter (fun a => d ≤ lieTreeWeight w a ∧
    k ≤ lieTreeMarkedCount marked a ∧ l ≤ a.length)).image (lieTreeEval v)

theorem finiteMarkedLieValues_mem (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (s d k l : ℕ) {x : L} (hx : x ∈ finiteMarkedLieValues v w marked s d k l) :
    x ∈ markedLieSpan v w marked d k l := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨_, hd, hk, hl⟩ := Finset.mem_filter.mp ha
  exact Submodule.subset_span ⟨a, hd, hk, hl, rfl⟩

theorem markedLieSpan_eq_finite_span {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (d k l : ℕ) :
    markedLieSpan v w marked d k l =
      Submodule.span ℚ (finiteMarkedLieValues v w marked s d k l : Set L) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨a, hd, hk, hl, rfl⟩
    by_cases ha : a.length ≤ s
    · exact Submodule.subset_span (Finset.mem_image.mpr ⟨a,
        Finset.mem_filter.mpr ⟨mem_finiteLieTrees_of_length_le I a ha, hd, hk, hl⟩, rfl⟩)
    · have hweight := lieTree_length_le_weight w hw a
      have hzero := F.lieTreeEval_mem_length v w hv a
      rw [F.layer_eq_bot_of_past_top (Or.inl (by omega)), Submodule.mem_bot] at hzero
      rw [hzero]
      exact Submodule.zero_mem _
  · exact Submodule.span_le.mpr (fun _ hx => finiteMarkedLieValues_mem v w marked s d k l hx)

theorem finiteMarkedLieValues_coordinate_height {ι : Type*} [Fintype ι]
    (b : Basis ι ℚ L) (v : I → L) (w : I → ℕ) (marked : I → Bool) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (hv : ∀ i j, RationalHeightLE (b.repr (v i) j) H) (s d k l : ℕ)
    {x : L} (hx : x ∈ finiteMarkedLieValues v w marked s d k l) (j : ι) :
    RationalHeightLE (b.repr x j) (lieTreeHeight (Fintype.card ι) H s) := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  exact finiteLieTrees_coordinate_height b v hc hv s a (Finset.mem_filter.mp ha).1 j

theorem exists_markedLieSpan_bounded_basis {ι : Type*} [Fintype ι] {s r : ℕ}
    (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L)
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H) (d k l : ℕ) :
    ∃ e : Basis (Fin (finrank ℚ (markedLieSpan v w marked d k l))) ℚ
      (markedLieSpan v w marked d k l),
      ∀ i j, RationalHeightLE (b.repr (e i : L) j) (lieTreeHeight (Fintype.card ι) H s) := by
  let S := finiteMarkedLieValues v w marked s d k l
  have hspan : Submodule.span ℚ (Set.range (Subtype.val : S → L)) =
      markedLieSpan v w marked d k l := by
    rw [markedLieSpan_eq_finite_span F v w marked hw hv]
    congr 1
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  exact exists_bounded_submodule_basis_from_spanning b _ (Subtype.val : S → L) hspan
    (fun x j => finiteMarkedLieValues_coordinate_height b v w marked hc hgen s d k l x.property j)

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem top_inter_dependentWordIdeal (k : ℕ) :
    D.coefficientFreeFiltration.layer s r ⊓ (D.dependentWordIdeal 0 k 0).toSubmodule =
      D.dependentWordLayer s k r :=
  FreeDegreeRankLieAlgebra.topLayer_inter_markedIdeal D.CoefficientAlphabet s r D.coefficientWeight
    D.coefficientWeight_pos D.coefficientIsDependent W.rank.filtration.rank_le_degree k

variable {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.top_inter_dependentWordIdeal_le_ker :
    D.coefficientFreeFiltration.layer s r ⊓ (D.dependentWordIdeal 0 2 0).toSubmodule ≤
      (B.freeFrequency D).ker := by
  rw [D.top_inter_dependentWordIdeal]
  exact B.dependentWordLayer_top_le_ker D

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

end Erdos3

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

abbrev DependentQuotient := D.CoefficientFreeLieAlgebra ⧸ D.dependentWordIdeal 0 2 0

noncomputable def dependentQuotientMap : D.CoefficientFreeLieAlgebra →ₗ⁅ℚ⁆ D.DependentQuotient :=
  lieQuotientMap (D.dependentWordIdeal 0 2 0)

noncomputable def dependentQuotientFiltration : DegreeRankLieFiltration D.DependentQuotient s r :=
  D.coefficientFreeFiltration.quotientLie (D.dependentWordIdeal 0 2 0)
    D.coefficientFreeFiltration.rank_le_degree (by
      rw [D.coefficientFreeFiltration.terminal]
      exact bot_le)

theorem dependentQuotientMap_mem_layer {d i : ℕ} {x : D.CoefficientFreeLieAlgebra}
    (hx : x ∈ D.coefficientFreeFiltration.layer d i) :
    D.dependentQuotientMap x ∈ D.dependentQuotientFiltration.layer d i := ⟨x, hx, rfl⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_uniform_dependentQuotient_comparison (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p q P M Q : ℝ}
      {W : NativeDegreeRankFamily s (r + 1) (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (B : D.CoefficientBases M)
      {d e : ℕ} (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s d)
      (F : RationalFilteredNilmanifold D.DependentQuotient s e)
      (T : E.DegreeRankStructure (r + 1)) (S : F.DegreeRankStructure (r + 1))
      [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ] D.DependentQuotient)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.DependentQuotient)]
      [T2Space (ℝ ⊗[ℚ] D.DependentQuotient)]
      (I J σ : Type) [Fintype I] [Fintype J]
      (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) I Q)
      (U : F.UnitVerticalObservable (S.realSubgroup s (r + 1)) J Q)
      (hmap : E.lattice ≤ F.lattice.comap (mapOfSteps
        (hL := E.filtration.lowerCentralSeries_eq_bot)
        (hM := F.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap)),
      T.filtration = D.coefficientFreeFiltration →
      S.filtration = D.dependentQuotientFiltration →
      0 ≤ Q → T.ComplexityLE Q → S.ComplexityLE Q →
      (∀ i j, rationalLogHeight (F.basis.repr (D.dependentQuotientMap (E.basis j)) i) ≤ Q) →
      V.frequency = B.freeFrequency D →
      (∀ x ∈ D.coefficientFreeFiltration.layer s (r + 1),
        U.frequency (D.dependentQuotientMap x) = B.freeFrequency D x) →
      ∀ w : σ → ℕ,
        E.HasUniformLowerRankUnitFamily T
          (mapDifferenceObservable V U D.dependentQuotientMap hmap) w ((Q + C) ^ C) := by
  obtain ⟨C, hC, hcomparison⟩ := exists_uniform_lower_rank_map_difference s
  refine ⟨C, hC, ?_⟩
  intro r N _ b p q P M Q W out H R D B d e E F T S _ _ _ _ _ _ _ _
    I J σ _ _ V U hmap hT hS hQ hTc hSc hentries hV hU w
  apply hcomparison E F T S D.dependentQuotientMap hmap V U hQ hTc hSc hentries
  · intro x hx
    rw [hS]
    apply D.dependentQuotientMap_mem_layer
    rwa [hT] at hx
  · intro x hx
    rw [hT] at hx
    rw [hV]
    exact (hU x hx).symm

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H₀ : Finset (ZMod N)} {R : NativeRankRelation W out H₀ p q} (D : R.CommonData P)
  (B : D.CoefficientBases Q) {n : ℕ}
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
  (T : E.DegreeRankStructure r) (hT : T.filtration = D.coefficientFreeFiltration)
  {H : ℕ} (hH : 1 ≤ H)
  (hbracket : ∀ i j k, RationalHeightLE (lieStructureConstants E.basis i j k) H)
  (hdegree : ∀ i a j, RationalHeightLE (E.basis.repr (E.layerBasis i a).val j) H)
  (hrank : ∀ i j a k, RationalHeightLE (E.basis.repr (T.basis i j a).val k) H)
  (hgen : ∀ i j, RationalHeightLE (E.basis.repr (D.coefficientFreeGenerator i) j) H)
  (hfreq : ∀ i, RationalHeightLE (B.freeFrequency D (E.basis i)) H)

include T hT hH hbracket hdegree hrank hgen hfreq in
theorem CoefficientBases.exists_dependentQuotient_integral_model (l : ℕ) (hl : 0 < l) :
    ∃ m : ℕ, m ≤ n ∧ ∃ d : ℕ, d ≤ n ∧ ∃ u : ℕ, u ≤ d ∧
      let K := rankQuotientHeight n m d u (lieTreeHeight n H s)
      ∃ G : RationalFilteredNilmanifold D.DependentQuotient s d,
        ∃ S : G.DegreeRankStructure r,
          S.filtration = D.dependentQuotientFiltration ∧
          l ∣ G.grid ∧
          G.grid ≤ bchIntegralDenominatorBound s * K ^ (d ^ 3) * (l * K ^ d) ∧
          bchSubgroupCoordinates G.basis G.lattice = scaledIntegerGrid G.grid ∧
          (∀ i j, RationalHeightLE (G.basis.repr (D.dependentQuotientMap (E.basis j)) i) K) ∧
          ∃ ξ : D.DependentQuotient →ₗ[ℚ] ℚ,
            (∀ x ∈ D.coefficientFreeFiltration.layer s r,
              ξ (D.dependentQuotientMap x) = B.freeFrequency D x) ∧
            (∀ i, RationalHeightLE (ξ (G.basis i)) K) ∧
            (∀ z : G.filtration.Group, z ∈ G.lattice → ∃ a : ℤ, ξ z.coord = a) ∧
            ∀ v : ℝ, (d : ℝ) ≤ v → (G.grid : ℝ) ≤ Real.exp v →
              (K : ℝ) ≤ Real.exp v → S.ComplexityLE v := by
  classical
  let I := D.dependentWordIdeal 0 2 0
  let H' := lieTreeHeight n H s
  have hHH' : H ≤ H' := lieTreeHeight_ge_input n H s
  have hb : ∃ b' : ∀ i : Fin (s + 1),
      Basis (Fin (finrank ℚ (T.filtration.associatedDegree.layer (i.val + 1)))) ℚ
        (T.filtration.associatedDegree.layer (i.val + 1)),
      ∀ i a j, RationalHeightLE (E.basis.repr (b' i a).val j) H' := by
    rw [T.associated]
    exact ⟨E.layerBasis, fun i a j => (hdegree i a j).mono hHH'⟩
  obtain ⟨b', hb'⟩ := hb
  obtain ⟨a, ha⟩ := exists_markedLieSpan_bounded_basis D.coefficientFreeFiltration E.basis
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
    D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer hbracket hgen 0 2 0
  change Basis (Fin (finrank ℚ I.toSubmodule)) ℚ I at a
  have ha' : ∀ i j, RationalHeightLE (E.basis.repr (a i).val j) H' := by
    intro i j
    have h := ha i j
    change RationalHeightLE (E.basis.repr (a i).val j)
      (lieTreeHeight (Fintype.card (Fin n)) H s) at h
    simpa only [Fintype.card_fin, H'] using h
  have hann : T.filtration.layer s r ⊓ I.toSubmodule ≤ (B.freeFrequency D).ker := by
    rw [hT]
    exact B.top_inter_dependentWordIdeal_le_ker D
  obtain ⟨m, hm, d, hd, u, hu, f, hproj, hc, hbq, hrq, ξ, hξ, hξH⟩ :=
    exists_bounded_rank_quotient_data T.filtration E.basis b' T.basis I a
      (B.freeFrequency D) hann (hH.trans hHH') hb'
      (fun i j a k => (hrank i j a k).mono hHH') ha'
      (fun i j k => (hbracket i j k).mono hHH') (fun i => (hfreq i).mono hHH')
  let K := rankQuotientHeight n m d u H'
  have hm' : m ≤ n := by
    let _ : FiniteDimensional ℚ D.CoefficientFreeLieAlgebra := E.basis.finiteDimensional_of_finite
    have hn : finrank ℚ D.CoefficientFreeLieAlgebra = n := by
      simpa only [Fintype.card_fin] using finrank_eq_card_basis E.basis
    exact hm.trans ((Submodule.finrank_le I.toSubmodule).trans_eq hn)
  have hbq' : ∀ i : Fin (s + 1), ∃ bq : Basis
      (Fin (finrank ℚ (D.dependentQuotientFiltration.associatedDegree.layer (i.val + 1)))) ℚ
        (D.dependentQuotientFiltration.associatedDegree.layer (i.val + 1)),
      ∀ a j, RationalHeightLE (f.repr (bq a).val j) K := by
    intro i
    have h := hbq i
    rw [hT] at h
    exact h
  have hrq' : ∀ i j : Fin (s + 1), ∃ cq : Basis
      (Fin (finrank ℚ (D.dependentQuotientFiltration.layer i.val j.val))) ℚ
        (D.dependentQuotientFiltration.layer i.val j.val),
      ∀ a k, RationalHeightLE (f.repr (cq a).val k) K := by
    intro i j
    have h := hrq i j
    rw [hT] at h
    exact h
  choose bq hbqH using hbq'
  choose cq hcqH using hrq'
  obtain ⟨grid, hgrid, hdiv, hbound, G, S, hSF, hGf, hGgrid, hcoords, hint, hcomplex⟩ :=
    D.dependentQuotientFiltration.exists_bounded_rank_integral_model_with_frequency
      f bq cq hbqH hcqH hc ξ hξH l hl
  refine ⟨m, hm', d, hd, u, hu, G, S, hSF, hGgrid.symm ▸ hdiv,
    hGgrid.symm ▸ hbound, ?_, ?_, ξ, ?_, ?_, hint, ?_⟩
  · rwa [hGgrid]
  · intro i j
    rw [hGf]
    exact hproj i j
  · intro x hx
    apply hξ x
    rwa [hT]
  · intro i
    rw [hGf]
    exact hξH i
  · intro v hdv hgv hKv
    apply hcomplex v hdv
    · rwa [← hGgrid]
    · exact hKv

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MarkedPolynomialGenerators
namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem markedLieSpan_le_markedDegree {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (d k l : ℕ) :
    markedLieSpan v w marked d k l ≤ F.layer k l := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, _, hk, hl, rfl⟩
  have hweight := hk.trans
    ((lieTreeMarkedCount_le_length marked a).trans (lieTree_length_le_weight w hw a))
  exact F.degree_antitone l hweight
    (F.rank_antitone (lieTreeWeight w a) hl (F.lieTreeEval_mem_length v w hv a))

noncomputable def markedPolynomialLayer (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (d k l : ℕ) : Submodule ℚ (VectorPolynomial σ ℚ L) where
  carrier := {p | ∀ α, coefficients p α ∈
    markedLieSpan v w marked d (k + Finsupp.weight (fun _ : σ => 1) α) l}
  zero_mem' := by intro α; simp only [map_zero, Finsupp.zero_apply, Submodule.zero_mem]
  add_mem' hp hq := by
    intro α
    simpa only [map_add, Finsupp.add_apply] using (markedLieSpan v w marked _ _ _).add_mem (hp α) (hq α)
  smul_mem' c p hp := by
    intro α
    simpa only [map_smul, Finsupp.smul_apply] using (markedLieSpan v w marked _ _ _).smul_mem c (hp α)

theorem markedPolynomialLayer_antitone (v : I → L) (w : I → ℕ) (marked : I → Bool)
    {d e k m l n : ℕ} (hde : d ≤ e) (hkm : k ≤ m) (hln : l ≤ n) :
    markedPolynomialLayer (σ := σ) v w marked e m n ≤ markedPolynomialLayer v w marked d k l := by
  intro p hp α
  exact markedLieSpan_antitone v w marked hde (Nat.add_le_add_right hkm _) hln (hp α)

theorem monomial_mem_markedPolynomialLayer (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (d k l : ℕ) (α : σ →₀ ℕ) {x : L}
    (hx : x ∈ markedLieSpan v w marked d (k + Finsupp.weight (fun _ : σ => 1) α) l) :
    monomial (R := ℚ) α x ∈ markedPolynomialLayer v w marked d k l := by
  classical
  intro β
  by_cases h : α = β
  · subst β
    simpa only [coefficients_monomial, Finsupp.single_eq_same] using hx
  · simp only [coefficients_monomial, Finsupp.single_eq_of_ne (Ne.symm h), Submodule.zero_mem]

theorem markedPolynomialLayer_lie_mem (v : I → L) (w : I → ℕ) (marked : I → Bool)
    {d e k m l n : ℕ} {p q : VectorPolynomial σ ℚ L}
    (hp : p ∈ markedPolynomialLayer v w marked d k l)
    (hq : q ∈ markedPolynomialLayer v w marked e m n) :
    ⁅p, q⁆ ∈ markedPolynomialLayer v w marked (d + e) (k + m) (l + n) := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum, sum_lie_sum]
  apply Submodule.sum_mem
  intro α _
  apply Submodule.sum_mem
  intro β _
  rw [lie_monomial]
  apply monomial_mem_markedPolynomialLayer
  simpa only [map_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    markedLieSpan_lie_mem v w marked (hp α) (hq β)

theorem markedPolynomialLayer_directionalDerivative [Fintype σ]
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (h : σ → ℚ)
    {d k l : ℕ} {p : VectorPolynomial σ ℚ L} (hp : p ∈ markedPolynomialLayer v w marked d k l) :
    directionalDerivative h p ∈ markedPolynomialLayer v w marked d (k + 1) l := by
  intro α
  change coefficients (directionalDerivative h p) α ∈
    markedLieSpan v w marked d (k + 1 + Finsupp.weight (fun _ : σ => 1) α) l
  rw [coefficients_directionalDerivative]
  apply (markedLieSpan v w marked d (k + 1 + Finsupp.weight (fun _ : σ => 1) α) l).sum_mem
  intro i _
  have he : k + Finsupp.weight (fun _ : σ => 1) (α + Finsupp.single i 1) =
      k + 1 + Finsupp.weight (fun _ : σ => 1) α := by
    rw [map_add, Finsupp.weight_single, one_smul]
    omega
  have hi := hp (α + Finsupp.single i 1)
  rw [he] at hi
  exact (markedLieSpan v w marked _ _ _).smul_mem _
    ((markedLieSpan v w marked _ _ _).smul_mem _ hi)

noncomputable def markedPolynomialAlgebra (v : I → L) (w : I → ℕ) (marked : I → Bool) :
    LieSubalgebra ℚ (VectorPolynomial σ ℚ L) :=
  { markedPolynomialLayer (σ := σ) v w marked 0 0 0 with
    lie_mem' := by
      intro p q hp hq
      change ⁅p, q⁆ ∈ markedPolynomialLayer v w marked 0 0 0
      exact markedPolynomialLayer_lie_mem v w marked
        (d := 0) (e := 0) (k := 0) (m := 0) (l := 0) (n := 0) hp hq }

theorem markedPolynomialAlgebra_le_adapted {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) :
    markedPolynomialAlgebra (σ := σ) v w marked ≤ F.associatedDegree.adaptedLieSubalgebra (fun _ => 1) := by
  intro p hp α
  have ha := hp α
  rw [Nat.zero_add] at ha
  exact markedLieSpan_le_markedDegree F v w marked hw hv 0 _ 0 ha

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem markedLieSpan_degree_zero_eq_one (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (hw : ∀ i, 0 < w i) (k l : ℕ) :
    markedLieSpan v w marked 0 k l = markedLieSpan v w marked 1 k l := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro x ⟨a, _, hk, hl, rfl⟩
    exact ⟨a, a.length_pos.trans_le (lieTree_length_le_weight w hw a), hk, hl, rfl⟩
  · exact markedLieSpan_antitone v w marked (Nat.zero_le 1) le_rfl le_rfl

theorem markedPolynomialLayer_degree_zero_eq_one (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (hw : ∀ i, 0 < w i) (k l : ℕ) :
    markedPolynomialLayer (σ := σ) v w marked 0 k l = markedPolynomialLayer v w marked 1 k l := by
  ext p
  change (∀ α, coefficients p α ∈ markedLieSpan v w marked 0
    (k + Finsupp.weight (fun _ : σ => 1) α) l) ↔ _
  simp only [markedLieSpan_degree_zero_eq_one v w marked hw]
  rfl

theorem markedPolynomialLayer_degree_terminal {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (k l : ℕ) :
    markedPolynomialLayer (σ := σ) v w marked (s + 1) k l = ⊥ := by
  apply bot_unique
  intro p hp
  change p = 0
  apply coefficients.injective
  ext α
  have h := markedLieSpan_le_layer F v w marked hv (s + 1) _ l (hp α)
  rw [F.layer_eq_bot_of_past_top (Or.inl (Nat.lt_succ_self s)), Submodule.mem_bot] at h
  simpa only [map_zero, Finsupp.zero_apply] using h

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem markedPolynomialLayer_eval_mem (v : I → L) (w : I → ℕ) (marked : I → Bool)
    {d k l : ℕ} {p : VectorPolynomial σ ℚ L} (hp : p ∈ markedPolynomialLayer v w marked d k l)
    (t : σ → ℚ) : eval t p ∈ markedLieSpan v w marked d k l := by
  apply (eval_mem_iff_coefficients (markedLieSpan v w marked d k l) p).mpr _ t
  intro α
  exact markedLieSpan_antitone v w marked le_rfl (Nat.le_add_right k _) le_rfl (hp α)

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
  (v : I → L) (w : I → ℕ) (marked : I → Bool)

theorem markedPolynomialLayer_translate (h : σ → ℚ) {d k l : ℕ}
    {p : VectorPolynomial σ ℚ L} (hp : p ∈ markedPolynomialLayer v w marked d k l) :
    translate h p ∈ markedPolynomialLayer v w marked d k l := by
  intro α
  rw [coefficients_translate]
  apply Submodule.sum_mem
  intro β _
  by_cases hc : (polynomialTranslate h (MvPolynomial.monomial β 1)).coeff α = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    have hd := polynomialDegreeGap_translate_monomial h β (MvPolynomial.mem_support_iff.mpr hc)
    change Finsupp.weight (fun _ : σ => 1) α + 0 ≤ Finsupp.weight (fun _ : σ => 1) β at hd
    exact markedLieSpan_antitone v w marked le_rfl (by omega) le_rfl (hp β)

theorem markedPolynomialLayer_taylorRemainder [Fintype σ] (h : σ → ℚ) {d k l : ℕ}
    {p : VectorPolynomial σ ℚ L} (hp : p ∈ markedPolynomialLayer v w marked d k l) :
    translate h p - p - directionalDerivative h p ∈
      markedPolynomialLayer v w marked d (k + 2) l := by
  rw [← taylorRemainder_apply]
  intro α
  rw [coefficients_taylorRemainder]
  apply Submodule.sum_mem
  intro β _
  by_cases hc : (scalarTaylorRemainder h (MvPolynomial.monomial β 1)).coeff α = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    have hd := scalarTaylorRemainder_monomial h β (MvPolynomial.mem_support_iff.mpr hc)
    change Finsupp.weight (fun _ : σ => 1) α + 2 ≤ Finsupp.weight (fun _ : σ => 1) β at hd
    exact markedLieSpan_antitone v w marked le_rfl (by omega) le_rfl (hp β)

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

noncomputable def markedParameterExponents (σ : Type*) [Fintype σ] (s : ℕ) : Finset (σ →₀ ℕ) :=
  (Finsupp.finite_of_nat_weight_le (fun _ : σ => 1) (by simp) s).toFinset

@[simp] theorem mem_markedParameterExponents {σ : Type*} [Fintype σ] (s : ℕ) (α : σ →₀ ℕ) :
    α ∈ markedParameterExponents σ s ↔ Finsupp.weight (fun _ : σ => 1) α ≤ s := by
  classical
  simp only [markedParameterExponents, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

variable {I σ L : Type*} [Fintype I] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

noncomputable def finiteMarkedPolynomialValues (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (s d k l : ℕ) : Finset (VectorPolynomial σ ℚ L) := by
  classical
  exact (markedParameterExponents σ s).biUnion (fun α =>
    (finiteMarkedLieValues v w marked s d (k + Finsupp.weight (fun _ : σ => 1) α) l).image
      (monomial (R := ℚ) α))

theorem finiteMarkedPolynomialValues_mem (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (s d k l : ℕ) {p : VectorPolynomial σ ℚ L}
    (hp : p ∈ finiteMarkedPolynomialValues v w marked s d k l) :
    p ∈ markedPolynomialLayer v w marked d k l := by
  classical
  obtain ⟨α, _, hα⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hα
  exact monomial_mem_markedPolynomialLayer v w marked d k l α
    (finiteMarkedLieValues_mem v w marked s d _ l hx)

omit [Fintype I] [Fintype σ] in
theorem markedPolynomialLayer_degreeLE {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) {d k l : ℕ} {p : VectorPolynomial σ ℚ L}
    (hp : p ∈ markedPolynomialLayer v w marked d k l) : DegreeLE (fun _ : σ => 1) s p := by
  intro α hα
  have hm := markedLieSpan_antitone v w marked le_rfl
    (by omega : s + 1 ≤ k + Finsupp.weight (fun _ : σ => 1) α) le_rfl (hp α)
  simpa only [markedLieSpan_marked_terminal F v w marked hw hv, Submodule.mem_bot] using hm

theorem monomial_mem_span_finiteMarkedPolynomialValues {s r : ℕ}
    (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
    (d k l : ℕ) (α : σ →₀ ℕ) (hα : Finsupp.weight (fun _ : σ => 1) α ≤ s)
    {x : L} (hx : x ∈ markedLieSpan v w marked d (k + Finsupp.weight (fun _ : σ => 1) α) l) :
    monomial (R := ℚ) α x ∈
      Submodule.span ℚ (finiteMarkedPolynomialValues (σ := σ) v w marked s d k l : Set (VectorPolynomial σ ℚ L)) := by
  classical
  rw [markedLieSpan_eq_finite_span F v w marked hw hv] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    exact Submodule.subset_span (Finset.mem_biUnion.mpr
      ⟨α, (mem_markedParameterExponents s α).mpr hα, Finset.mem_image.mpr ⟨y, hy, rfl⟩⟩)
  | zero => simp only [monomial, TensorProduct.tmul_zero, Submodule.zero_mem]
  | add y z _ _ hy hz =>
    simpa only [monomial, TensorProduct.tmul_add] using Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    simpa only [monomial, TensorProduct.tmul_smul] using Submodule.smul_mem _ c hy

theorem markedPolynomialLayer_eq_finite_span {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (d k l : ℕ) :
    markedPolynomialLayer (σ := σ) v w marked d k l =
      Submodule.span ℚ (finiteMarkedPolynomialValues (σ := σ) v w marked s d k l : Set (VectorPolynomial σ ℚ L)) := by
  classical
  apply le_antisymm
  · intro p hp
    have hdeg := (degreeLE_iff (fun _ : σ => 1) s p).mp
      (markedPolynomialLayer_degreeLE F v w marked hw hv hp)
    rw [← sum_monomial_coefficients p]
    simp only [Finsupp.sum]
    apply Submodule.sum_mem
    intro α hα
    exact monomial_mem_span_finiteMarkedPolynomialValues F v w marked hw hv d k l α
      (hdeg α hα) (hp α)
  · exact Submodule.span_le.mpr
      (fun _ hp => finiteMarkedPolynomialValues_mem v w marked s d k l hp)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedShiftGeneratorBounds
namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)

noncomputable def markedShiftSubalgebra (t : ℕ) :
    LieSubalgebra ℚ (F.associatedDegree.PolynomialShiftAlgebra t) where
  carrier := {x | x.left.val ∈ markedPolynomialLayer v w marked 0 0 0}
  zero_mem' := (markedPolynomialLayer v w marked 0 0 0).zero_mem
  add_mem' hx hy := (markedPolynomialLayer v w marked 0 0 0).add_mem hx hy
  smul_mem' c _ hx := (markedPolynomialLayer v w marked 0 0 0).smul_mem c hx
  lie_mem' := by
    intro x y hx hy
    change ⁅x.left.val, y.left.val⁆ + directionalDerivative x.right y.left.val -
      directionalDerivative y.right x.left.val ∈ markedPolynomialLayer v w marked 0 0 0
    have hder (h : Fin t → ℚ) (p : VectorPolynomial (Fin t) ℚ L)
        (hp : p ∈ markedPolynomialLayer v w marked 0 0 0) :
        directionalDerivative h p ∈ markedPolynomialLayer v w marked 0 0 0 :=
      markedPolynomialLayer_antitone v w marked le_rfl (Nat.zero_le 1) le_rfl
        (markedPolynomialLayer_directionalDerivative v w marked h (d := 0) (k := 0) (l := 0) hp)
    exact (markedPolynomialLayer v w marked 0 0 0).sub_mem
      ((markedPolynomialLayer v w marked 0 0 0).add_mem
        (markedPolynomialLayer_lie_mem v w marked
          (d := 0) (e := 0) (k := 0) (m := 0) (l := 0) (n := 0) hx hy)
        (hder x.right y.left.val hy)) (hder y.right x.left.val hx)

theorem markedShiftSubalgebra_contains_direction (t : ℕ) (h : RationalTorus.Algebra t) :
    (⟨0, h⟩ : F.associatedDegree.PolynomialShiftAlgebra t) ∈ markedShiftSubalgebra F v w marked t :=
  (markedPolynomialLayer v w marked 0 0 0).zero_mem

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)

noncomputable def markedShiftPolynomialSubmodule (t d k l : ℕ) :
    Submodule ℚ (markedShiftSubalgebra F v w marked t) where
  carrier := {x | x.val.right = 0 ∧ x.val.left.val ∈ markedPolynomialLayer v w marked d k l}
  zero_mem' := ⟨rfl, (markedPolynomialLayer v w marked d k l).zero_mem⟩
  add_mem' := by
    intro x y hx hy
    constructor
    · change x.val.right + y.val.right = (0 : RationalTorus.Algebra t)
      rw [hx.1, hy.1, add_zero]
    · exact (markedPolynomialLayer v w marked d k l).add_mem hx.2 hy.2
  smul_mem' c x hx := by
    constructor
    · change c • x.val.right = 0
      rw [hx.1, smul_zero]
    · exact (markedPolynomialLayer v w marked d k l).smul_mem c hx.2

noncomputable def markedShiftSecondIdeal (t : ℕ) :
    LieIdeal ℚ (markedShiftSubalgebra F v w marked t) :=
  { markedShiftPolynomialSubmodule F v w marked t 0 2 0 with
    lie_mem := by
      intro x y hy
      constructor
      · rfl
      · change ⁅x.val.left.val, y.val.left.val⁆ + directionalDerivative x.val.right y.val.left.val -
          directionalDerivative y.val.right x.val.left.val ∈ markedPolynomialLayer v w marked 0 2 0
        rw [hy.1]
        have hz : directionalDerivative (0 : Fin t → ℚ) x.val.left.val = 0 := by
          simp only [directionalDerivative, Pi.zero_apply, zero_smul, Finset.sum_const_zero,
            LinearMap.zero_apply]
        change ⁅x.val.left.val, y.val.left.val⁆ + directionalDerivative x.val.right y.val.left.val -
          directionalDerivative (0 : Fin t → ℚ) x.val.left.val ∈ markedPolynomialLayer v w marked 0 2 0
        rw [hz, sub_zero]
        apply (markedPolynomialLayer v w marked 0 2 0).add_mem
        · exact markedPolynomialLayer_lie_mem v w marked
            (d := 0) (e := 0) (k := 0) (m := 2) (l := 0) (n := 0) x.property hy.2
        · exact markedPolynomialLayer_antitone v w marked le_rfl (by omega : 2 ≤ 2 + 1) le_rfl
            (markedPolynomialLayer_directionalDerivative v w marked x.val.right
              (d := 0) (k := 2) (l := 0) hy.2) }

abbrev MarkedShiftQuotient (t : ℕ) :=
  markedShiftSubalgebra F v w marked t ⧸ markedShiftSecondIdeal F v w marked t

noncomputable def markedShiftEval (t : ℕ) (a : Fin t → ℚ) :
    markedShiftSubalgebra F v w marked t →ₗ[ℚ] L where
  toFun x := eval a x.val.left.val
  map_add' x y := (eval a).map_add x.val.left.val y.val.left.val
  map_smul' c x := (eval a).map_smul c x.val.left.val

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)

noncomputable def markedShiftBiLayer (t h n : ℕ) :
    Submodule ℚ (markedShiftSubalgebra F v w marked t) where
  carrier := {x | x.val.left.val ∈ markedPolynomialLayer v w marked n h 0 ∧
    (n ≠ 0 ∨ 1 < h → x.val.right = 0)}
  zero_mem' := ⟨(markedPolynomialLayer v w marked n h 0).zero_mem, fun _ => rfl⟩
  add_mem' := by
    intro x y hx hy
    refine ⟨(markedPolynomialLayer v w marked n h 0).add_mem hx.1 hy.1, ?_⟩
    intro hc
    change x.val.right + y.val.right = 0
    rw [hx.2 hc, hy.2 hc, add_zero]
  smul_mem' c x hx := by
    refine ⟨(markedPolynomialLayer v w marked n h 0).smul_mem c hx.1, ?_⟩
    intro hc
    change c • x.val.right = 0
    rw [hx.2 hc, smul_zero]

theorem markedShiftBiLayer_antitone (t : ℕ) {h k n m : ℕ} (hh : h ≤ k) (hn : n ≤ m) :
    markedShiftBiLayer F v w marked t k m ≤ markedShiftBiLayer F v w marked t h n := by
  intro x hx
  refine ⟨markedPolynomialLayer_antitone v w marked hn hh le_rfl hx.1, ?_⟩
  intro hc
  exact hx.2 (by omega)

theorem markedShiftBiLayer_zero (t : ℕ) : markedShiftBiLayer F v w marked t 0 0 = ⊤ := by
  apply top_unique
  intro x _
  refine ⟨x.property, ?_⟩
  intro hc
  omega

theorem markedPolynomialLayer_shiftDerivative {t h n k m : ℕ} (u : Fin t → ℚ)
    (hu : n ≠ 0 ∨ 1 < h → u = 0) {p : VectorPolynomial (Fin t) ℚ L}
    (hp : p ∈ markedPolynomialLayer v w marked m k 0) :
    directionalDerivative u p ∈ markedPolynomialLayer v w marked (n + m) (h + k) 0 := by
  by_cases ha : n = 0 ∧ h ≤ 1
  · obtain ⟨rfl, hh⟩ := ha
    have hd := markedPolynomialLayer_directionalDerivative v w marked u hp
    simpa only [Nat.zero_add] using
      markedPolynomialLayer_antitone v w marked le_rfl (by omega : h + k ≤ k + 1) le_rfl hd
  · have hz := hu (by omega)
    rw [hz]
    simp only [directionalDerivative, Pi.zero_apply, zero_smul, Finset.sum_const_zero,
      LinearMap.zero_apply, Submodule.zero_mem]

theorem markedShiftBiLayer_lie_mem (t : ℕ) {h k n m : ℕ}
    {x y : markedShiftSubalgebra F v w marked t}
    (hx : x ∈ markedShiftBiLayer F v w marked t h n)
    (hy : y ∈ markedShiftBiLayer F v w marked t k m) :
    ⁅x, y⁆ ∈ markedShiftBiLayer F v w marked t (h + k) (n + m) := by
  constructor
  · change ⁅x.val.left.val, y.val.left.val⁆ + directionalDerivative x.val.right y.val.left.val -
      directionalDerivative y.val.right x.val.left.val ∈ markedPolynomialLayer v w marked (n + m) (h + k) 0
    apply (markedPolynomialLayer v w marked (n + m) (h + k) 0).sub_mem
    · exact (markedPolynomialLayer v w marked (n + m) (h + k) 0).add_mem
        (markedPolynomialLayer_lie_mem v w marked (l := 0) (n := 0) hx.1 hy.1)
        (markedPolynomialLayer_shiftDerivative v w marked x.val.right hx.2 hy.1)
    · simpa only [Nat.add_comm] using
        markedPolynomialLayer_shiftDerivative v w marked y.val.right hy.2 hx.1
  · intro _
    rfl

theorem markedShiftBiLayer_eq_polynomialSubmodule (t h n : ℕ) (hc : n ≠ 0 ∨ 1 < h) :
    markedShiftBiLayer F v w marked t h n = markedShiftPolynomialSubmodule F v w marked t n h 0 := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.2 hc, hx.1⟩
  · intro hx
    exact ⟨hx.2, fun _ => hx.1⟩

theorem markedShiftBiLayer_second (t : ℕ) :
    markedShiftBiLayer F v w marked t 2 0 = (markedShiftSecondIdeal F v w marked t).toSubmodule :=
  markedShiftBiLayer_eq_polynomialSubmodule F v w marked t 2 0 (Or.inr (by decide))

theorem markedShiftBiLayer_positive (hw : ∀ i, 0 < w i) (t : ℕ) :
    markedShiftBiLayer F v w marked t 0 1 ⊔ markedShiftBiLayer F v w marked t 1 0 = ⊤ := by
  apply top_unique
  intro x _
  let p : markedShiftSubalgebra F v w marked t := ⟨⟨x.val.left, 0⟩, x.property⟩
  let q : markedShiftSubalgebra F v w marked t :=
    ⟨⟨0, x.val.right⟩, (markedPolynomialLayer v w marked 0 0 0).zero_mem⟩
  have hp : p ∈ markedShiftBiLayer F v w marked t 0 1 := by
    exact ⟨(markedPolynomialLayer_degree_zero_eq_one v w marked hw 0 0).le x.property,
      fun _ => rfl⟩
  have hq : q ∈ markedShiftBiLayer F v w marked t 1 0 := by
    refine ⟨(markedPolynomialLayer v w marked 0 1 0).zero_mem, ?_⟩
    intro hc
    omega
  have he : p + q = x := by
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · change x.val.left + 0 = x.val.left
      exact add_zero _
    · change 0 + x.val.right = x.val.right
      exact zero_add _
  have hx := Submodule.add_mem _ (Submodule.mem_sup_left hp) (Submodule.mem_sup_right hq)
  rwa [he] at hx

theorem markedShiftBiLayer_degree_terminal
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (t h : ℕ) :
    markedShiftBiLayer F v w marked t h (s + 1) = ⊥ := by
  apply bot_unique
  intro x hx
  have hp : x.val.left.val = 0 := by
    simpa only [markedPolynomialLayer_degree_terminal F v w marked hv, Submodule.mem_bot] using hx.1
  have hq : x.val.right = 0 := hx.2 (Or.inl (by omega))
  change x = 0
  apply Subtype.ext
  apply LieAlgebra.SemiDirectSum.ext
  · apply Subtype.ext
    change x.val.left.val = 0
    exact hp
  · change x.val.right = 0
    exact hq

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial NilpotentLieBCHGroup

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ)

noncomputable def markedShiftDirection (h : Fin t → ℚ) : markedShiftSubalgebra F v w marked t :=
  ⟨⟨0, h⟩, markedShiftSubalgebra_contains_direction F v w marked t h⟩

theorem markedShiftDirection_lie_left (h : Fin t → ℚ) (x : markedShiftSubalgebra F v w marked t) :
    (⁅markedShiftDirection F v w marked t h, x⁆).val.left.val =
      directionalDerivative h x.val.left.val := by
  change ⁅(0 : VectorPolynomial (Fin t) ℚ L), x.val.left.val⁆ +
    directionalDerivative h x.val.left.val - directionalDerivative x.val.right 0 = _
  have hz : ⁅(0 : VectorPolynomial (Fin t) ℚ L), x.val.left.val⁆ = 0 :=
    zero_lie (L := VectorPolynomial (Fin t) ℚ L) x.val.left.val
  have hd : directionalDerivative x.val.right (0 : VectorPolynomial (Fin t) ℚ L) = 0 := map_zero _
  exact (congrArg₂ (fun a b : VectorPolynomial (Fin t) ℚ L =>
    a + directionalDerivative h x.val.left.val - b) hz hd).trans (by simp)

theorem markedShiftDirection_lie_right (h : Fin t → ℚ) (x : markedShiftSubalgebra F v w marked t) :
    (⁅markedShiftDirection F v w marked t h, x⁆).val.right = 0 := rfl

noncomputable def markedQuotientDirection (h : Fin t → ℚ) : MarkedShiftQuotient F v w marked t :=
  lieQuotientMap (markedShiftSecondIdeal F v w marked t) (markedShiftDirection F v w marked t h)

end Erdos3

end

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s)

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

variable {I L : Type*} [Fintype I] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)

noncomputable def markedPolynomialGeneratorFamily (t d k l : ℕ)
    (p : finiteMarkedPolynomialValues (σ := Fin t) v w marked s d k l) :
    markedPolynomialLayer (σ := Fin t) v w marked d k l :=
  ⟨p.val, finiteMarkedPolynomialValues_mem v w marked s d k l p.property⟩

include hw hv in
theorem markedPolynomialGeneratorFamily_span (t d k l : ℕ) :
    Submodule.span ℚ (Set.range (markedPolynomialGeneratorFamily (s := s) v w marked t d k l)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff _ _).mpr
  have hrange : Set.range (fun p : finiteMarkedPolynomialValues (σ := Fin t) v w marked s d k l =>
      (p.val : VectorPolynomial (Fin t) ℚ L)) =
      (finiteMarkedPolynomialValues (σ := Fin t) v w marked s d k l : Set (VectorPolynomial (Fin t) ℚ L)) := by
    ext p
    exact ⟨fun ⟨q, hq⟩ => hq ▸ q.property, fun hp => ⟨⟨p, hp⟩, rfl⟩⟩
  change Submodule.span ℚ (Set.range (fun p : finiteMarkedPolynomialValues (σ := Fin t) v w marked s d k l =>
    (p.val : VectorPolynomial (Fin t) ℚ L))) = _
  rw [hrange]
  exact (markedPolynomialLayer_eq_finite_span F v w marked hw hv d k l).symm

noncomputable def markedShiftLayerPolynomialMap (t d k l : ℕ) :
    markedPolynomialLayer (σ := Fin t) v w marked d k l →ₗ[ℚ] markedShiftSubalgebra F v w marked t where
  toFun p :=
    let hp := markedPolynomialLayer_antitone v w marked (Nat.zero_le d) (Nat.zero_le k) (Nat.zero_le l) p.property
    ⟨⟨⟨p.val, markedPolynomialAlgebra_le_adapted F v w marked hw hv hp⟩, 0⟩, hp⟩
  map_add' p q := by
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · apply Subtype.ext
      rfl
    · exact (zero_add (0 : RationalTorus.Algebra t)).symm
  map_smul' c p := by
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · apply Subtype.ext
      rfl
    · exact (smul_zero c : c • (0 : RationalTorus.Algebra t) = 0).symm

noncomputable def markedShiftDirectionMap (t : ℕ) :
    RationalTorus.Algebra t →ₗ[ℚ] markedShiftSubalgebra F v w marked t where
  toFun u := ⟨⟨0, u⟩, (markedPolynomialLayer v w marked 0 0 0).zero_mem⟩
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

abbrev MarkedShiftGeneratorIndex (t h n : ℕ) :=
  (finiteMarkedPolynomialValues (σ := Fin t) v w marked s n h 0) ⊕
    {_i : Fin t // n = 0 ∧ h ≤ 1}

noncomputable def markedShiftGenerator (t h n : ℕ) :
    MarkedShiftGeneratorIndex (s := s) v w marked t h n → markedShiftSubalgebra F v w marked t
  | .inl p => markedShiftLayerPolynomialMap F v w marked hw hv t n h 0
      (markedPolynomialGeneratorFamily v w marked t n h 0 p)
  | .inr i => markedShiftDirectionMap F v w marked t (RationalTorus.basis t i.val)

theorem markedShiftGenerator_mem (t h n : ℕ)
    (i : MarkedShiftGeneratorIndex (s := s) v w marked t h n) :
    markedShiftGenerator F v w marked hw hv t h n i ∈ markedShiftBiLayer F v w marked t h n := by
  rcases i with p | i
  · exact ⟨finiteMarkedPolynomialValues_mem v w marked s n h 0 p.property, fun _ => rfl⟩
  · refine ⟨(markedPolynomialLayer v w marked n h 0).zero_mem, ?_⟩
    intro hc
    have hi := i.property
    omega

theorem markedShiftGenerator_span (t h n : ℕ) :
    Submodule.span ℚ (Set.range (markedShiftGenerator F v w marked hw hv t h n)) =
      markedShiftBiLayer F v w marked t h n := by
  classical
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun _ ⟨i, hi⟩ => hi ▸ markedShiftGenerator_mem F v w marked hw hv t h n i)
  · intro x hx
    let S := Submodule.span ℚ (Set.range (markedShiftGenerator F v w marked hw hv t h n))
    have hpoly (p : markedPolynomialLayer (σ := Fin t) v w marked n h 0) :
        markedShiftLayerPolynomialMap F v w marked hw hv t n h 0 p ∈ S := by
      have hp : p ∈ Submodule.span ℚ
          (Set.range (markedPolynomialGeneratorFamily (s := s) v w marked t n h 0)) := by
        rw [markedPolynomialGeneratorFamily_span F v w marked hw hv]
        trivial
      induction hp using Submodule.span_induction with
      | mem q hq =>
        obtain ⟨i, rfl⟩ := hq
        exact Submodule.subset_span ⟨.inl i, rfl⟩
      | zero => rw [map_zero]; exact S.zero_mem
      | add p q _ _ hp hq => rw [map_add]; exact S.add_mem hp hq
      | smul c p _ hp => rw [map_smul]; exact S.smul_mem c hp
    have hdir : markedShiftDirectionMap F v w marked t x.val.right ∈ S := by
      by_cases ha : n = 0 ∧ h ≤ 1
      · rw [← (RationalTorus.basis t).sum_repr x.val.right, map_sum]
        apply S.sum_mem
        intro i _
        rw [map_smul]
        exact S.smul_mem _ (Submodule.subset_span ⟨.inr ⟨i, ha⟩, rfl⟩)
      · rw [hx.2 (by omega), map_zero]
        exact S.zero_mem
    have he : markedShiftLayerPolynomialMap F v w marked hw hv t n h 0 ⟨x.val.left.val, hx.1⟩ +
        markedShiftDirectionMap F v w marked t x.val.right = x := by
      apply Subtype.ext
      apply LieAlgebra.SemiDirectSum.ext
      · apply Subtype.ext
        change x.val.left.val + 0 = x.val.left.val
        exact add_zero _
      · change 0 + x.val.right = x.val.right
        exact zero_add _
    exact he ▸ S.add_mem (hpoly ⟨x.val.left.val, hx.1⟩) hdir

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial NilpotentLieBCHGroup

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

noncomputable def markedShiftTranslate (h : Fin t → ℚ) :
    markedShiftSubalgebra F v w marked t →ₗ[ℚ] markedShiftSubalgebra F v w marked t where
  toFun x :=
    ⟨⟨⟨translate h x.val.left.val,
        markedPolynomialAlgebra_le_adapted F v w marked hw hv
          (markedPolynomialLayer_translate v w marked h x.property)⟩, x.val.right⟩,
      markedPolynomialLayer_translate v w marked h x.property⟩
  map_add' x y := by
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · apply Subtype.ext
      exact (VectorPolynomial.translate h).map_add x.val.left.val y.val.left.val
    · rfl
  map_smul' a x := by
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · apply Subtype.ext
      exact (VectorPolynomial.translate h).map_smul a x.val.left.val
    · rfl

theorem markedShiftEval_translate (h a : Fin t → ℚ) (x : markedShiftSubalgebra F v w marked t) :
    markedShiftEval F v w marked t a (markedShiftTranslate F v w marked hw hv t h x) =
      markedShiftEval F v w marked t (a + h) x :=
  eval_translate h a x.val.left.val

theorem markedShiftTranslate_second_mem (h : Fin t → ℚ) {x : markedShiftSubalgebra F v w marked t}
    (hx : x ∈ markedShiftSecondIdeal F v w marked t) :
    markedShiftTranslate F v w marked hw hv t h x ∈ markedShiftSecondIdeal F v w marked t :=
  ⟨hx.1, markedPolynomialLayer_translate v w marked h hx.2⟩

theorem markedShiftTranslate_first_order (h : Fin t → ℚ) (x : markedShiftSubalgebra F v w marked t) :
    markedShiftTranslate F v w marked hw hv t h x - x - ⁅markedShiftDirection F v w marked t h, x⁆ ∈
      markedShiftSecondIdeal F v w marked t := by
  constructor
  · change x.val.right - x.val.right - (⁅markedShiftDirection F v w marked t h, x⁆).val.right = 0
    rw [markedShiftDirection_lie_right, sub_self, sub_zero]
  · change translate h x.val.left.val - x.val.left.val -
      (⁅markedShiftDirection F v w marked t h, x⁆).val.left.val ∈ _
    rw [markedShiftDirection_lie_left]
    exact markedPolynomialLayer_taylorRemainder v w marked h x.property

theorem markedShiftTranslate_quotient (h : Fin t → ℚ) (x : markedShiftSubalgebra F v w marked t) :
    lieQuotientMap (markedShiftSecondIdeal F v w marked t) (markedShiftTranslate F v w marked hw hv t h x) =
      lieQuotientMap (markedShiftSecondIdeal F v w marked t) x +
        ⁅markedQuotientDirection F v w marked t h, lieQuotientMap (markedShiftSecondIdeal F v w marked t) x⁆ := by
  have he := (lieQuotientMap_eq_zero (markedShiftSecondIdeal F v w marked t)
    (markedShiftTranslate F v w marked hw hv t h x - x - ⁅markedShiftDirection F v w marked t h, x⁆)).mpr
      (markedShiftTranslate_first_order F v w marked hw hv t h x)
  rw [map_sub, map_sub, LieHom.map_lie] at he
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp he)).trans (add_comm _ _)

noncomputable def markedQuotientTranslate (h : Fin t → ℚ) :
    MarkedShiftQuotient F v w marked t →ₗ[ℚ] MarkedShiftQuotient F v w marked t :=
  (markedShiftSecondIdeal F v w marked t).toSubmodule.liftQ
    ((lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.comp
      (markedShiftTranslate F v w marked hw hv t h)) (by
        intro x hx
        exact (lieQuotientMap_eq_zero _ _).mpr (markedShiftTranslate_second_mem F v w marked hw hv t h hx))

theorem markedQuotientTranslate_first_order (h : Fin t → ℚ) (x : MarkedShiftQuotient F v w marked t) :
    markedQuotientTranslate F v w marked hw hv t h x = x + ⁅markedQuotientDirection F v w marked t h, x⁆ := by
  obtain ⟨z, rfl⟩ := lieQuotientMap_surjective (markedShiftSecondIdeal F v w marked t) x
  exact markedShiftTranslate_quotient F v w marked hw hv t h z

end Erdos3

end

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)

noncomputable def markedShiftQuotientLayer (t : ℕ) (a : Fin 2 → ℕ) :
    Submodule ℚ (MarkedShiftQuotient F v w marked t) :=
  (markedShiftBiLayer F v w marked t (a 0) (a 1)).map
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap

theorem markedShiftQuotientLayer_antitone (t : ℕ) :
    Antitone (markedShiftQuotientLayer F v w marked t) := by
  intro a b hab
  exact Submodule.map_mono (markedShiftBiLayer_antitone F v w marked t (hab 0) (hab 1))

theorem markedShiftQuotientLayer_zero (t : ℕ) : markedShiftQuotientLayer F v w marked t 0 = ⊤ := by
  change (markedShiftBiLayer F v w marked t 0 0).map _ = ⊤
  rw [markedShiftBiLayer_zero, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (lieQuotientMap_surjective _)

theorem markedShiftQuotientLayer_lie_mem (t : ℕ) {a b : Fin 2 → ℕ}
    {x y : MarkedShiftQuotient F v w marked t}
    (hx : x ∈ markedShiftQuotientLayer F v w marked t a)
    (hy : y ∈ markedShiftQuotientLayer F v w marked t b) :
    ⁅x, y⁆ ∈ markedShiftQuotientLayer F v w marked t (a + b) := by
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  exact ⟨⁅p, q⁆, markedShiftBiLayer_lie_mem F v w marked t hp hq,
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).map_lie p q⟩

theorem markedShiftQuotientLayer_eq_bot_of_le (t : ℕ) (a : Fin 2 → ℕ)
    (ha : markedShiftBiLayer F v w marked t (a 0) (a 1) ≤
      (markedShiftSecondIdeal F v w marked t).toSubmodule) :
    markedShiftQuotientLayer F v w marked t a = ⊥ := by
  apply bot_unique
  rintro x ⟨y, hy, rfl⟩
  exact (lieQuotientMap_eq_zero _ y).mpr (ha hy)

theorem markedShiftQuotientLayer_terminal
    (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ) (a : Fin 2 → ℕ)
    (ha : ¬a ≤ mixedCorrelationDegree s) : markedShiftQuotientLayer F v w marked t a = ⊥ := by
  have hnot : ¬(a 0 ≤ 1 ∧ a 1 ≤ s) := by
    intro h
    apply ha
    intro i
    fin_cases i
    · exact h.1
    · exact h.2
  have hcases : 1 < a 0 ∨ s < a 1 := by omega
  rcases hcases with hh | hn
  · apply markedShiftQuotientLayer_eq_bot_of_le F v w marked t a
    exact (markedShiftBiLayer_antitone F v w marked t (by omega : 2 ≤ a 0) (Nat.zero_le _)).trans
      (markedShiftBiLayer_second F v w marked t).le
  · have hzero : markedShiftBiLayer F v w marked t (a 0) (a 1) = ⊥ := by
      apply bot_unique
      exact (markedShiftBiLayer_antitone F v w marked t le_rfl (by omega : s + 1 ≤ a 1)).trans
        (markedShiftBiLayer_degree_terminal F v w marked hv t (a 0)).le
    unfold markedShiftQuotientLayer
    rw [hzero, Submodule.map_bot]

theorem markedShiftQuotientLayer_positive (hw : ∀ i, 0 < w i) (t : ℕ) :
    markedShiftQuotientLayer F v w marked t (correlationInput 0 1) ⊔
      markedShiftQuotientLayer F v w marked t (correlationInput 1 0) = ⊤ := by
  change (markedShiftBiLayer F v w marked t 0 1).map _ ⊔
    (markedShiftBiLayer F v w marked t 1 0).map _ = ⊤
  rw [← Submodule.map_sup, markedShiftBiLayer_positive F v w marked hw t, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (lieQuotientMap_surjective _)

theorem markedShiftQuotientLayer_total_one (hw : ∀ i, 0 < w i) (t : ℕ) :
    multidegreeTotalLayer (markedShiftQuotientLayer F v w marked t) 1 = ⊤ := by
  apply top_unique
  rw [← markedShiftQuotientLayer_positive F v w marked hw t]
  apply sup_le
  · apply layer_le_multidegreeTotalLayer _ (correlationInput 0 1) 1
    decide
  · apply layer_le_multidegreeTotalLayer _ (correlationInput 1 0) 1
    decide

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial

variable {I σ ι L : Type*} [Fintype I] [Fintype σ] [Fintype ι]
  [LieRing L] [LieAlgebra ℚ L]

theorem finiteMarkedPolynomialValues_coefficient_height
    (b : Basis ι ℚ L) (v : I → L) (w : I → ℕ) (marked : I → Bool) {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (hv : ∀ i j, RationalHeightLE (b.repr (v i) j) H) (s d k l : ℕ)
    {p : VectorPolynomial σ ℚ L} (hp : p ∈ finiteMarkedPolynomialValues v w marked s d k l)
    (α : σ →₀ ℕ) (j : ι) :
    RationalHeightLE (b.repr (coefficients p α) j) (lieTreeHeight (Fintype.card ι) H s) := by
  classical
  obtain ⟨β, _, hβ⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hβ
  rw [coefficients_monomial]
  by_cases h : β = α
  · subst β
    rw [Finsupp.single_eq_same]
    exact finiteMarkedLieValues_coordinate_height b v w marked hc hv s d _ l hx j
  · rw [Finsupp.single_eq_of_ne (Ne.symm h), map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero (hH.trans (lieTreeHeight_ge_input _ _ _))

variable {s r : ℕ} (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
  (hv : ∀ i, v i ∈ F.layer (w i) 1) {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

omit [Fintype σ] in
include hH hc hgen in
theorem markedShiftGenerator_coordinate_height (t h n : ℕ)
    (i : MarkedShiftGeneratorIndex (s := s) v w marked t h n)
    (j : NilpotentLieFiltration.AdaptedBasisIndex (fun _ : Fin t => 1) ω ⊕ Fin t) :
    RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (markedShiftGenerator F v w marked hw hv t h n i).val j)
      (lieTreeHeight (Fintype.card ι) H s) := by
  have hbound := hH.trans (lieTreeHeight_ge_input (Fintype.card ι) H s)
  rcases i with p | i
  · rcases j with z | j
    · rw [F.associatedDegree.polynomialShiftBasis_repr_inl]
      exact finiteMarkedPolynomialValues_coefficient_height b v w marked hH hc hgen s n h 0
        p.property z.val.1 z.val.2
    · rw [F.associatedDegree.polynomialShiftBasis_repr_inr]
      exact rationalHeightLE_zero hbound
  · rcases j with z | j
    · rw [F.associatedDegree.polynomialShiftBasis_repr_inl]
      change RationalHeightLE (b.repr (coefficients (0 : VectorPolynomial (Fin t) ℚ L) z.val.1) z.val.2) _
      simp only [map_zero, Finsupp.zero_apply]
      exact rationalHeightLE_zero hbound
    · rw [F.associatedDegree.polynomialShiftBasis_repr_inr]
      change RationalHeightLE ((RationalTorus.basis t).repr (RationalTorus.basis t i.val) j) _
      exact (basis_repr_height_one (RationalTorus.basis t) i.val j).mono hbound

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CommonDependentPolynomialIntersections
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {σ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

noncomputable def dependentPolynomialLayer (d k l : ℕ) :
    Submodule ℚ (VectorPolynomial σ ℚ D.CoefficientFreeLieAlgebra) :=
  markedPolynomialLayer D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent d k l

theorem coefficientFreeSpan_le_dependentWordLayer (d : Fin s) :
    D.coefficientFreeSpan d ≤ D.dependentWordLayer (d.val + 1) 0 1 :=
  sup_le (D.commonFreeSpan_le_dependentWordLayer d)
    ((D.dependentFreeSpan_le_dependentWordLayer d).trans
      (D.dependentWordLayer_antitone le_rfl (Nat.zero_le 1) le_rfl))

variable {Q : ℝ} (B : D.CoefficientBases Q)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {σ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

variable {Q : ℝ} (B : D.CoefficientBases Q)

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NormalizedMarkedPhase
namespace OAI

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t : ℕ)

noncomputable def markedShiftPhase :
    markedShiftSubalgebra F v w marked t →ₗ⁅ℚ⁆ RationalTorus.Algebra t where
  toFun x := x.val.right
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

noncomputable def markedQuotientPhase :
    MarkedShiftQuotient F v w marked t →ₗ⁅ℚ⁆ RationalTorus.Algebra t :=
  lieQuotientDescend (markedShiftSecondIdeal F v w marked t)
    (markedShiftPhase F v w marked t) (fun _ hx => hx.1)

theorem markedQuotientPhase_direction (a : Fin t → ℚ) :
    markedQuotientPhase F v w marked t (markedQuotientDirection F v w marked t a) = a := rfl

noncomputable def markedQuotientPolynomialAlgebra :
    LieSubalgebra ℚ (MarkedShiftQuotient F v w marked t) :=
  (markedQuotientPhase F v w marked t).ker.toLieSubalgebra

theorem exists_zero_phase_lift (x : MarkedShiftQuotient F v w marked t)
    (hx : markedQuotientPhase F v w marked t x = 0) :
    ∃ p : markedShiftSubalgebra F v w marked t,
      p.val.right = 0 ∧ lieQuotientMap (markedShiftSecondIdeal F v w marked t) p = x := by
  obtain ⟨p, rfl⟩ := lieQuotientMap_surjective (markedShiftSecondIdeal F v w marked t) x
  exact ⟨p, hx, rfl⟩

end Erdos3

end

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t : ℕ)
  (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)
  (hphase : ∀ z : D.filtration.Group, z ∈ D.lattice →
    IntegralVector (markedQuotientPhase F v w marked t z.coord))

variable [TopologicalSpace (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
  [T2Space (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]

end Erdos3

end

section

namespace Erdos3

theorem rationalLogHeight_nat_inv_mul_exp_bound (m : ℕ) (hm : 0 < m)
    {p : ℝ} (hp : 0 ≤ p) (hmp : (m : ℝ) ≤ Real.exp p) {x : ℚ}
    (hx : rationalLogHeight x ≤ p) :
    rationalLogHeight ((m : ℚ)⁻¹ * x) ≤ 2 * p + 1 := by
  have hmheight : RationalHeightLE (m : ℚ) m := by
    simp only [RationalHeightLE, Rat.num_natCast, Rat.den_natCast, Int.natAbs_natCast]
    exact ⟨le_rfl, hm⟩
  have hinv := hmheight.inv (by exact_mod_cast hm.ne')
  apply rationalLogHeight_le_of_height (hinv.mul (rationalHeightLE_ceil_exp hx))
  rw [Nat.cast_mul]
  calc
    (m : ℝ) * ⌈Real.exp p⌉₊ ≤ Real.exp p * Real.exp (p + 1) :=
      mul_le_mul hmp (ceil_exp_le_exp_add_one hp) (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (2 * p + 1) := by rw [← Real.exp_add]; congr 1; ring

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t m : ℕ)

noncomputable def normalizedMarkedPhase :
    MarkedShiftQuotient F v w marked t →ₗ⁅ℚ⁆ RationalTorus.Algebra t where
  toLinearMap := (m : ℚ)⁻¹ • (markedQuotientPhase F v w marked t).toLinearMap
  map_lie' {x y} := by
    change (m : ℚ)⁻¹ • markedQuotientPhase F v w marked t ⁅x, y⁆ = 0
    rw [(markedQuotientPhase F v w marked t).map_lie, RationalTorus.lie_eq_zero, smul_zero]

theorem normalizedMarkedPhase_apply (x : MarkedShiftQuotient F v w marked t) :
    normalizedMarkedPhase F v w marked t m x =
      (m : ℚ)⁻¹ • markedQuotientPhase F v w marked t x := rfl

theorem normalizedMarkedPhase_scaled_direction (hm : 0 < m) (a : Fin t → ℚ) :
    normalizedMarkedPhase F v w marked t m
      ((m : ℚ) • markedQuotientDirection F v w marked t a) = a := by
  rw [normalizedMarkedPhase_apply, map_smul, markedQuotientPhase_direction]
  change (m : ℚ)⁻¹ • ((m : ℚ) • a) = a
  rw [smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast hm.ne' : (m : ℚ) ≠ 0), one_smul]

theorem normalizedMarkedPhase_height {p : ℝ} (hm : 0 < m) (hp : 0 ≤ p)
    (hmp : (m : ℝ) ≤ Real.exp p) (x : MarkedShiftQuotient F v w marked t) (i : Fin t)
    (hx : rationalLogHeight (markedQuotientPhase F v w marked t x i) ≤ p) :
    rationalLogHeight (normalizedMarkedPhase F v w marked t m x i) ≤ 2 * p + 1 :=
  rationalLogHeight_nat_inv_mul_exp_bound m hm hp hmp hx

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedPureEvaluation
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t : ℕ)

theorem markedShiftEval_lie_of_zero_phase (a : Fin t → ℚ)
    (p q : markedShiftSubalgebra F v w marked t)
    (hp : p.val.right = 0) (hq : q.val.right = 0) :
    markedShiftEval F v w marked t a ⁅p, q⁆ =
      ⁅markedShiftEval F v w marked t a p, markedShiftEval F v w marked t a q⁆ := by
  have hz (p : VectorPolynomial (Fin t) ℚ L) : directionalDerivative (0 : Fin t → ℚ) p = 0 := by
    simp only [directionalDerivative, Pi.zero_apply, zero_smul, Finset.sum_const_zero, LinearMap.zero_apply]
  change eval a (⁅p.val.left.val, q.val.left.val⁆ + directionalDerivative p.val.right q.val.left.val -
    directionalDerivative q.val.right p.val.left.val) = ⁅eval a p.val.left.val, eval a q.val.left.val⁆
  rw [hp, hq]
  change eval a (⁅p.val.left.val, q.val.left.val⁆ +
    directionalDerivative (0 : Fin t → ℚ) q.val.left.val -
    directionalDerivative (0 : Fin t → ℚ) p.val.left.val) = _
  rw [hz, hz, add_zero, sub_zero]
  exact (evalLie a).map_lie _ _

variable (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)

noncomputable def markedBaseEvaluation (a : Fin t → ℚ) :
    MarkedShiftQuotient F v w marked t →ₗ[ℚ] (L ⧸ J) :=
  (markedShiftSecondIdeal F v w marked t).toSubmodule.liftQ
    ((lieQuotientMap J).toLinearMap.comp (markedShiftEval F v w marked t a)) (by
      intro p hp
      exact (lieQuotientMap_eq_zero J _).mpr (hJ (markedPolynomialLayer_eval_mem v w marked hp.2 a)))

theorem markedBaseEvaluation_map (a : Fin t → ℚ) (p : markedShiftSubalgebra F v w marked t) :
    markedBaseEvaluation F v w marked t J hJ a (lieQuotientMap (markedShiftSecondIdeal F v w marked t) p) =
      lieQuotientMap J (markedShiftEval F v w marked t a p) := rfl

theorem markedBaseEvaluation_lie (a : Fin t → ℚ) (x y : MarkedShiftQuotient F v w marked t)
    (hx : markedQuotientPhase F v w marked t x = 0) (hy : markedQuotientPhase F v w marked t y = 0) :
    markedBaseEvaluation F v w marked t J hJ a ⁅x, y⁆ =
      ⁅markedBaseEvaluation F v w marked t J hJ a x, markedBaseEvaluation F v w marked t J hJ a y⁆ := by
  obtain ⟨p, hp, rfl⟩ := exists_zero_phase_lift F v w marked t x hx
  obtain ⟨q, hq, rfl⟩ := exists_zero_phase_lift F v w marked t y hy
  rw [← (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).map_lie]
  change lieQuotientMap J (markedShiftEval F v w marked t a ⁅p, q⁆) =
    ⁅lieQuotientMap J (markedShiftEval F v w marked t a p),
      lieQuotientMap J (markedShiftEval F v w marked t a q)⁆
  rw [markedShiftEval_lie_of_zero_phase F v w marked t a p q hp hq]
  exact (lieQuotientMap J).map_lie _ _

noncomputable def markedBaseEvaluationLie (a : Fin t → ℚ) :
    markedQuotientPolynomialAlgebra F v w marked t →ₗ⁅ℚ⁆ (L ⧸ J) where
  toLinearMap := (markedBaseEvaluation F v w marked t J hJ a).comp
    (markedQuotientPolynomialAlgebra F v w marked t).toSubmodule.subtype
  map_lie' {x y} := markedBaseEvaluation_lie F v w marked t J hJ a x.val y.val x.property y.property

theorem markedBaseEvaluation_real_map (a : Fin t → ℚ)
    (p : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    (markedBaseEvaluation F v w marked t J hJ a).baseChange ℝ
        ((lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ p) =
      (lieQuotientMap J).toLinearMap.baseChange ℝ ((markedShiftEval F v w marked t a).baseChange ℝ p) := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul c p =>
    simp only [LinearMap.baseChange_tmul]
    rfl
  | add p q hp hq => simp only [map_add, hp, hq]

end Erdos3

end

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

def monoidHomOfSurjectiveComposition {A B C : Type*} [Monoid A] [Monoid B] [Monoid C]
    (f : A →* B) (hf : Function.Surjective f) (g : A →* C) (k : B → C)
    (hcomp : ∀ a, k (f a) = g a) : B →* C where
  toFun := k
  map_one' := by
    calc
      k 1 = k (f 1) := congrArg k f.map_one.symm
      _ = g 1 := hcomp 1
      _ = 1 := g.map_one
  map_mul' x y := by
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    rw [← f.map_mul, hcomp, hcomp, hcomp, g.map_mul]

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d e u : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool) (t : ℕ)
  (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)
  (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
  (E : RationalFilteredNilmanifold (L ⧸ J) u e) (a : Fin t → ℚ)

theorem markedBaseEvaluation_real_incl
    (z : ℝ ⊗[ℚ] markedQuotientPolynomialAlgebra F v w marked t) :
    (markedBaseEvaluation F v w marked t J hJ a).baseChange ℝ
      ((markedQuotientPolynomialAlgebra F v w marked t).incl.toLinearMap.baseChange ℝ z) =
      (markedBaseEvaluationLie F v w marked t J hJ a).toLinearMap.baseChange ℝ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c z => simp only [LinearMap.baseChange_tmul]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def markedPureEvaluation
    (g : realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (markedQuotientPolynomialAlgebra F v w marked t)) : E.RealGroup :=
  ⟨(markedBaseEvaluation F v w marked t J hJ a).baseChange ℝ g.val.coord⟩

theorem markedPureEvaluation_inclusion
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] markedQuotientPolynomialAlgebra F v w marked t) (s + 1)
      (realification_lowerCentralSeries_eq_bot (lie_subalgebra_lowerCentralSeries_eq_bot
        D.filtration.lowerCentralSeries_eq_bot (markedQuotientPolynomialAlgebra F v w marked t)))) :
    markedPureEvaluation F v w marked t D J hJ E a
      (realificationSubgroupHom (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (markedQuotientPolynomialAlgebra F v w marked t) g) =
      realificationMap
        (hnil := lie_subalgebra_lowerCentralSeries_eq_bot D.filtration.lowerCentralSeries_eq_bot
          (markedQuotientPolynomialAlgebra F v w marked t))
        (hM := E.filtration.lowerCentralSeries_eq_bot)
        (markedBaseEvaluationLie F v w marked t J hJ a) g := by
  apply NilpotentLieBCHGroup.ext
  exact markedBaseEvaluation_real_incl F v w marked t J hJ a g.coord

noncomputable def markedPureEvaluationHom :
    realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (markedQuotientPolynomialAlgebra F v w marked t) →* E.RealGroup :=
  monoidHomOfSurjectiveComposition
    (realificationSubgroupHom (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (markedQuotientPolynomialAlgebra F v w marked t))
    (realificationSubgroupHom_surjective (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (markedQuotientPolynomialAlgebra F v w marked t))
    (realificationMap
      (hnil := lie_subalgebra_lowerCentralSeries_eq_bot D.filtration.lowerCentralSeries_eq_bot
        (markedQuotientPolynomialAlgebra F v w marked t))
      (hM := E.filtration.lowerCentralSeries_eq_bot) (markedBaseEvaluationLie F v w marked t J hJ a))
    (markedPureEvaluation F v w marked t D J hJ E a)
    (markedPureEvaluation_inclusion F v w marked t D J hJ E a)

variable (hmap : ∀ z : D.RealGroup, z ∈ D.realLattice →
  (⟨(markedBaseEvaluation F v w marked t J hJ a).baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice)

include hmap in
theorem markedPureEvaluationHom_lattice :
    D.realLattice.comap (realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (markedQuotientPolynomialAlgebra F v w marked t)).subtype ≤
        E.realLattice.comap (markedPureEvaluationHom F v w marked t D J hJ E a) := by
  intro g hg
  exact hmap g.val hg

noncomputable def markedPureSpaceMap :
    (realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (markedQuotientPolynomialAlgebra F v w marked t) ⧸
        D.realLattice.comap (realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (markedQuotientPolynomialAlgebra F v w marked t)).subtype) → E.Space :=
  cosetMap _ _ (markedPureEvaluationHom F v w marked t D J hJ E a)
    (markedPureEvaluationHom_lattice F v w marked t D J hJ E a hmap)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MarkedProjectionBounds
namespace OAI

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
  (hv : ∀ i, v i ∈ F.layer (w i) 1) {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

end Erdos3

end

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
  (hv : ∀ i, v i ∈ F.layer (w i) 1) {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial

variable {I ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r d q : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (e : Basis (Fin d) ℚ (markedShiftSubalgebra F v w marked t))
  {H : ℕ} (he : ∀ i j, RationalHeightLE
    ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr (e i).val j) H)

include he

omit [Fintype ι] in
theorem markedShiftPhase_coordinate_height (i : Fin t) (j : Fin d) :
    RationalHeightLE ((RationalTorus.basis t).repr (markedShiftPhase F v w marked t (e j)) i) H := by
  have h := he j (Sum.inr i)
  rw [F.associatedDegree.polynomialShiftBasis_repr_inr] at h
  exact h

omit [Fintype ι] in
theorem markedShiftEval_zero_coordinate_height (i : ι) (j : Fin d) :
    RationalHeightLE (b.repr (markedShiftEval F v w marked t 0 (e j)) i) H := by
  let z : NilpotentLieFiltration.AdaptedBasisIndex (fun _ : Fin t => 1) ω :=
    ⟨(0, i), by simp⟩
  have h := he j (Sum.inl z)
  rw [F.associatedDegree.polynomialShiftBasis_repr_inl] at h
  change RationalHeightLE (b.repr (eval (fun _ => 0) (e j).val.left.val) i) H
  rw [eval_zero_eq_coefficient]
  exact h

variable (f : Basis (Fin q) ℚ (MarkedShiftQuotient F v w marked t))
  {Q : ℕ} (hQ : 1 ≤ Q)
  (hf : ∀ i j, RationalHeightLE
    (f.repr (lieQuotientMap (markedShiftSecondIdeal F v w marked t) (e j)) i) Q)

include hQ hf

omit [Fintype ι] in
theorem markedQuotientPhase_coordinate_height (i : Fin t) (j : Fin q) :
    RationalHeightLE ((RationalTorus.basis t).repr (markedQuotientPhase F v w marked t (f j)) i)
      ((d + 1) * (rationalSolveHeight q Q * H) ^ d) := by
  have h := descended_linear_map_coordinate_height e f (RationalTorus.basis t)
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap
    (lieQuotientMap_surjective _) (markedQuotientPhase F v w marked t).toLinearMap hQ hf
    (fun i j => markedShiftPhase_coordinate_height F v w marked t b ω hF e he i j) i j
  change RationalHeightLE ((RationalTorus.basis t).repr
    (markedQuotientPhase F v w marked t (f j)) i)
    ((Fintype.card (Fin d) + 1) * (rationalSolveHeight (Fintype.card (Fin q)) Q * H) ^
      Fintype.card (Fin d)) at h
  simpa only [Fintype.card_fin] using h

variable {ν : Type*} (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
  (c : Basis ν ℚ (L ⧸ J)) {K : ℕ}
  (hc : ∀ i j, RationalHeightLE (c.repr (lieQuotientMap J (b j)) i) K)

include hc

theorem markedBaseEvaluation_zero_coordinate_height (i : ν) (j : Fin q) :
    RationalHeightLE (c.repr (markedBaseEvaluation F v w marked t J hJ 0 (f j)) i)
      ((d + 1) * (rationalSolveHeight q Q * ((Fintype.card ι + 1) * (H * K) ^ Fintype.card ι)) ^ d) := by
  have hcomp (i j) : RationalHeightLE
      (c.repr (markedBaseEvaluation F v w marked t J hJ 0
        (lieQuotientMap (markedShiftSecondIdeal F v w marked t) (e j))) i)
      ((Fintype.card ι + 1) * (H * K) ^ Fintype.card ι) := by
    rw [markedBaseEvaluation_map]
    exact linearMap_coordinate_height b c (lieQuotientMap J).toLinearMap
      (fun j i => hc i j) (markedShiftEval F v w marked t 0 (e j))
      (fun i => markedShiftEval_zero_coordinate_height F v w marked t b ω hF e he i j) i
  have h := descended_linear_map_coordinate_height e f c
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap
    (lieQuotientMap_surjective _) (markedBaseEvaluation F v w marked t J hJ 0)
    hQ hf hcomp i j
  simpa only [Fintype.card_fin] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MarkedDirectionCoordinates
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial

variable {I ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ)

noncomputable def markedShiftDirectionLinear :
    RationalTorus.Algebra t →ₗ[ℚ] markedShiftSubalgebra F v w marked t where
  toFun := markedShiftDirection F v w marked t
  map_add' h k := by
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · apply Subtype.ext
      exact (zero_add (0 : VectorPolynomial (Fin t) ℚ L)).symm
    · rfl
  map_smul' a h := by
    apply Subtype.ext
    apply LieAlgebra.SemiDirectSum.ext
    · apply Subtype.ext
      exact (smul_zero a).symm
    · rfl

noncomputable def markedQuotientDirectionLinear :
    RationalTorus.Algebra t →ₗ[ℚ] MarkedShiftQuotient F v w marked t :=
  (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.comp
    (markedShiftDirectionLinear F v w marked t)

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

omit [Fintype ι] in
theorem markedShiftDirection_ambient_height (i : Fin t)
    (j : NilpotentLieFiltration.AdaptedBasisIndex (fun _ : Fin t => 1) ω ⊕ Fin t) :
    RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (markedShiftDirection F v w marked t (RationalTorus.basis t i)).val j) 1 := by
  rcases j with z | j
  · rw [F.associatedDegree.polynomialShiftBasis_repr_inl]
    change RationalHeightLE (b.repr (coefficients (0 : VectorPolynomial (Fin t) ℚ L) z.val.1) z.val.2) 1
    simp only [map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero le_rfl
  · rw [F.associatedDegree.polynomialShiftBasis_repr_inr]
    exact basis_repr_height_one (RationalTorus.basis t) i j

theorem markedShiftDirection_coordinate_height (hω : ∀ i, ω i ≤ s) {H : ℕ} (hH : 1 ≤ H)
    (e : Basis (Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) ℚ
      (markedShiftSubalgebra F v w marked t))
    (he : ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (e i).val j) H) (i : Fin t) (j : Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) :
    RationalHeightLE (e.repr (markedShiftDirection F v w marked t (RationalTorus.basis t i)) j)
      ((finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t) + 1) *
        (rationalSolveHeight (finrank ℚ (markedShiftSubalgebra F v w marked t)) H * H) ^
          finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)) := by
  classical
  let _ : Fintype (NilpotentLieFiltration.AdaptedBasisIndex (fun _ : Fin t => 1) ω) :=
    NilpotentLieFiltration.adaptedBasisIndexFintype (fun _ : Fin t => 1) ω s (by simp) hω
  have hb := embedding_basis_coordinate_height e (F.associatedDegree.polynomialShiftBasis b ω hF t)
    (markedShiftSubalgebra F v w marked t).incl.toLinearMap
    (fun _ _ h => Subtype.ext h) hH (fun j i => he i j)
    (markedShiftDirection F v w marked t (RationalTorus.basis t i))
    (fun j => (markedShiftDirection_ambient_height F v w marked t b ω hF i j).mono hH) j
  simpa only [Fintype.card_fin,
    ← finrank_eq_card_basis (F.associatedDegree.polynomialShiftBasis b ω hF t)] using hb

theorem markedQuotientDirection_coordinate_height (hω : ∀ i, ω i ≤ s) {H Q q : ℕ} (hH : 1 ≤ H)
    (e : Basis (Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) ℚ
      (markedShiftSubalgebra F v w marked t))
    (he : ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (e i).val j) H) (f : Basis (Fin q) ℚ (MarkedShiftQuotient F v w marked t))
    (hf : ∀ i j, RationalHeightLE
      (f.repr (lieQuotientMap (markedShiftSecondIdeal F v w marked t) (e j)) i) Q)
    (i : Fin t) (j : Fin q) :
    let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
    let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
    let B := (a + 1) * (rationalSolveHeight d H * H) ^ a
    RationalHeightLE (f.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j)
      ((d + 1) * (B * Q) ^ d) := by
  have hb := linearMap_coordinate_height e f (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap
    (fun j i => hf i j) (markedShiftDirection F v w marked t (RationalTorus.basis t i))
    (markedShiftDirection_coordinate_height F v w marked t b ω hF hω hH e he i) j
  simp only [Fintype.card_fin] at hb
  exact hb

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonMarkedMultidegree
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mixedCorrelationDegree_sum (s : ℕ) : (∑ i, mixedCorrelationDegree s i) = s + 1 := by
  rw [Fin.sum_univ_two]
  change 1 + s = s + 1
  omega

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)

noncomputable def markedShiftMultidegree (t : ℕ) :
    MultidegreeLieFiltration (Fin 2) (MarkedShiftQuotient F v w marked t) (s + 1)
      (mixedCorrelationDegree s) :=
  MultidegreeLieFiltration.ofLayers (markedShiftQuotientLayer F v w marked t)
    (markedShiftQuotientLayer_antitone F v w marked t) (markedShiftQuotientLayer_zero F v w marked t)
    (markedShiftQuotientLayer_lie_mem F v w marked t) (markedShiftQuotientLayer_total_one F v w marked hw t)
    (mixedCorrelationDegree s) (markedShiftQuotientLayer_terminal F v w marked hv t) (s + 1)
    (by rw [mixedCorrelationDegree_sum])

@[simp] theorem markedShiftMultidegree_layer (t : ℕ) (a : Fin 2 → ℕ) :
    (markedShiftMultidegree F v w marked hw hv t).layer a = markedShiftQuotientLayer F v w marked t a := rfl

end Erdos3

end

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

noncomputable def realMarkedDirection (h : Fin t → ℚ) : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t :=
  rationalLieInclusion (markedQuotientDirection F v w marked t h)

theorem realMarkedTranslate_first_order (h : Fin t → ℚ) (x : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    (markedQuotientTranslate F v w marked hw hv t h).baseChange ℝ x =
      x + ⁅realMarkedDirection F v w marked t h, x⁆ := by
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [lie_zero (L := ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) (M := ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
    simp
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, markedQuotientTranslate_first_order, TensorProduct.tmul_add]
    change a ⊗ₜ[ℚ] x + a ⊗ₜ[ℚ] ⁅markedQuotientDirection F v w marked t h, x⁆ =
      a ⊗ₜ[ℚ] x + ⁅(1 : ℝ) ⊗ₜ[ℚ] markedQuotientDirection F v w marked t h, a ⊗ₜ[ℚ] x⁆
    rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul]
  | add x y hx hy =>
    rw [map_add, hx, hy, LieRing.lie_add]
    abel

theorem realMarkedTranslate_quotient (h : Fin t → ℚ)
    (x : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ
        ((markedShiftTranslate F v w marked hw hv t h).baseChange ℝ x) =
      (markedQuotientTranslate F v w marked hw hv t h).baseChange ℝ
        ((lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [LinearMap.baseChange_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realMarkedShiftEval_translate (h a : Fin t → ℚ)
    (x : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    (markedShiftEval F v w marked t a).baseChange ℝ
        ((markedShiftTranslate F v w marked hw hv t h).baseChange ℝ x) =
      (markedShiftEval F v w marked t (a + h)).baseChange ℝ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
      LinearMap.baseChange_tmul, markedShiftEval_translate]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ)

theorem markedQuotientDirection_smul (q : ℚ) (a : Fin t → ℚ) :
    markedQuotientDirection F v w marked t (q • a) =
      q • markedQuotientDirection F v w marked t a :=
  (markedQuotientDirectionLinear F v w marked t).map_smul q a

theorem markedDirection_mem_realLattice_of_smul {k d : ℕ}
    (E : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) k d)
    (q : ℚ) (a : Fin t → ℚ)
    (ha : (⟨q • markedQuotientDirection F v w marked t a⟩ : E.filtration.Group) ∈ E.lattice) :
    (⟨realMarkedDirection F v w marked t (q • a)⟩ : E.RealGroup) ∈ E.realLattice := by
  refine Subgroup.mem_map.mpr ⟨⟨q • markedQuotientDirection F v w marked t a⟩, ha, ?_⟩
  apply NilpotentLieBCHGroup.ext
  exact congrArg rationalLieInclusion (markedQuotientDirection_smul F v w marked t q a).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

noncomputable def rationalMarkedDirectionMap :
    (Fin t → ℚ) →ₗ[ℚ] (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :=
  rationalLieInclusion.toLinearMap.comp (markedQuotientDirectionLinear F v w marked t)

theorem rationalMarkedDirectionMap_apply (a : Fin t → ℚ) :
    rationalMarkedDirectionMap F v w marked t a = realMarkedDirection F v w marked t a := rfl

noncomputable def realMarkedParameterDirection :
    (Fin t → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :=
  realDirectionExtension (rationalMarkedDirectionMap F v w marked t)

theorem realMarkedParameterDirection_apply (a : Fin t → ℝ) :
    realMarkedParameterDirection F v w marked t a =
      ∑ i, a i • realMarkedDirection F v w marked t (Pi.single i 1) := by
  rw [realMarkedParameterDirection, realDirectionExtension_apply]
  simp only [rationalMarkedDirectionMap_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun h : Fin t → ℚ => a i • realMarkedDirection F v w marked t h)
  funext j
  by_cases hij : i = j <;> simp [hij, eq_comm]

theorem realMarkedParameterDirection_rat (a : Fin t → ℚ) :
    realMarkedParameterDirection F v w marked t (fun i => (a i : ℝ)) =
      realMarkedDirection F v w marked t a :=
  realDirectionExtension_rat (rationalMarkedDirectionMap F v w marked t) a

theorem markedQuotientDirection_mem_first (a : Fin t → ℚ) :
    markedQuotientDirection F v w marked t a ∈
      markedShiftQuotientLayer F v w marked t (correlationInput 1 0) := by
  refine ⟨markedShiftDirection F v w marked t a, ?_, rfl⟩
  refine ⟨(markedPolynomialLayer v w marked 0 1 0).zero_mem, ?_⟩
  intro h
  change 0 ≠ 0 ∨ 1 < 1 at h
  omega

theorem realMarkedDirection_mem_first (a : Fin t → ℚ) :
    realMarkedDirection F v w marked t a ∈
      (markedShiftMultidegree F v w marked hw hv t).realification.layer (correlationInput 1 0) :=
  Submodule.tmul_mem_baseChange_of_mem 1 (markedQuotientDirection_mem_first F v w marked t a)

theorem realMarkedParameterDirection_mem_first (a : Fin t → ℝ) :
    realMarkedParameterDirection F v w marked t a ∈
      (markedShiftMultidegree F v w marked hw hv t).realification.layer (correlationInput 1 0) := by
  change realMarkedParameterDirection F v w marked t a ∈
    (markedShiftQuotientLayer F v w marked t (correlationInput 1 0)).baseChange ℝ
  rw [realMarkedParameterDirection_apply]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (realMarkedDirection_mem_first F v w marked hw hv t (Pi.single i 1))

end Erdos3

end

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

theorem marked_first_layer_bracket_zero
    {x y : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t}
    (hx : x ∈ (markedShiftMultidegree F v w marked hw hv t).realification.layer (correlationInput 1 0))
    (hy : y ∈ (markedShiftMultidegree F v w marked hw hv t).realification.layer (correlationInput 1 0)) :
    ⁅x, y⁆ = 0 := by
  let M := (markedShiftMultidegree F v w marked hw hv t).realification
  have h := M.lie_mem hx hy
  have he : correlationInput (1 : ℕ) 0 + correlationInput 1 0 = correlationInput 2 0 := by
    funext i
    fin_cases i <;> rfl
  have ht : M.layer (correlationInput 2 0) = ⊥ := M.terminal _ (by
    intro hle
    have hh := hle 0
    exact Nat.not_succ_le_self 1 hh)
  rw [he, ht] at h
  exact h

include hw hv in
theorem realMarkedParameterDirection_lie (a b : Fin t → ℝ) :
    ⁅realMarkedParameterDirection F v w marked t a, realMarkedParameterDirection F v w marked t b⁆ = 0 :=
  marked_first_layer_bracket_zero F v w marked hw hv t
    (realMarkedParameterDirection_mem_first F v w marked hw hv t a)
    (realMarkedParameterDirection_mem_first F v w marked hw hv t b)

include hw hv in
theorem realMarkedParameterDirection_double_lie (a : Fin t → ℝ)
    (x : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    ⁅realMarkedParameterDirection F v w marked t a,
      ⁅realMarkedParameterDirection F v w marked t a, x⁆⁆ = 0 := by
  let M := (markedShiftMultidegree F v w marked hw hv t).realification
  have ha := realMarkedParameterDirection_mem_first F v w marked hw hv t a
  have hx : x ∈ M.layer 0 := by rw [M.zero_eq_top]; trivial
  have hb := M.lie_mem ha hx
  rw [add_zero] at hb
  exact marked_first_layer_bracket_zero F v w marked hw hv t ha hb

noncomputable def realMarkedParameterElement (a : Fin t → ℝ) :
    (markedShiftMultidegree F v w marked hw hv t).realification.Group :=
  ⟨realMarkedParameterDirection F v w marked t a⟩

theorem realMarkedParameterElement_mul (a b : Fin t → ℝ) :
    realMarkedParameterElement F v w marked hw hv t a *
      realMarkedParameterElement F v w marked hw hv t b =
        realMarkedParameterElement F v w marked hw hv t (a + b) := by
  apply NilpotentLieBCHGroup.ext
  change lieBCH (s + 1) (realMarkedParameterDirection F v w marked t a)
    (realMarkedParameterDirection F v w marked t b) = _
  rw [lieBCH_eq_add_of_lie_eq_zero
    (markedShiftMultidegree F v w marked hw hv t).realification.ordinary.lowerCentralSeries_eq_bot
    (realMarkedParameterDirection_lie F v w marked hw hv t a b)]
  exact ((realMarkedParameterDirection F v w marked t).map_add a b).symm

theorem realMarkedParameterElement_inv (a : Fin t → ℝ) :
    (realMarkedParameterElement F v w marked hw hv t a)⁻¹ =
      realMarkedParameterElement F v w marked hw hv t (-a) := by
  apply NilpotentLieBCHGroup.ext
  exact ((realMarkedParameterDirection F v w marked t).map_neg a).symm

theorem realMarkedParameterElement_conjugation (hs : 1 ≤ s) (a : Fin t → ℝ)
    (x : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    conjugationCoord (realMarkedParameterElement F v w marked hw hv t a) x =
      x + ⁅realMarkedParameterDirection F v w marked t a, x⁆ :=
  conjugationCoord_eq_add_lie (by omega) _ x
    (realMarkedParameterDirection_double_lie F v w marked hw hv t a x)

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

noncomputable def markedQuotientMultidegree (t : ℕ) :
    MultidegreeLieFiltration (Fin 2)
      (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t) (s + 1) (mixedCorrelationDegree s) :=
  markedShiftMultidegree D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t

variable {Q : ℝ} (B : D.CoefficientBases Q)

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedEvaluationJointBounds
namespace OAI

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)

include hω hH hc in
theorem markedShiftBasis_structure_height (t : ℕ)
    (e : Basis (Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) ℚ
      (markedShiftSubalgebra F v w marked t))
    (he : ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (e i).val j) (lieTreeHeight (Fintype.card ι) H s)) :
    let U := max (lieTreeHeight (Fintype.card ι) H s) (s + 1)
    let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
    let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
    ∀ i j k, RationalHeightLE (lieStructureConstants e i j k)
      (rationalLieStructureHeight a (max U (rationalSolveHeight d U))) := by
  classical
  let U := max (lieTreeHeight (Fintype.card ι) H s) (s + 1)
  have hHU : H ≤ U := (lieTreeHeight_ge_input _ _ _).trans (Nat.le_max_left _ _)
  have hU : 1 ≤ U := hH.trans hHU
  let _ : Fintype (NilpotentLieFiltration.AdaptedBasisIndex (fun _ : Fin t => 1) ω) :=
    NilpotentLieFiltration.adaptedBasisIndexFintype (fun _ : Fin t => 1) ω s (by simp) hω
  let E := F.associatedDegree.polynomialShiftBasis b ω hF t
  have hCE (i j k) : RationalHeightLE (lieStructureConstants E i j k) U :=
    (F.associatedDegree.polynomialShiftBasis_structure_height b ω hF hω hH hc t i j k).mono
      (max_le hHU (Nat.le_max_right _ _))
  have hmatrix (i j) : RationalHeightLE
      (LinearMap.toMatrix e E (markedShiftSubalgebra F v w marked t).incl.toLinearMap i j) U := by
    rw [LinearMap.toMatrix_apply]
    exact (he j i).mono (Nat.le_max_left _ _)
  obtain ⟨_, _, _, hstructure⟩ := exists_bounded_lie_embedding_retraction e E
    (markedShiftSubalgebra F v w marked t).incl (fun _ _ h => Subtype.ext h) hU hCE hmatrix
  dsimp only
  intro i j k
  simpa only [Fintype.card_fin, ← finrank_eq_card_basis E] using hstructure i j k

end Erdos3

end

section

namespace Erdos3

open Module

def markedQuotientHeight (s n a d m q H : ℕ) : ℕ :=
  let T := lieTreeHeight n H s
  let U := max T (s + 1)
  let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
  let C := rationalLieStructureHeight a (max U (rationalSolveHeight d U))
  let Q := rationalKernelHeight m B
  let J := max 1 (max C Q)
  max (rationalLieStructureHeight d (max J (rationalSolveHeight q J)))
    ((d + 1) * (B * Q) ^ d)

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

end Erdos3

end

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

end Erdos3

end

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

end Erdos3

end

section

namespace Erdos3

open Module

def markedEvaluationHeight (s n a d m q H K : ℕ) : ℕ :=
  let T := lieTreeHeight n H s
  let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
  let Q := rationalKernelHeight m B
  max (markedQuotientHeight s n a d m q H)
    ((d + 1) * (rationalSolveHeight q Q * max T ((n + 1) * (T * K) ^ n)) ^ d)

variable {I ι ν L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

end Erdos3

end

end OAI

end


