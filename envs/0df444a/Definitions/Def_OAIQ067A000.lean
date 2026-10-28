-- Prove2me | Definitions.Def_OAIQ067A000
-- name    : OAIQ067A000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:18:52.977969+00:00
-- url     : https://prove2.me/theorems/c0763b8e-612e-47ac-9c6f-6d7a390e99f4
-- title:
--   Definitions bundle OAIQ067A000 of the split of OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 367 declarations of OpenAI's Lean: 107 definitions, 2 inductive types or structures, 3 instances and 255 theorems. The definitions and types are `OAI.FixedClauseThreshold.AuxiliaryClause`, `OAI.FixedClauseThreshold.CenterRegular`, `OAI.FixedClauseThreshold.Computability.ActiveClause`, `OAI.FixedClauseThreshold.Computability.BadIncident`, `OAI.FixedClauseThreshold.Computability.DeletionCandidate`, `OAI.FixedClauseThreshold.Computability.ExpressionTable`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.SiteExpressionDatum`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.arithmeticConstructorsRatPrimcodable`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.arithmeticEnclosuresRatPrimcodable`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.arithmeticSyntaxCodeEq`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.arithmeticSyntaxRatPrimcodable`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.binaryLogMeanExpression`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.binaryLogSumExpression`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.cavityExpressionsRatPrimcodable`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.clampBall`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.decodedRational`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.expApprox`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.expBall`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.exponentialExpression`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.expressionBall`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.expressionBound`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.expressionValue`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.interval`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.logApprox`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.logBall`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.logMixtureExpression`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.logQExpression`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.logTwoExpression`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.mixtureBound`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.mixtureExpression`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.physicalExpressionsRatPrimcodable`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.positiveLogExpression`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.rationalExpression`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.scaledLogExpression`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.signedExpression`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.sumExpressions`, `OAI.FixedClauseThreshold.Computability.FiniteArithmetic.weightedExpressionsRatPrimcodable`, `OAI.FixedClauseThreshold.Computability.IncidentClass`, `OAI.FixedClauseThreshold.Computability.SignedLiteral`, `OAI.FixedClauseThreshold.Computability.Triple` and 69 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `DilutedSpin_CavityBounds`, `DilutedSpin_FiniteEncoding`, `DilutedSpin_FiniteLaw`, `DilutedSpin_FiniteProducts`, `DilutedSpin_MeasureHierarchy`, `DilutedSpin_PhysicalIndex`, `DilutedSpin_QSubtreePotential`, `DilutedSpin_TrialPhysical`, `PeriodicLattice_Arithmetic`, `PeriodicLattice_EffectiveReals`, `PeriodicLattice_ElementaryFunctions`, `PeriodicLattice_RationalArithmetic`, `RandomSAT_CenterBounds`, `RandomSAT_CenterComparison`, `RandomSAT_ClauseProcess`, `RandomSAT_Clauses`, `RandomSAT_Concentration`, `RandomSAT_FiniteMean`, `RandomSAT_Forcing`, `RandomSAT_Interpolation`, `RandomSAT_Transfer`, `RandomSAT_Variance`, `RapidForcing_ArithmeticAutomation`, `RapidForcing_BoundsPrograms`, `RapidForcing_ComputableAutomation`, `RapidForcing_ComputableProfiles`, `RapidForcing_ExprCoding`, `RapidForcing_IntegerPrimrec`, `RapidForcing_RatComputable`, `RapidForcing_RatOperations`, `RapidForcing_RatPrimrec`, `RapidForcing_RationalProfiles`, `RapidForcing_RecursiveComputable`, `RapidForcing_SyntaxComputable`, `SATComputability_ActiveClauses`, `SATComputability_ArithmeticConstructors`, `SATComputability_ArithmeticEnclosures`, `SATComputability_ArithmeticSyntax`, `SATComputability_CavityExpressions`, `SATComputability_ClauseClasses`, `SATComputability_EffectiveLog`, `SATComputability_HierarchyTable`, `SATComputability_IncidentObstruction`, `SATComputability_PhysicalExpressions`, `SATComputability_RelaxedCandidates`, `SATComputability_WeightedExpressions`.
--
--   **Imports.** It imports the published bundles `Def_DilutedSpin`, `Def_OAIQ041D000` and `Def_SATComputability`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ067A002`, `OAIQ067A003` and `OAIQ067A004`; the statements `OAI_DilutedSpinGlass_ConcreteReservoir_physical_coefficients_tendsto`, `OAI_DilutedSpinGlass_ConcreteReservoir_scoreError_tendsto`, `OAI_DilutedSpinGlass_HeterogeneousMarks_dictionary_coefficients_tendsto`, `OAI_DilutedSpinGlass_PhysicalRoot_normalizedParameterError_tendsto`, `OAI_DilutedSpinGlass_UniversalDictionary_FullShapeControl_scheduled`, `OAI_DilutedSpinGlass_UniversalDictionary_physical_grid_scheduled_step`, `OAI_FixedClauseThreshold_Computability_PositiveInterpolation_PrescribedTree_datumRoot_conditional_replacement_firstMoment`, `OAI_FixedClauseThreshold_Computability_PositiveInterpolation_PrescribedTree_finiteTrial_upper_fixedField`, `OAI_FixedClauseThreshold_Computability_PositiveInterpolation_PrescribedTree_integral_mixedLog_combination_nonpos`, `OAI_FixedClauseThreshold_Computability_PositiveInterpolation_PrescribedTree_upperPoisson_cavity_separable`, `OAI_FixedClauseThreshold_Computability_exists_lowerProgram`, `OAI_FixedClauseThreshold_Computability_threshold_program`, `OAI.FixedClauseThreshold.properSATProbability_center_lower_sat` and `OAI.FixedClauseThreshold.properSATProbability_center_upper_sat`; the proofs of `OAI_DilutedSpinGlass_ConcreteReservoir_uniform_increment`, `OAI.DilutedSpinGlass.ConcreteReservoir.uniform_increment_sat`, `OAI_DilutedSpinGlass_HeterogeneousMarks_averagedEnergyRoot_old_new_compare`, `OAI.DilutedSpinGlass.HeterogeneousMarks.averagedEnergyRoot_old_new_compare_sat`, `OAI_DilutedSpinGlass_HeterogeneousMarks_full_selected_root_concentration`, `OAI.DilutedSpinGlass.HeterogeneousMarks.full_selected_root_concentration_sat`, `OAI_DilutedSpinGlass_HeterogeneousMarks_independentInsertion_tail`, `OAI.DilutedSpinGlass.HeterogeneousMarks.independentInsertion_tail_sat`, `OAI_DilutedSpinGlass_HeterogeneousMarks_parameter_dictionary_palm`, `OAI.DilutedSpinGlass.HeterogeneousMarks.parameter_dictionary_palm_sat`, `OAI_DilutedSpinGlass_HeterogeneousMarks_sameInsertionAverage_tail`, `OAI.DilutedSpinGlass.HeterogeneousMarks.sameInsertionAverage_tail_sat`, `OAI_DilutedSpinGlass_HeterogeneousMarks_variance_actual_root`, `OAI.DilutedSpinGlass.HeterogeneousMarks.variance_actual_root_sat`, `OAI_DilutedSpinGlass_PrescribedTree_marker_history_joint`, `OAI.DilutedSpinGlass.PrescribedTree.marker_history_joint_sat`, `OAI_DilutedSpinGlass_PrescribedTree_matrixHistory_first_pair`, `OAI.DilutedSpinGlass.PrescribedTree.matrixHistory_first_pair_sat`, `OAI_DilutedSpinGlass_PrescribedTree_matrix_three_copy_pointwise`, `OAI.DilutedSpinGlass.PrescribedTree.matrix_three_copy_pointwise_sat`, `OAI_DilutedSpinGlass_PrescribedTree_root_matrix_three_copy`, `OAI.DilutedSpinGlass.PrescribedTree.root_matrix_three_copy_sat`, `OAI_DilutedSpinGlass_ReducedTopology_root_averaged_projectionShiftError_le`, `OAI.DilutedSpinGlass.ReducedTopology.root_averaged_projectionShiftError_le_sat`, `OAI_DilutedSpinGlass_ReducedTopology_scheduledMarkerDefect_covariance`, `OAI.DilutedSpinGlass.ReducedTopology.scheduledMarkerDefect_covariance_sat`, `OAI_DilutedSpinGlass_ReducedTopology_scheduled_root_multileaf`, `OAI.DilutedSpinGlass.ReducedTopology.scheduled_root_multileaf_sat`, `OAI_DilutedSpinGlass_SizeCoupling_perturbedMean_cavity_split`, `OAI.DilutedSpinGlass.SizeCoupling.perturbedMean_cavity_split_sat`, `OAI_DilutedSpinGlass_UniversalDictionary_FullShapeControl_singleton_regular`, `OAI.DilutedSpinGlass.UniversalDictionary.FullShapeControl.singleton_regular_sat`, `OAI_DilutedSpinGlass_UniversalDictionary_clippedSiteInsertion_rate_bound`, `OAI.DilutedSpinGlass.UniversalDictionary.clippedSiteInsertion_rate_bound_sat`, `OAI_DilutedSpinGlass_UniversalDictionary_integrable_rootHistory`, `OAI.DilutedSpinGlass.UniversalDictionary.integrable_rootHistory_sat`, `OAI_DilutedSpinGlass_UniversalDictionary_regular_node_pointwise`, `OAI.DilutedSpinGlass.UniversalDictionary.regular_node_pointwise_sat`, `OAI_DilutedSpinGlass_UniversalDictionary_reservoirShapeError_tendsto`, `OAI.DilutedSpinGlass.UniversalDictionary.reservoirShapeError_tendsto_sat`, `OAI_DilutedSpinGlass_UniversalDictionary_rootHistory_polarization`, `OAI.DilutedSpinGlass.UniversalDictionary.rootHistory_polarization_sat`, `OAI_DilutedSpinGlass_symmetric_trial_lower`, `OAI.DilutedSpinGlass.symmetric_trial_lower_sat`, `OAI_FixedClauseThreshold_Computability_PositiveInterpolation_PrescribedTree_datumRoot_conditional_replacement_firstMoment`, `OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.datumRoot_conditional_replacement_firstMoment_sat`, `OAI_FixedClauseThreshold_Computability_PositiveInterpolation_PrescribedTree_finiteTrial_upper_fixedField`, `OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.finiteTrial_upper_fixedField_sat`, `OAI_FixedClauseThreshold_Computability_PositiveInterpolation_PrescribedTree_integral_mixedLog_combination_nonpos`, `OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.integral_mixedLog_combination_nonpos_sat`, `OAI_FixedClauseThreshold_Computability_PositiveInterpolation_PrescribedTree_upperPoisson_cavity_separable`, `OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperPoisson_cavity_separable_sat`, `OAI_FixedClauseThreshold_Computability_auxiliaryPoissonProbability_supercritical`, `OAI_FixedClauseThreshold_limitingCenter_bounds`, `OAI_FixedClauseThreshold_properSATProbability_center_lower`, `OAI_FixedClauseThreshold_properSATProbability_center_upper` and `OAI_FixedClauseThreshold_subcritical_limit`.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000
import Definitions.Def_SATComputability

section
-- module Solutions.OAIQ067_SAT.Compat
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FiniteLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)

theorem expect_congr {f g : Ω → ℝ} (h : ∀ x, f x = g x) : P.expect f = P.expect g := by
  exact congrArg P.expect (funext h)

theorem expect_mono {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) : P.expect f ≤ P.expect g := by
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (P.nonneg x))

variable {n : ℕ}

theorem abs_expect_le {f : Ω → ℝ} {B : ℝ} (hf : ∀ x, |f x| ≤ B) :
    |P.expect f| ≤ B := by
  apply abs_le.mpr
  constructor
  · have h := P.expect_mono (fun x => (abs_le.mp (hf x)).1)
    simpa only [expect_const] using h
  · have h := P.expect_mono (fun x => (abs_le.mp (hf x)).2)
    simpa only [expect_const] using h

end FiniteLaw
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FiniteProducts
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators

/-- Split off the new first child at a root attachment. -/
theorem expect_pi_cons {n : ℕ} {α : Fin (n+1) → Type*} [∀ i, Fintype (α i)]
    (Q : (i : Fin (n+1)) → FiniteLaw (α i)) (H : ((i : Fin (n+1)) → α i) → ℝ) :
    (pi Q).expect H = (Q 0).expect (fun a =>
      (pi (fun j : Fin n => Q j.succ)).expect (fun rest => H (Fin.cons a rest))) := by
  classical
  simp only [expect, pi]
  rw [← (Fin.consEquiv α).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rest _
  rw [Fin.prod_univ_succ]
  simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
  ring_nf
  rfl

end DilutedSpinGlass.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PhysicalIndex
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology
namespace DilutedSpinGlass

theorem abs_spin (s : Spin) : |spin s| = 1 := by cases s <;> norm_num [spin]

theorem sum_exp_pos {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    0 < ∑ i, Real.exp (f i) :=
  Finset.sum_pos' (fun _ _ => (Real.exp_pos _).le)
    ⟨Classical.arbitrary ι, Finset.mem_univ _, Real.exp_pos _⟩


end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavityBounds
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory Filter Set TopologicalSpace
open scoped Topology NNReal ENNReal BigOperators

namespace DilutedSpinGlass

/-- Product message probabilities have total mass exactly one. -/
theorem product_q_sum {p : ℕ} (x : Fin p → ℝ) :
    (∑ s : Fin p → Spin, ∏ l, q (x l) (s l)) = 1 := by
  rw [← Fintype.prod_sum]
  simp only [q_sum, Finset.prod_const_one]


/-- Uniform bounds on a finite probability-weighted exponential sum. -/
theorem weighted_exp_bounds {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) {B : ℝ}
    (hf : ∀ i, |f i| ≤ B) :
    Real.exp (-B) ≤ ∑ i, w i * Real.exp (f i) ∧
      (∑ i, w i * Real.exp (f i)) ≤ Real.exp B := by
  have hlo : ∀ i, Real.exp (-B) ≤ Real.exp (f i) :=
    fun i => Real.exp_le_exp.mpr (abs_le.mp (hf i)).1
  have hhi : ∀ i, Real.exp (f i) ≤ Real.exp B :=
    fun i => Real.exp_le_exp.mpr (abs_le.mp (hf i)).2
  constructor
  · calc
      Real.exp (-B) = ∑ i, w i * Real.exp (-B) := by rw [← Finset.sum_mul, hs, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hlo i) (hw i))
  · calc
      _ ≤ ∑ i, w i * Real.exp B :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hhi i) (hw i))
      _ = Real.exp B := by rw [← Finset.sum_mul, hs, one_mul]

theorem weighted_log_exp_bound {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) {B : ℝ}
    (hf : ∀ i, |f i| ≤ B) :
    |Real.log (∑ i, w i * Real.exp (f i))| ≤ B := by
  obtain ⟨hlo, hhi⟩ := weighted_exp_bounds w f hw hs hf
  have hp := (Real.exp_pos _).trans_le hlo
  exact abs_le.mpr ⟨(Real.le_log_iff_exp_le hp).mpr hlo,
    (Real.log_le_iff_le_exp hp).mpr hhi⟩

/-- The uniform cavity-message bound; no message moments occur. -/
theorem message_bound {p : ℕ} (theta : Interaction p)
    (x : Fin (p - 1) → ℝ) (ε : Spin) : |message theta x ε| ≤ ‖theta‖ := by
  simpa only [message, mul_comm] using
    weighted_log_exp_bound (B := ‖theta‖) (fun s : Fin (p-1) → Spin => ∏ l, q (x l) (s l))
      (fun s => theta (appendSpin s ε))
      (fun _ => (Finset.prod_pos (fun l _ => q_pos _ _)).le)
      (product_q_sum x) (fun s => norm_le_pi_norm theta (appendSpin s ε))

 
theorem siteLog_bound {p k : ℕ} (theta : Fin k → InteractionSample p)
    (h : ℝ) (x : (Fin k × Fin (p-1)) → ℝ) :
    |siteLog theta h x| ≤ |h| + ∑ j, ‖(theta j).1‖ := by
  have hf : ∀ ε : Spin,
      |h * spin ε + ∑ j, message (theta j).1 (fun l => x (j,l)) ε| ≤
        |h| + ∑ j, ‖(theta j).1‖ := by
    intro ε
    apply (abs_add_le _ _).trans
    apply add_le_add
    · simp only [abs_mul, abs_spin, mul_one, le_refl]
    · exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun j _ => message_bound _ _ _))
  have hw : (∑ _ε : Spin, (1/2 : ℝ)) = 1 := by norm_num [Fintype.sum_bool]
  have hb := weighted_log_exp_bound (fun _ε : Spin => (1/2 : ℝ))
    (fun ε => h * spin ε + ∑ j, message (theta j).1 (fun l => x (j,l)) ε)
    (fun _ => by norm_num) hw hf
  simpa only [siteLog, ← Finset.mul_sum, one_div, div_eq_mul_inv, one_mul, mul_comm] using hb

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MeasureHierarchy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory Filter Set TopologicalSpace
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

namespace DilutedSpinGlass.MeasureMean

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem bounded_integrable {f : Ω → ℝ} {B : ℝ} (hf : Measurable f)
    (hb : ∀ x, |f x| ≤ B) : Integrable f μ :=
  (integrable_const B).mono' hf.aestronglyMeasurable
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb x))

theorem exp_integrable {f : Ω → ℝ} {B : ℝ} (hf : Measurable f)
    (hb : ∀ x, |f x| ≤ B) (m : ℝ) : Integrable (fun x => Real.exp (m*f x)) μ := by
  apply bounded_integrable μ (hf.const_mul m).exp
  intro x
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc m*f x ≤ |m*f x| := le_abs_self _
       _ = |m| * |f x| := abs_mul _ _
       _ ≤ |m| * B := mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)

theorem exp_integral_pos {f : Ω → ℝ} {B : ℝ} (hf : Measurable f)
    (hb : ∀ x, |f x| ≤ B) (m : ℝ) : 0 < ∫ x, Real.exp (m*f x) ∂μ :=
  integral_exp_pos (exp_integrable μ hf hb m)

theorem logMean_const {m : ℝ} (hm : m ≠ 0) (a : ℝ) :
    logMean μ m (fun _ => a) = a := by
  simp [logMean, Real.log_exp, hm]

theorem logMean_mono {m : ℝ} (hm : 0 < m) {f g : Ω → ℝ} {B C : ℝ}
    (hf : Measurable f) (hg : Measurable g) (hfb : ∀ x, |f x| ≤ B)
    (hgb : ∀ x, |g x| ≤ C) (hfg : ∀ x, f x ≤ g x) :
    logMean μ m f ≤ logMean μ m g := by
  apply div_le_div_of_nonneg_right _ hm.le
  apply Real.log_le_log (exp_integral_pos μ hf hfb m)
  exact integral_mono (exp_integrable μ hf hfb m) (exp_integrable μ hg hgb m)
    (fun x => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hfg x) hm.le))

theorem logMean_add_const {m : ℝ} (hm : m ≠ 0) {f : Ω → ℝ} {B : ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) (a : ℝ) :
    logMean μ m (fun x => f x+a) = logMean μ m f+a := by
  unfold logMean
  simp_rw [mul_add, Real.exp_add]
  rw [integral_mul_const, Real.log_mul (ne_of_gt (exp_integral_pos μ hf hb m))
    (Real.exp_ne_zero _), Real.log_exp]
  field_simp

theorem logMean_stability {m : ℝ} (hm : 0 < m) {f g : Ω → ℝ} {B C D : ℝ}
    (hf : Measurable f) (hg : Measurable g) (hfb : ∀ x, |f x| ≤ B)
    (hgb : ∀ x, |g x| ≤ C) (hfg : ∀ x, |f x-g x| ≤ D) :
    |logMean μ m f-logMean μ m g| ≤ D := by
  have haddb (g : Ω → ℝ) (C : ℝ) (hg : ∀ x, |g x| ≤ C) (x : Ω) :
      |g x+D| ≤ C+|D| := (abs_add_le _ _).trans (add_le_add (hg x) le_rfl)
  have h1 := logMean_mono μ hm hf (hg.add_const D) hfb (haddb g C hgb)
    (fun x => by have := (abs_le.mp (hfg x)).2; linarith)
  have h2 := logMean_mono μ hm hg (hf.add_const D) hgb (haddb f B hfb)
    (fun x => by have := (abs_le.mp (hfg x)).1; linarith)
  rw [logMean_add_const μ hm.ne' hg hgb] at h1
  rw [logMean_add_const μ hm.ne' hf hfb] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem logMean_bound {m : ℝ} (hm : 0 < m) {f : Ω → ℝ} {B : ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ B) : |logMean μ m f| ≤ B := by
  have h := logMean_stability μ hm hf measurable_const hb
    (fun _ => (by simp : |(0 : ℝ)| ≤ 0)) (by simpa using hb)
  simpa only [logMean_const μ hm.ne', sub_zero] using h

end DilutedSpinGlass.MeasureMean

namespace DilutedSpinGlass
attribute [local instance] OAI.DilutedSpinGlass.measureHierarchyContinuousMeasurableSpace
local instance measureHierarchyContinuousBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

theorem logMean_continuous_bound {ι : Type} [Fintype ι] (r : ℕ)
    (g : (ι → ℝ) → ℝ) (hg : Continuous g) {B : ℝ} (hB : ∀ x, |g x| ≤ B)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) :
    Continuous (logMean r g m) ∧ ∀ eta, |logMean r g m eta| ≤ B := by
  induction r with
  | zero => exact ⟨hg, hB⟩
  | succ r ih =>
    obtain ⟨hc, hb⟩ := ih (fun i => m i.succ) (fun i => hm i.succ)
    let f := logMean r g (fun i => m i.succ)
    let F : (ι → Hierarchy r) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x => Real.exp (m 0 * f x)) (Real.continuous_exp.comp (hc.const_mul (m 0)))
      (Real.exp (|m 0| * B)) (fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        exact (le_abs_self _).trans (by rw [abs_mul]; gcongr; exact hb x))
    have hpos (eta : ι → Hierarchy (r+1)) : 0 < ∫ x, F x ∂(ProbabilityMeasure.pi eta) :=
      MeasureMean.exp_integral_pos (ProbabilityMeasure.pi eta).toMeasure hc.measurable hb (m 0)
    have hcont : Continuous (fun eta : ι → Hierarchy (r+1) => ∫ x, F x ∂(ProbabilityMeasure.pi eta)) :=
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction F).comp
        ProbabilityMeasure.continuous_pi
    refine ⟨(hcont.log (fun eta => (hpos eta).ne')).div_const (m 0), ?_⟩
    intro eta
    exact MeasureMean.logMean_bound (ProbabilityMeasure.pi eta).toMeasure (hm 0) hc.measurable hb

 theorem trialLog_continuous_bound {ι : Type} [Fintype ι] (r : ℕ)
    (g : (ι → ℝ) → ℝ) (hg : Continuous g) {B : ℝ} (hB : ∀ x, |g x| ≤ B)
    (m : Fin r → ℝ) (hm : ∀ i, 0 < m i) :
    Continuous (fun ζ => trialLog r ζ m g) ∧ ∀ ζ, |trialLog r ζ m g| ≤ B := by
  obtain ⟨hc,hb⟩ := logMean_continuous_bound r g hg hB m hm
  let F : (ι → Hierarchy r) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (logMean r g m) hc B (fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have hpi : Continuous (fun ζ : Hierarchy (r+1) => ProbabilityMeasure.pi (fun _ : ι => ζ)) :=
    ProbabilityMeasure.continuous_pi.comp (continuous_pi (fun _ => continuous_id))
  refine ⟨(ProbabilityMeasure.continuous_integral_boundedContinuousFunction F).comp hpi, ?_⟩
  intro ζ
  change |∫ x, F x ∂(ProbabilityMeasure.pi (fun _ : ι => ζ)).toMeasure| ≤ B
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := (ProbabilityMeasure.pi (fun _ : ι => ζ)).toMeasure)
      (ae_of_all _ (fun x => (show ‖F x‖ ≤ B from by simpa [F] using hb x))))

end DilutedSpinGlass

namespace DilutedSpinGlass

 theorem continuous_q (s : Spin) : Continuous (fun x => q x s) := by
  unfold q
  apply (Real.continuous_exp.comp (continuous_id.mul continuous_const)).div
    (continuous_const.mul Real.continuous_cosh)
  intro x
  exact mul_ne_zero (by norm_num) (Real.cosh_pos x).ne'

 theorem continuous_message {p : ℕ} (theta : Interaction p) (ε : Spin) :
    Continuous (fun x => message theta x ε) := by
  unfold message
  apply Continuous.log
  · apply continuous_finsetSum
    intro s _
    apply continuous_const.mul
    exact continuous_finsetProd _ (fun l _ => (continuous_q (s l)).comp (continuous_apply l))
  · intro x
    apply ne_of_gt
    apply Finset.sum_pos
    · intro s _
      exact mul_pos (Real.exp_pos _) (Finset.prod_pos (fun l _ => q_pos _ _))
    · exact Finset.univ_nonempty

 theorem continuous_siteLog {p k : ℕ} (theta : Fin k → InteractionSample p) (h : ℝ) :
    Continuous (siteLog theta h) := by
  unfold siteLog
  apply Continuous.log
  · apply Continuous.div_const
    apply continuous_finsetSum
    intro ε _
    apply Real.continuous_exp.comp
    apply continuous_const.add
    apply continuous_finsetSum
    intro j _
    exact (continuous_message (theta j).1 ε).comp
      (continuous_pi (fun l => continuous_apply (j,l)))
  · intro x
    apply ne_of_gt
    exact div_pos (sum_exp_pos _) (by norm_num)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FiniteEncoding
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Set
open scoped NNReal BigOperators

namespace FiniteLaw
variable {Ω : Type} [Fintype Ω]

noncomputable local instance finiteEncodingDecidableEq_rb1a102_1 (type : Type) :
    DecidableEq type := Classical.decEq type
lemma integral_asProbability {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : FiniteLaw Ω) (f : Ω → X) (g : X → ℝ) :
    ∫ x, g x ∂(P.asProbability f)=P.expect (fun a => g (f a)) := by
  rw [asProbability,integral_atomicProbability]
  rfl

end FiniteLaw

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory
open scoped BigOperators

lemma piCongrLeft_const_apply {ι κ X : Type} [MeasurableSpace X]
    (e : ι ≃ κ) (x : κ → X) :
    (MeasurableEquiv.piCongrLeft (fun _ : ι => X) e.symm) x = fun i => x (e i) := by
  funext i
  change (Equiv.piCongrLeft (fun _ : ι => X) e.symm) x i = _
  rw [Equiv.piCongrLeft_apply]
  simp

attribute [local instance] OAI.DilutedSpinGlass.finiteEncodingReindexMeasurableSpace
local instance finiteEncodingReindexBorelSpace_rb1a102_1 (space : TopCat) : BorelSpace space := ⟨rfl⟩
lemma logMean_reindex {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (r : ℕ) (g : (ι → ℝ) → ℝ) (m : Fin r → ℝ) (eta : ι → Hierarchy r) :
    logMean r (fun x : κ → ℝ => g (fun i => x (e i))) m (fun j => eta (e.symm j)) =
      logMean r g m eta := by
  induction r with
  | zero => simp [logMean]
  | succ r ih =>
    change ι → ProbabilityMeasure (Hierarchy r) at eta
    simp only [logMean]
    congr 2
    have he := (measurePreserving_piCongrLeft
      (fun i : ι => (eta i).toMeasure) e.symm).integral_comp'
        (fun x : ι → Hierarchy r => Real.exp (m 0*logMean r g (fun i => m i.succ) x))
    rw [← he]
    apply integral_congr_ae
    filter_upwards [] with x
    congr 2
    simpa only [Equiv.apply_symm_apply,piCongrLeft_const_apply] using ih (fun i => m i.succ) (fun i => x (e i))

lemma trialLog_reindex {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (r : ℕ) (g : (ι → ℝ) → ℝ) (m : Fin r → ℝ) (ζ : Hierarchy (r+1)) :
    trialLog r ζ m (fun x : κ → ℝ => g (fun i => x (e i))) = trialLog r ζ m g := by
  change ProbabilityMeasure (Hierarchy r) at ζ
  unfold trialLog
  have he := (measurePreserving_piCongrLeft
    (fun _ : ι => ζ.toMeasure) e.symm).integral_comp' (logMean r g m)
  rw [← he]
  apply integral_congr_ae
  filter_upwards [] with x
  simpa only [Equiv.apply_symm_apply,piCongrLeft_const_apply] using logMean_reindex e r g m (fun i => x (e i))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_QSubtreePotential
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace FiniteLaw
variable {Ω : Type} [Fintype Ω]

lemma asProbability_id_singleton [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (P : FiniteLaw Ω) (a : Ω) : (P.asProbability id).toMeasure {a} = ENNReal.ofReal (P.weight a) := by
  classical
  simp [asProbability, atomicProbability, nnWeights, Measure.finsetSum_apply,
    Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton a), Pi.single_apply]
  exact ENNReal.ofReal_coe_nnreal.symm

lemma asProbability_eq_map [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    {X : Type*} [MeasurableSpace X] (P : FiniteLaw Ω) (f : Ω → X) :
    (P.asProbability f).toMeasure = Measure.map f (P.asProbability id).toMeasure := by
  classical
  have hf : Measurable f := measurable_of_countable f
  simp only [asProbability, atomicProbability]
  change (∑ a, ((P.nnWeights).val a : ℝ≥0∞) • Measure.dirac (f a)) =
    Measure.map f (∑ a, ((P.nnWeights).val a : ℝ≥0∞) • Measure.dirac a)
  rw [Measure.map_finset_sum hf.aemeasurable]
  simp only [Measure.map_smul, Measure.map_dirac' hf]

lemma asProbability_pi {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : ι → Type} [∀ i, Fintype (α i)] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (Q : (i : ι) → FiniteLaw (α i)) (f : (i : ι) → α i → X i) :
    ((pi Q).asProbability (fun x i => f i (x i))).toMeasure =
      Measure.pi (fun i => ((Q i).asProbability (f i)).toMeasure) := by
  classical
  let (index : ι) : MeasurableSpace (α index) := ⊤
  let (index : ι) : MeasurableSingletonClass (α index) := ⟨fun _ => trivial⟩
  have he : ((pi Q).asProbability id).toMeasure =
      Measure.pi (fun i => ((Q i).asProbability id).toMeasure) := by
    apply Measure.ext_of_singleton
    intro x
    simp only [asProbability_id_singleton, Measure.pi_singleton]
    change ENNReal.ofReal (∏ i, (Q i).weight (x i)) = _
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => (Q i).nonneg _)]
  rw [asProbability_eq_map, he, Measure.pi_map_pi (fun i =>
    (measurable_of_countable (f i)).aemeasurable)]
  simp_rw [← asProbability_eq_map]

lemma integral_pi_asProbability {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : ι → Type} [∀ i, Fintype (α i)] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (Q : (i : ι) → FiniteLaw (α i)) (f : (i : ι) → α i → X i)
    (g : ((i : ι) → X i) → ℝ) :
    (∫ x, g x ∂Measure.pi (fun i => ((Q i).asProbability (f i)).toMeasure)) =
      (pi Q).expect (fun a => g (fun i => f i (a i))) := by
  rw [← asProbability_pi, integral_asProbability]

end FiniteLaw
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_TrialPhysical
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Filter
open scoped Topology BigOperators NNReal

lemma trial_site_bound {p k : ℕ} (r : ℕ) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)
    (ζ : Hierarchy (r+1)) (θ : Fin k → InteractionSample p) (h : ℝ) :
    |trialLog r ζ m (siteLog θ h)|≤|h|+∑ j,‖(θ j).1‖ :=
  (trialLog_continuous_bound r _ (continuous_siteLog θ h) (siteLog_bound θ h) m hm).2 ζ

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.PeriodicLattice_Arithmetic
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recursive arithmetic and effective profile syntax. -/

namespace PeriodicLattice

noncomputable section

namespace RecursiveArithmetic
open Encodable Primrec

theorem factorial : Primrec Nat.factorial := by
  have h := Primrec.nat_rec₁ (1 : ℕ)
    ((Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst) Primrec.snd).to₂)
  exact h.of_eq (fun n => by induction n <;> simp [Nat.factorial, *])

local instance finiteFunctionEncodingArithmetic_rb1a102_1 {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow
@[simp] theorem encode_int_ofNat (n : ℕ) : encode (n : ℤ) = 2 * n := rfl
@[simp] theorem encode_int_negSucc (n : ℕ) : encode (Int.negSucc n) = 2 * n + 1 := rfl

theorem intOfNat : Primrec (fun n : ℕ => (n : ℤ)) :=
  Primrec.encode_iff.mp (Primrec.nat_double.of_eq (fun _ => rfl))

theorem intNegSucc : Primrec Int.negSucc :=
  Primrec.encode_iff.mp (Primrec.nat_double_succ.of_eq (fun _ => rfl))

theorem intNatAbs : Primrec Int.natAbs := by
  have h := Primrec.cond (Primrec.nat_bodd.comp (Primrec.encode : Primrec (encode : ℤ → ℕ)))
    (Primrec.succ.comp (Primrec.nat_div2.comp Primrec.encode))
    (Primrec.nat_div2.comp Primrec.encode)
  exact h.of_eq (fun z => by cases z <;> simp [Nat.bodd, Nat.div2_val, encode_int_ofNat, encode_int_negSucc, show (2 : ℕ) ≠ 0 from by decide])

theorem intNegative : PrimrecPred (fun z : ℤ => z < 0) := by
  refine ⟨inferInstance, ?_⟩
  exact (Primrec.nat_bodd.comp Primrec.encode).of_eq (fun z => by
    cases z <;> simp [Nat.bodd, encode_int_ofNat, encode_int_negSucc])

theorem intNeg : Primrec (fun z : ℤ => -z) := by
  have hc : Primrec (fun z : ℤ => if z < 0 then (z.natAbs : ℤ)
      else if z.natAbs = 0 then 0 else Int.negSucc (z.natAbs - 1)) :=
    Primrec.ite intNegative (intOfNat.comp intNatAbs)
      (Primrec.ite (Primrec.eq.comp intNatAbs (Primrec.const 0)) (Primrec.const 0)
        (intNegSucc.comp (Primrec.nat_sub.comp intNatAbs (Primrec.const 1))))
  exact hc.of_eq (fun z => by cases z <;> simp; split_ifs <;> omega)

theorem intSubNat : Primrec₂ (fun a b : ℕ => (a : ℤ) - b) := by
  have hc : Primrec (fun p : ℕ × ℕ => if p.2 ≤ p.1 then ((p.1 - p.2 : ℕ) : ℤ)
      else Int.negSucc (p.2 - p.1 - 1)) :=
    Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst)
      (intOfNat.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
      (intNegSucc.comp (Primrec.nat_sub.comp (Primrec.nat_sub.comp Primrec.snd Primrec.fst) (Primrec.const 1)))
  exact hc.of_eq (fun p => by dsimp only; split_ifs <;> omega)

theorem intAdd : Primrec₂ (fun a b : ℤ => a + b) := by
  have ap := Primrec.fst (α := ℤ) (β := ℤ)
  have bp := Primrec.snd (α := ℤ) (β := ℤ)
  have aa := intNatAbs.comp ap
  have ab := intNatAbs.comp bp
  have hp := intOfNat.comp (Primrec.nat_add.comp aa ab)
  have hc := Primrec.ite (intNegative.comp ap)
    (Primrec.ite (intNegative.comp bp) (intNeg.comp hp) (intSubNat.comp ab aa))
    (Primrec.ite (intNegative.comp bp) (intSubNat.comp aa ab) hp)
  exact hc.of_eq (fun p => by
    rcases p with ⟨a,b⟩
    cases a <;> cases b <;>
      simp only [Int.natAbs_natCast, Int.natAbs_negSucc, Int.ofNat_eq_natCast,
      Int.negSucc_lt_zero, not_lt_of_ge (Int.natCast_nonneg _), ↓reduceIte]
    all_goals simp [Int.negSucc_eq] <;> omega)

theorem intSub : Primrec₂ (fun a b : ℤ => a - b) :=
  (intAdd.comp Primrec.fst (intNeg.comp Primrec.snd)).of_eq (fun _ => by simp [sub_eq_add_neg])

theorem intMul : Primrec₂ (fun a b : ℤ => a * b) := by
  have ap := Primrec.fst (α := ℤ) (β := ℤ)
  have bp := Primrec.snd (α := ℤ) (β := ℤ)
  have hp := intOfNat.comp (Primrec.nat_mul.comp (intNatAbs.comp ap) (intNatAbs.comp bp))
  have hc := Primrec.ite (intNegative.comp ap)
    (Primrec.ite (intNegative.comp bp) hp (intNeg.comp hp))
    (Primrec.ite (intNegative.comp bp) (intNeg.comp hp) hp)
  exact hc.of_eq (fun p => by
    rcases p with ⟨a,b⟩
    cases a <;> cases b <;>
      simp only [Int.natAbs_natCast, Int.natAbs_negSucc, Int.ofNat_eq_natCast,
      Int.negSucc_lt_zero, not_lt_of_ge (Int.natCast_nonneg _), ↓reduceIte]
    all_goals simp [Int.negSucc_eq] <;> ring)

theorem intLE : PrimrecRel (fun a b : ℤ => a ≤ b) := by
  exact (intNegative.comp (intSub.comp Primrec.snd Primrec.fst)).not.of_eq (fun p => by dsimp only; omega)

end RecursiveArithmetic

attribute [fun_prop] Primrec
attribute [fun_prop] Primrec.id Primrec.const Primrec.comp Primrec.pair Primrec.fst Primrec.snd
attribute [fun_prop] RecursiveArithmetic.intOfNat RecursiveArithmetic.intNatAbs
attribute [fun_prop] RecursiveArithmetic.intNeg RecursiveArithmetic.factorial
namespace RecursiveArithmetic
@[fun_prop] theorem int_add : Primrec (fun p : ℤ × ℤ => p.1 + p.2) := intAdd
@[fun_prop] theorem int_mul : Primrec (fun p : ℤ × ℤ => p.1 * p.2) := intMul
@[fun_prop] theorem nat_add : Primrec (fun p : ℕ × ℕ => p.1 + p.2) := Primrec.nat_add
@[fun_prop] theorem nat_sub : Primrec (fun p : ℕ × ℕ => p.1 - p.2) := Primrec.nat_sub
@[fun_prop] theorem nat_mul : Primrec (fun p : ℕ × ℕ => p.1 * p.2) := Primrec.nat_mul
@[fun_prop] theorem nat_div : Primrec (fun p : ℕ × ℕ => p.1 / p.2) := Primrec.nat_div

end RecursiveArithmetic

end
end PeriodicLattice

end OAI
end

section
-- module Solutions.OAIQ067_SAT.PeriodicLattice_RationalArithmetic
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform lattice constants and computable reduced rational arithmetic. -/

namespace PeriodicLattice

noncomputable section

namespace RecursiveArithmetic
open Encodable Primrec

theorem natDvd : PrimrecRel (fun a b : ℕ => a ∣ b) :=
  (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd Primrec.fst) (Primrec.const 0)).of_eq
    (fun _ => Nat.dvd_iff_mod_eq_zero.symm)

def gcdSearch (a b : ℕ) : ℕ :=
  Nat.findGreatest (fun k => k ∣ a ∧ k ∣ b) (a+b)

theorem gcdSearch_eq (a b : ℕ) : gcdSearch a b = Nat.gcd a b := by
  unfold gcdSearch
  by_cases hab : a + b = 0
  · have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    simp [ha, hb]
  have hpos : 0 < Nat.gcd a b := Nat.gcd_pos_iff.mpr (by omega)
  have hle : Nat.gcd a b ≤ a + b := Nat.le_of_dvd (by omega)
    (dvd_add (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b))
  have hs : (Nat.findGreatest (fun k => k ∣ a ∧ k ∣ b) (a+b)) ∣ a ∧
      (Nat.findGreatest (fun k => k ∣ a ∧ k ∣ b) (a+b)) ∣ b :=
    Nat.findGreatest_spec (P := fun k => k ∣ a ∧ k ∣ b) hle ⟨Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _⟩
  apply le_antisymm
  · exact Nat.le_of_dvd hpos (Nat.dvd_gcd
      hs.1
      hs.2)
  · exact Nat.le_findGreatest hle ⟨Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _⟩

@[fun_prop] theorem nat_gcd : Primrec (fun p : ℕ × ℕ => Nat.gcd p.1 p.2) := by
  have h := Primrec.nat_findGreatest (Primrec.nat_add.comp Primrec.fst Primrec.snd)
    ((natDvd.comp (Primrec.snd) (Primrec.fst.comp Primrec.fst)).and
      (natDvd.comp (Primrec.snd) (Primrec.snd.comp Primrec.fst))).primrecRel
  exact h.of_eq (fun p => gcdSearch_eq p.1 p.2)

theorem natCoprime : PrimrecRel Nat.Coprime :=
  (Primrec.eq.comp nat_gcd (Primrec.const 1)).of_eq (fun _ => Iff.rfl)

theorem reducedPred : PrimrecPred (fun p : ℤ × ℕ => 0 < p.2 ∧ p.1.natAbs.Coprime p.2) :=
  (Primrec.nat_lt.comp (Primrec.const 0) Primrec.snd).and
    (natCoprime.comp (intNatAbs.comp Primrec.fst) Primrec.snd)

abbrev ReducedPair := {p : ℤ × ℕ // 0 < p.2 ∧ p.1.natAbs.Coprime p.2}
local instance rationalArithmeticLocal1 : Primcodable ReducedPair := Primcodable.subtype reducedPred

def ratEquiv : ℚ ≃ ReducedPair where
  toFun q := ⟨(q.num, q.den), Nat.pos_of_ne_zero q.den_nz, q.reduced⟩
  invFun p := ⟨p.1.1, p.1.2, Nat.ne_of_gt p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[instance_reducible] def rationalPrimcodable : Primcodable ℚ := Primcodable.ofEquiv _ ratEquiv

theorem encodable_ext {α : Type*} {e f : Encodable α}
    (he : e.encode = f.encode) (hd : e.decode = f.decode) : e = f := by
  cases e
  cases f
  cases he
  cases hd
  rfl

local instance finiteFunctionEncodingRationalArithmetic_rb1a102_1 {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow
theorem rational_encoding : rationalPrimcodable.toEncodable = Rat.instEncodable := by
  refine encodable_ext (e := rationalPrimcodable.toEncodable) (f := Rat.instEncodable) rfl ?_
  funext n
  dsimp +instances only [rationalPrimcodable, rationalArithmeticLocal1, Primcodable.ofEquiv, Primcodable.subtype, Primcodable.prod, Primcodable.ofDenumerable, Denumerable.int, Denumerable.nat, ratEquiv,
    Rat.instEncodable, Encodable.ofEquiv, Encodable.ofLeftInverse, Encodable.ofLeftInjection,
    Encodable.decodeSubtype, Encodable.decodeSigma, Encodable.Prod.encodable,
    Subtype.encodable, Sigma.encodable, Int.encodable, Nat.encodable,
    Option.bind_some, Option.map_some, Equiv.symm_symm, Equiv.sigmaEquivProd, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  simp only [Function.comp_apply, Option.bind_some]
  split_ifs with h
  · cases h with
    | intro hp hc => rfl
  · rfl

local instance ratPrimcodable : Primcodable ℚ :=
  { toEncodable := Rat.instEncodable
    prim := by
      rw [← rational_encoding]
      exact @Primcodable.prim ℚ rationalPrimcodable }

@[simp] theorem ratEncoding (q : ℚ) : encode q = Nat.pair (encode q.num) q.den := rfl

@[fun_prop] theorem ratNum : Primrec Rat.num := by
  exact Primrec.encode_iff.mp (((Primrec.fst.comp Primrec.unpair).comp
    (Primrec.encode : Primrec (encode : ℚ → ℕ))).of_eq (fun q => by simp))

@[fun_prop] theorem ratDen : Primrec Rat.den := by
  exact ((Primrec.snd.comp Primrec.unpair).comp
    (Primrec.encode : Primrec (encode : ℚ → ℕ))).of_eq (fun q => by simp)

@[fun_prop] theorem int_div : Primrec (fun p : ℤ × ℤ => p.1 / p.2) := by
  have hc : Primrec (fun p : ℤ × ℤ =>
      if p.2 = 0 then 0 else if p.1 < 0 then
        if p.2 < 0 then (((p.1.natAbs-1) / p.2.natAbs + 1 : ℕ) : ℤ)
        else Int.negSucc ((p.1.natAbs-1) / p.2.natAbs)
      else if p.2 < 0 then -((p.1.natAbs / p.2.natAbs : ℕ) : ℤ)
        else ((p.1.natAbs / p.2.natAbs : ℕ) : ℤ)) := by
    apply Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const 0)
    apply Primrec.ite (intNegative.comp Primrec.fst)
    · apply Primrec.ite (intNegative.comp Primrec.snd)
      · fun_prop
      · exact intNegSucc.comp (by fun_prop)
    · apply Primrec.ite (intNegative.comp Primrec.snd) <;> fun_prop
  exact hc.of_eq (fun p => by
    rcases p with ⟨a,b⟩
    cases a with
    | ofNat a =>
      cases b with
      | ofNat b =>
        simp only [Int.ofNat_eq_natCast, Int.natAbs_natCast,
          not_lt_of_ge (Int.natCast_nonneg _), ↓reduceIte, Int.natCast_ediv]
        split_ifs with hb <;> simp_all
      | negSucc b =>
        rw [Int.ofNat_ediv_negSucc]
        simp only [Int.ofNat_eq_natCast, Int.negSucc_ne_zero, Int.negSucc_lt_zero,
          not_lt_of_ge (Int.natCast_nonneg _), ↓reduceIte,
          Int.natAbs_natCast, Int.natAbs_negSucc]
    | negSucc a =>
      cases b with
      | ofNat b =>
        cases b with
        | zero => simp
        | succ b => simp only [Int.ofNat_eq_natCast,
          Int.natCast_eq_zero, Nat.succ_ne_zero, Int.negSucc_lt_zero,
          not_lt_of_ge (Int.natCast_nonneg _), ↓reduceIte, Int.natAbs_natCast,
          Int.natAbs_negSucc,
          Int.negSucc_ediv_ofNat_succ, Nat.succ_sub_one]
      | negSucc b => simp [Int.negSucc_ediv_negSucc])

@[fun_prop] theorem ratMk : Primrec (fun p : ℤ × ℕ => mkRat p.1 p.2) := by
  apply Primrec.encode_iff.mp
  have hc : Primrec (fun p : ℤ × ℕ =>
      if p.2 = 0 then encode (0 : ℚ) else
      Nat.pair (encode (p.1 / (Nat.gcd p.2 p.1.natAbs : ℤ)))
        (p.2 / Nat.gcd p.2 p.1.natAbs)) := by
    apply Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const _)
    apply Primrec₂.natPair.comp
    · exact Primrec.encode.comp (by fun_prop)
    · fun_prop
  exact hc.of_eq (fun p => by
    simp only [ratEncoding, Rat.num_mkRat, Rat.den_mkRat]
    split_ifs <;> simp [*])

@[fun_prop] theorem ratInt : Primrec (fun z : ℤ => (z : ℚ)) := by
  apply Primrec.encode_iff.mp
  exact (Primrec₂.natPair.comp Primrec.encode (Primrec.const 1)).of_eq
    (fun z => by simp)

@[fun_prop] theorem ratNat : Primrec (fun n : ℕ => (n : ℚ)) :=
  (ratInt.comp intOfNat).of_eq (fun _ => by simp)

@[fun_prop] theorem rat_add : Primrec (fun p : ℚ × ℚ => p.1 + p.2) := by
  have hc : Primrec (fun p : ℚ × ℚ =>
      mkRat (p.1.num * p.2.den + p.2.num * p.1.den) (p.1.den * p.2.den)) := by
    exact ratMk.comp (show Primrec (fun p : ℚ × ℚ =>
      (p.1.num * p.2.den + p.2.num * p.1.den, p.1.den * p.2.den)) from by fun_prop)
  exact hc.of_eq (fun p => by simp [Rat.add_def, Rat.normalize_eq_mkRat])

@[fun_prop] theorem rat_mul : Primrec (fun p : ℚ × ℚ => p.1 * p.2) := by
  have hc : Primrec (fun p : ℚ × ℚ => mkRat (p.1.num * p.2.num) (p.1.den * p.2.den)) := by
    exact ratMk.comp (show Primrec (fun p : ℚ × ℚ =>
      (p.1.num * p.2.num, p.1.den * p.2.den)) from by fun_prop)
  exact hc.of_eq (fun p => by simp [Rat.mul_def, Rat.normalize_eq_mkRat])

@[fun_prop] theorem ratNeg : Primrec (fun q : ℚ => -q) := by
  have hc : Primrec (fun q : ℚ => mkRat (-q.num) q.den) := by
    exact ratMk.comp (show Primrec (fun q : ℚ => (-q.num, q.den)) from by fun_prop)
  exact hc.of_eq (fun q => by simp [Rat.neg_def, Rat.divInt_ofNat])

@[fun_prop] theorem ratDivInt : Primrec (fun p : ℤ × ℤ => Rat.divInt p.1 p.2) := by
  have hc : Primrec (fun p : ℤ × ℤ =>
      if p.2 < 0 then mkRat (-p.1) p.2.natAbs else mkRat p.1 p.2.natAbs) :=
    Primrec.ite (intNegative.comp Primrec.snd) (by fun_prop) (by fun_prop)
  exact hc.of_eq (fun p => by
    rcases p with ⟨a,b⟩
    cases b <;> simp [Rat.divInt, Rat.normalize_eq_mkRat])

@[fun_prop] theorem ratInv : Primrec (fun q : ℚ => q⁻¹) := by
  exact (ratDivInt.comp (show Primrec (fun q : ℚ => ((q.den : ℤ), q.num)) from by fun_prop)).of_eq (fun q => (Rat.inv_def q).symm)

@[fun_prop] theorem rat_sub : Primrec (fun p : ℚ × ℚ => p.1 - p.2) := by
  simpa only [sub_eq_add_neg] using rat_add.comp (Primrec.fst.pair (ratNeg.comp Primrec.snd))

@[fun_prop] theorem rat_div : Primrec (fun p : ℚ × ℚ => p.1 / p.2) := by
  simpa only [div_eq_mul_inv] using rat_mul.comp (Primrec.fst.pair (ratInv.comp Primrec.snd))

@[fun_prop] theorem rat_pow : Primrec (fun p : ℚ × ℕ => p.1 ^ p.2) := by
  exact (Primrec.nat_iterate Primrec.snd (Primrec.const (1 : ℚ))
    (rat_mul.comp (Primrec.snd.pair (Primrec.fst.comp Primrec.fst))).to₂).of_eq
    (fun p => by dsimp only; induction p.2 <;> simp_all [pow_succ'])

end RecursiveArithmetic

end
end PeriodicLattice

end OAI
end

section
-- module Solutions.OAIQ067_SAT.PeriodicLattice_EffectiveReals
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Well-formed input encodings and effective real enclosures. -/

namespace PeriodicLattice

noncomputable section

namespace RecursiveArithmetic
open Encodable Primrec
local instance effectiveRealsLocal1 : Primcodable ℚ := ratPrimcodable

@[fun_prop] theorem rat_abs : Primrec (abs : ℚ → ℚ) := by
  have hn : PrimrecPred (fun q : ℚ => q < 0) :=
    (intNegative.comp ratNum).of_eq (fun q => Rat.num_neg)
  exact (Primrec.ite hn ratNeg Primrec.id).of_eq (fun q => by split_ifs with h; exact (abs_of_neg h).symm; exact (abs_of_nonneg (not_lt.mp h)).symm)

theorem ratLE : PrimrecRel (fun a b : ℚ => a ≤ b) := by
  exact (intLE.comp (by fun_prop : Primrec (fun p : ℚ × ℚ => p.1.num * p.2.den))
    (by fun_prop : Primrec (fun p : ℚ × ℚ => p.2.num * p.1.den))).of_eq (fun p => (Rat.le_iff p.1 p.2).symm)

theorem ratLT : PrimrecRel (fun a b : ℚ => a < b) :=
  (ratLE.comp Primrec.snd Primrec.fst).not.of_eq (fun _ => not_le)

@[fun_prop] theorem rat_floor : Primrec (fun q : ℚ => ⌊q⌋) :=
  (int_div.comp (ratNum.pair (intOfNat.comp ratDen))).of_eq (fun q => (Rat.floor_def q).symm)

@[fun_prop] theorem listSumRat : Primrec (List.sum : List ℚ → ℚ) := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0)
    (rat_add.comp ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp Primrec.snd))).to₂).of_eq
    (fun l => by dsimp only; induction l <;> simp_all)

@[fun_prop] theorem sumRangeRat {α : Type*} [Primcodable α] {f : α → ℕ} {g : α → ℕ → ℚ}
    (hf : Primrec f) (hg : Primrec₂ g) : Primrec (fun a => ∑ i ∈ Finset.range (f a), g a i) :=
  (listSumRat.comp (Primrec.list_map (Primrec.list_range.comp hf) hg)).of_eq
    (fun a => by simpa only [List.toFinset_range] using (List.sum_toFinset (g a) List.nodup_range).symm)

end RecursiveArithmetic

namespace CertifiedReal
open Encodable Filter Topology
local instance effectiveRealsLocal2 : Primcodable ℚ := RecursiveArithmetic.ratPrimcodable

def error (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
def qerror (n : ℕ) : ℚ := 1 / ((n : ℚ) + 1)

@[simp] theorem cast_qerror (n : ℕ) : (qerror n : ℝ) = error n := by simp [qerror, error]
theorem error_pos (n : ℕ) : 0 < error n := by unfold error; positivity
theorem error_le_one (n : ℕ) : error n ≤ 1 := by unfold error; exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
theorem error_tendsto : Tendsto error atTop (𝓝 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

@[fun_prop] theorem qerror_primrec : Primrec qerror := by unfold qerror; fun_prop

def Effective {A : Type*} [Primcodable A] (f : A → ℝ) : Prop :=
  ∃ q : A × ℕ → ℚ, Computable q ∧ ∀ a n, |f a - (q (a,n) : ℝ)| ≤ error n

section
variable {A B : Type*} [Primcodable A] [Primcodable B]

theorem computable_find {p : A → ℕ → Prop} [DecidableRel p]
    (hp : Computable (fun an : A × ℕ => decide (p an.1 an.2))) (he : ∀ a, ∃ n, p a n) :
    Computable (fun a => Nat.find (he a)) := by
  have hr : Partrec (fun a => Nat.rfind (fun n => Part.some (decide (p a n)))) :=
    Partrec.rfind hp.partrec.to₂
  apply hr.of_eq_tot
  intro a
  apply (Nat.mem_rfind (p := (fun n => Part.some (decide (p a n))) )).mpr
  constructor
  · simpa using Nat.find_spec (he a)
  · intro m hm
    simpa only [Part.mem_some_iff, eq_comm (a := false), decide_eq_false_iff_not] using Nat.find_min (he a) hm

theorem of_enclosures {f : A → ℝ} {q e : A × ℕ → ℚ}
    (hq : Computable q) (he : Computable e)
    (bound : ∀ a n, |f a - (q (a,n) : ℝ)| ≤ (e (a,n) : ℝ))
    (small : ∀ a, Tendsto (fun n => (e (a,n) : ℝ)) atTop (𝓝 0)) : Effective f := by
  have existsSmall : ∀ an : A × ℕ, ∃ k, e (an.1,k) ≤ qerror an.2 := by
    intro an
    have hh := (small an.1).eventually (gt_mem_nhds (error_pos an.2))
    obtain ⟨k,hk⟩ := hh.exists
    exact ⟨k, by exact_mod_cast (show (e (an.1,k) : ℝ) ≤ (qerror an.2 : ℝ) by simpa using hk.le)⟩
  have hc : Computable (fun p : (A × ℕ) × ℕ => decide (e (p.1.1,p.2) ≤ qerror p.1.2)) :=
    RecursiveArithmetic.ratLE.decide.to_comp.comp
      (he.comp ((Computable.fst.comp Computable.fst).pair Computable.snd))
      (qerror_primrec.to_comp.comp (Computable.snd.comp Computable.fst))
  let pick (an : A × ℕ) := Nat.find (existsSmall an)
  have hpick := computable_find (A := A × ℕ) (p := fun (an : A × ℕ) (k : ℕ) => e (an.1,k) ≤ qerror an.2) hc existsSmall
  have hfinal : Computable (fun an => q (an.1,pick an)) := hq.comp (Computable.fst.pair hpick)
  refine ⟨fun an => q (an.1,pick an), hfinal, ?_⟩
  intro a n
  apply (bound a (pick (a,n))).trans
  rw [← cast_qerror]
  exact_mod_cast Nat.find_spec (existsSmall (a,n))

theorem rational {q : A → ℚ} (hq : Computable q) : Effective (fun a => (q a : ℝ)) :=
  ⟨fun an => q an.1, hq.comp Computable.fst, fun a n => by simpa using (error_pos n).le⟩

omit [Primcodable A] in
theorem Effective.approximants_tendsto {f : A → ℝ} {q : A × ℕ → ℚ}
    (he : ∀ a n, |f a - (q (a,n) : ℝ)| ≤ error n) (a : A) :
    Tendsto (fun n => (q (a,n) : ℝ)) atTop (𝓝 (f a)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) _ error_tendsto
  intro n
  simpa [Real.dist_eq, abs_sub_comm] using he a n
end
end CertifiedReal

attribute [fun_prop] Computable
attribute [fun_prop] Computable.id Computable.const Computable.comp Computable.pair Computable.fst Computable.snd
attribute [fun_prop] Primrec.to_comp

end
end PeriodicLattice

end OAI
end

section
-- module Solutions.OAIQ067_SAT.PeriodicLattice_ElementaryFunctions
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certified effective inversion, powers and exponential evaluation. -/

namespace PeriodicLattice

noncomputable section

namespace CertifiedReal
open Encodable Filter Topology
local instance elementaryFunctionsLocal2 : Primcodable ℚ := RecursiveArithmetic.ratPrimcodable
section
variable {A B : Type*} [Primcodable A] [Primcodable B]

@[fun_prop] theorem computable_sum {m : A → ℕ} {f : A → ℕ → ℚ}
    (hm : Computable m) (hf : Computable₂ f) :
    Computable (fun a => ∑ i ∈ Finset.range (m a), f a i) := by
  have hv := hf.comp (g := fun p : A × (ℕ × ℚ) => p.1)
    (h := fun p => p.2.1) Computable.fst (Computable.fst.comp Computable.snd)
  have hstep := RecursiveArithmetic.rat_add.to_comp.comp
    (g := fun p : A × (ℕ × ℚ) => (p.2.2, f p.1 p.2.1))
    ((Computable.snd.comp Computable.snd).pair hv)
  exact (Computable.nat_rec hm (Computable.const 0) hstep.to₂).of_eq (fun a => by
    induction m a with
    | zero => simp
    | succ n ih => simp [Finset.sum_range_succ, ih])

theorem rat_abs_bound (q : ℚ) : |(q : ℝ)| ≤ (q.num.natAbs : ℝ) := by
  have heq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
    exact_mod_cast (Rat.num_div_den q).symm
  rw [heq, abs_div, abs_of_pos (show (0 : ℝ) < (q.den : ℝ) from Nat.cast_pos.mpr q.den_pos), ← Int.cast_abs,
    Int.abs_eq_natAbs, Int.cast_natCast]
  exact (div_le_self (Nat.cast_nonneg _) (by exact_mod_cast q.den_pos)).trans le_rfl

theorem Effective.exp {f : A → ℝ} (hf : Effective f) : Effective (fun a => Real.exp (f a)) := by
  obtain ⟨q,hq,bq⟩ := hf
  let M (a : A) : ℕ := (q (a,0)).num.natAbs + 3
  have hM : Computable M := by unfold M; fun_prop
  have b (a : A) (n : ℕ) : |(q (a,n) : ℝ)| ≤ (M a : ℝ) := by
    have hf0 : |f a| ≤ (q (a,0)).num.natAbs + 1 := by
      have ht := (abs_add_le (f a - q (a,0)) (q (a,0))).trans
        (add_le_add ((bq a 0).trans (error_le_one 0)) (rat_abs_bound _))
      rw [sub_add_cancel] at ht
      linarith
    have ht := (abs_add_le ((q (a,n) : ℝ) - f a) (f a)).trans
      (add_le_add (by simpa only [abs_sub_comm] using (bq a n).trans (error_le_one n)) hf0)
    rw [sub_add_cancel] at ht
    dsimp [M]; push_cast; linarith
  have diff (a : A) (n : ℕ) :
      |Real.exp (f a) - Real.exp (q (a,n))| ≤ 2 * 3 ^ M a * error n := by
    have he := Real.abs_exp_sub_one_le ((bq a n).trans (error_le_one n))
    have hqM : Real.exp (q (a,n)) ≤ 3 ^ M a := by
      apply (Real.exp_le_exp.mpr ((le_abs_self _).trans (b a n))).trans
      simpa only [← Real.exp_nat_mul, mul_one] using
        (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le (M a))
    calc
      |Real.exp (f a) - Real.exp (q (a,n))| =
          |Real.exp (f a - q (a,n)) - 1| * Real.exp (q (a,n)) := by
        have heq : Real.exp (f a) - Real.exp (q (a,n)) =
            (Real.exp (f a - q (a,n)) - 1) * Real.exp (q (a,n)) := by
          rw [sub_mul, one_mul, ← Real.exp_add, sub_add_cancel]
        rw [heq, abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ (2 * error n) * 3 ^ M a :=
        mul_le_mul (he.trans (mul_le_mul_of_nonneg_left (bq a n) (by norm_num))) hqM
          (Real.exp_pos _).le (mul_nonneg (by norm_num) (error_pos n).le)
      _ = _ := by ring
  let N (a : A) (n : ℕ) := 2 * M a + 1 + n
  refine of_enclosures
    (q := fun an => ∑ i ∈ Finset.range (N an.1 an.2), q an ^ i / (i.factorial : ℚ))
    (e := fun an => 2 * 3 ^ M an.1 * qerror an.2 +
      2 * (M an.1 : ℚ) ^ N an.1 an.2 / (N an.1 an.2).factorial)
    (by
      apply computable_sum
      · unfold N; fun_prop
      · change Computable (fun p : (A × ℕ) × ℕ => q p.1 ^ p.2 / (p.2.factorial : ℚ))
        fun_prop)
    (by unfold N; fun_prop) ?_ ?_
  · intro a n
    have htail := Complex.exp_bound' (x := (q (a,n) : ℝ)) (n := N a n) (by
      rw [Complex.norm_real, Real.norm_eq_abs]
      apply (div_le_div_of_nonneg_right (b a n) (by positivity)).trans
      apply (div_le_iff₀ (by positivity)).mpr
      dsimp [N]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) n])
    have htail' : |Real.exp (q (a,n)) - ∑ i ∈ Finset.range (N a n), (q (a,n) : ℝ)^i / i.factorial| ≤
        2 * (M a : ℝ) ^ N a n / (N a n).factorial := by
      have htailR : |Real.exp (q (a,n)) - ∑ i ∈ Finset.range (N a n), (q (a,n) : ℝ)^i / i.factorial| ≤
          |(q (a,n) : ℝ)| ^ N a n / (N a n).factorial * 2 := by
        simpa only [← Complex.ofReal_exp, ← Complex.ofReal_pow, ← Complex.ofReal_natCast,
          ← Complex.ofReal_div, ← Complex.ofReal_sum, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs] using htail
      apply htailR.trans
      rw [div_mul_eq_mul_div, mul_comm _ (2 : ℝ)]
      gcongr
      exact b a n
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_sum, cast_qerror]
    exact (abs_sub_le _ _ _).trans (add_le_add (diff a n) htail')
  · intro a
    have hn : Tendsto (fun n => N a n) atTop atTop :=
      tendsto_atTop_mono (fun n : ℕ => show n ≤ N a n by dsimp [N]; omega) tendsto_id
    have ht := (Real.summable_pow_div_factorial (M a : ℝ)).tendsto_atTop_zero.comp hn
    simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_natCast,
      cast_qerror, Rat.cast_div, Function.comp_apply, mul_div_assoc, mul_zero, add_zero] using
      (error_tendsto.const_mul (2 * 3 ^ M a)).add (ht.const_mul 2)

end
end CertifiedReal

end
end PeriodicLattice

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Clauses
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Signed variable sets, clause cardinalities, and the exact probability of killing
a nonempty solution set.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def clauseSupport {n k : ℕ} (C : ProperClause n k) : Finset (Fin n) :=
  Finset.univ.filter fun i => (C.val i).isSome

@[simp] theorem clauseSupport_card {n k : ℕ} (C : ProperClause n k) :
    (clauseSupport C).card = k := C.property

@[simp] theorem mem_clauseSupport {n k : ℕ} (C : ProperClause n k) (i : Fin n) :
    i ∈ clauseSupport C ↔ (C.val i).isSome := by
  simp [clauseSupport]

abbrev VariableSet (n k : ℕ) := ↥((Finset.univ : Finset (Fin n)).powersetCard k)

abbrev SignedVariableSet (n k : ℕ) := Σ s : VariableSet n k, ↥s.val → Bool

def clauseFromSigns {n k : ℕ} (s : VariableSet n k) (b : ↥s.val → Bool) :
    ProperClause n k :=
  ⟨fun i => if h : i ∈ s.val then some (b ⟨i, h⟩) else none, by
    have hs : (Finset.univ.filter fun i : Fin n =>
        (if h : i ∈ s.val then some (b ⟨i, h⟩) else none).isSome) = s.val := by
      ext i
      by_cases hi : i ∈ s.val <;> simp [hi]
    rw [hs]
    exact (Finset.mem_powersetCard.mp s.property).2⟩

@[simp] theorem clauseSupport_fromSigns {n k : ℕ} (s : VariableSet n k)
    (b : ↥s.val → Bool) : clauseSupport (clauseFromSigns s b) = s.val := by
  ext i
  by_cases hi : i ∈ s.val <;> simp [clauseSupport, clauseFromSigns, hi]

def clauseToSigns {n k : ℕ} (C : ProperClause n k) : SignedVariableSet n k :=
  ⟨⟨clauseSupport C, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, clauseSupport_card C⟩⟩,
    fun i => (C.val i.val).getD false⟩

def properClauseEquiv (n k : ℕ) : ProperClause n k ≃ SignedVariableSet n k where
  toFun := clauseToSigns
  invFun := fun t => clauseFromSigns t.1 t.2
  left_inv C := by
    apply Subtype.ext
    funext i
    dsimp [clauseToSigns, clauseFromSigns]
    by_cases hi : i ∈ clauseSupport C
    · rw [ite_eq_left hi]
      exact Option.getD_of_ne_none (Option.isSome_iff_ne_none.mp
        ((mem_clauseSupport C i).mp hi)) false
    · rw [ite_eq_right hi]
      exact ((Option.not_isSome_iff_eq_none).mp (by simpa using hi)).symm
  right_inv t := by
    rcases t with ⟨s, b⟩
    apply Sigma.ext
    · apply Subtype.ext
      exact clauseSupport_fromSigns s b
    · apply Function.hfunext (by
        change ↥(clauseSupport (clauseFromSigns s b)) = ↥s.val
        rw [clauseSupport_fromSigns])
      intro i j hij
      apply heq_of_eq
      have hv : i.val = j.val := by
        exact (Subtype.heq_iff_coe_eq (fun x => by
          change x ∈ clauseSupport (clauseFromSigns s b) ↔ x ∈ s.val
          rw [clauseSupport_fromSigns])).mp hij
      simp [clauseToSigns, clauseFromSigns, hv, j.property]

@[simp] theorem card_variableSet (n k : ℕ) :
    Fintype.card (VariableSet n k) = n.choose k := by
  simp [VariableSet]

@[simp] theorem card_properClause (n k : ℕ) :
    Fintype.card (ProperClause n k) = n.choose k * 2 ^ k := by
  rw [Fintype.card_congr (properClauseEquiv n k), Fintype.card_sigma]
  have hc (s : VariableSet n k) : Fintype.card (↥s.val → Bool) = 2 ^ k := by
    simp [(Finset.mem_powersetCard.mp s.property).2]
  simp_rw [hc]
  simp

@[simp] theorem card_formula (n k m : ℕ) :
    Fintype.card (Formula n k m) = (n.choose k * 2 ^ k) ^ m := by
  simp [Formula]

def KillsSolutions {n k : ℕ} (S : Finset (Assignment n)) (C : ProperClause n k) : Prop :=
  ∀ σ ∈ S, ¬ SatisfiesClause σ C

def forcedVariables {n : ℕ} (S : Finset (Assignment n)) : Finset (Fin n) :=
  Finset.univ.filter fun i => S.Nonempty ∧ ∃ b : Bool, ∀ σ ∈ S, σ i = b

@[simp] theorem forcedVariables_empty (n : ℕ) :
    forcedVariables (∅ : Finset (Assignment n)) = ∅ := by
  simp [forcedVariables]

def opposingClause {n k : ℕ} (σ : Assignment n) (s : VariableSet n k) :
    ProperClause n k := clauseFromSigns s (fun i => !(σ i.val))

@[simp] theorem support_opposingClause {n k : ℕ} (σ : Assignment n)
    (s : VariableSet n k) : clauseSupport (opposingClause σ s) = s.val :=
  clauseSupport_fromSigns _ _

noncomputable def uniformProbability {α : Type*} [Fintype α] (p : α → Prop) : ℝ := by
  classical
  exact (Fintype.card {a : α // p a} : ℝ) / Fintype.card α

noncomputable def killingProbability {n : ℕ} (k : ℕ) (S : Finset (Assignment n)) : ℝ :=
  uniformProbability (fun C : ProperClause n k => S.Nonempty ∧ KillsSolutions S C)

@[simp] theorem killingProbability_empty (n k : ℕ) :
    killingProbability k (∅ : Finset (Assignment n)) = 0 := by
  classical
  simp [killingProbability, uniformProbability]

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_FiniteMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Uniform finite expectations and variances.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def uniformMean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_ClauseProcess
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Coordinate erasure, independent clause averaging, survival probabilities, and
iterated replacement.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem support_card_cons {v : ℕ} (b : Option Bool) (C : Fin v → Option Bool) :
    (Finset.univ.filter fun i : Fin (v + 1) => (Fin.cons (α := fun _ => Option Bool) b C i).isSome).card =
      (if b.isSome then 1 else 0) + (Finset.univ.filter fun i => (C i).isSome).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fin.sum_univ_succ]
  simp

def prependAbsent {v k : ℕ} (C : ProperClause v k) : ProperClause (v + 1) k :=
  ⟨Fin.cons none C.val, by simpa [support_card_cons] using C.property⟩

def prependPresent {v k : ℕ} (hk : 0 < k) (C : ProperClause v (k - 1)) (b : Bool) :
    ProperClause (v + 1) k :=
  ⟨Fin.cons (some b) C.val, by
    rw [support_card_cons]
    simp only [Option.isSome_some, ↓reduceIte, C.property]
    omega⟩

@[simp] theorem satisfiesClause_prependAbsent {v k : ℕ}
    (σ : Assignment v) (b : Bool) (C : ProperClause v k) :
    SatisfiesClause (Fin.cons b σ) (prependAbsent C) ↔ SatisfiesClause σ C := by
  simp [SatisfiesClause, prependAbsent, Fin.exists_fin_succ]

@[simp] theorem satisfiesClause_prependPresent {v k : ℕ} (hk : 0 < k)
    (σ : Assignment v) (b t : Bool) (C : ProperClause v (k - 1)) :
    SatisfiesClause (Fin.cons b σ) (prependPresent hk C t) ↔ t = b ∨ SatisfiesClause σ C := by
  simp [SatisfiesClause, prependPresent, Fin.exists_fin_succ]

def addClause {n k : ℕ} (S : Finset (Assignment n)) (C : ProperClause n k) :
    Finset (Assignment n) := S.filter (fun σ => SatisfiesClause σ C)

@[simp] theorem mem_addClause {n k : ℕ} (S : Finset (Assignment n))
    (C : ProperClause n k) (σ : Assignment n) :
    σ ∈ addClause S C ↔ σ ∈ S ∧ SatisfiesClause σ C := by
  simp [addClause]

def restrictSolutions {n k : ℕ} {ι : Type*} [Fintype ι]
    (S : Finset (Assignment n)) (F : ι → ProperClause n k) : Finset (Assignment n) :=
  S.filter (fun σ => ∀ i, SatisfiesClause σ (F i))

@[simp] theorem mem_restrictSolutions {n k : ℕ} {ι : Type*} [Fintype ι]
    (S : Finset (Assignment n)) (F : ι → ProperClause n k) (σ : Assignment n) :
    σ ∈ restrictSolutions S F ↔ σ ∈ S ∧ ∀ i, SatisfiesClause σ (F i) := by
  simp [restrictSolutions]

def alive {n : ℕ} (S : Finset (Assignment n)) : ℝ := if S.Nonempty then 1 else 0

def clauseAverage {n : ℕ} (k : ℕ) (f : Finset (Assignment n) → ℝ)
    (S : Finset (Assignment n)) : ℝ :=
  uniformMean (fun C : ProperClause n k => f (addClause S C))

def survival {n : ℕ} (k : ℕ) (m : ℕ) (S : Finset (Assignment n)) : ℝ :=
  ((clauseAverage k)^[m] alive) S

@[simp] theorem survival_zero {n k : ℕ} (S : Finset (Assignment n)) :
    survival k 0 S = alive S := rfl

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Forcing
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Deletion and erasure of a coordinate, permutation symmetry, and the integrated
forcing bound.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev SplitClause (v k : ℕ) := ProperClause v k ⊕ (ProperClause v (k - 1) × Bool)

def DeletedSatisfied {v k : ℕ} (σ : Assignment v) : SplitClause v k → Prop
  | .inl C => SatisfiesClause σ C
  | .inr _ => True

def ErasedSatisfied {v k : ℕ} (σ : Assignment v) : SplitClause v k → Prop
  | .inl C => SatisfiesClause σ C
  | .inr Q => SatisfiesClause σ Q.1

def deletedSolutions {v k m : ℕ} (S : Finset (Assignment v)) (F : Fin m → SplitClause v k) :
    Finset (Assignment v) := S.filter (fun σ => ∀ i, DeletedSatisfied σ (F i))

def erasedSolutions {v k m : ℕ} (S : Finset (Assignment v)) (F : Fin m → SplitClause v k) :
    Finset (Assignment v) := S.filter (fun σ => ∀ i, ErasedSatisfied σ (F i))

@[simp] theorem mem_deletedSolutions {v k m : ℕ} (S : Finset (Assignment v))
    (F : Fin m → SplitClause v k) (σ : Assignment v) :
    σ ∈ deletedSolutions S F ↔ σ ∈ S ∧ ∀ i, DeletedSatisfied σ (F i) := by
  simp [deletedSolutions]

@[simp] theorem mem_erasedSolutions {v k m : ℕ} (S : Finset (Assignment v))
    (F : Fin m → SplitClause v k) (σ : Assignment v) :
    σ ∈ erasedSolutions S F ↔ σ ∈ S ∧ ∀ i, ErasedSatisfied σ (F i) := by
  simp [erasedSolutions]

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Variance
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Stopped satisfiable lifetimes, insertion delays, and the coordinate-omission
variance bound in terms of integrated forcing.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

@[simp] theorem addClause_empty {n k : ℕ} (C : ProperClause n k) :
    addClause ∅ C = ∅ := by simp [addClause]

@[simp] theorem alive_empty {n : ℕ} : alive (∅ : Finset (Assignment n)) = 0 := by simp [alive]

def lifetime {n : ℕ} (k : ℕ) : (m : ℕ) → Finset (Assignment n) → Formula n k m → ℝ
  | 0, _, _ => 0
  | m + 1, S, F => alive (addClause S (F 0)) +
      lifetime k m (addClause S (F 0)) (Fin.tail F)

@[simp] theorem lifetime_zero {n k : ℕ} (S : Finset (Assignment n)) (F : Formula n k 0) :
    lifetime k 0 S F = 0 := rfl

@[simp] theorem lifetime_cons {n k m : ℕ} (S : Finset (Assignment n)) (C : ProperClause n k)
    (F : Formula n k m) : lifetime k (m + 1) S (Fin.cons C F) =
      alive (addClause S C) + lifetime k m (addClause S C) F := rfl

@[simp] theorem lifetime_empty {n k m : ℕ} (F : Formula n k m) : lifetime k m ∅ F = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [lifetime, ih]

def lifetimeMean {n : ℕ} (k m : ℕ) (S : Finset (Assignment n)) : ℝ :=
  uniformMean (lifetime k m S)

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Concentration
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Normalized capped centers and polynomial concentration of the proper-clause
satisfiability probability.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def capMultiplier (k : ℕ) : ℕ := 2^(k + 1)

def mainCap (n k : ℕ) : ℕ := capMultiplier k * n

def center (n k : ℕ) : ℝ :=
  lifetimeMean k (mainCap n k) (Finset.univ : Finset (Assignment n)) / n

def varianceConstant (k : ℕ) : ℝ :=
  2 * (capMultiplier k : ℝ)^3 * k * (2 * k + capMultiplier k + 2)

def delta (k : ℕ) : ℝ := ((k : ℝ) - 2) / (4 * k)

def eta (k : ℕ) : ℝ := ((k : ℝ) - 2) / (2 * k)

def fluctuationWindow (n k : ℕ) : ℝ := (n : ℝ) ^ (1 - delta k)

def concentrationError (n k : ℕ) : ℝ := varianceConstant k * (n : ℝ) ^ (-eta k)

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_CenterBounds
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite union bounds, a matching criterion for satisfiability, and positive finite
bounds for the normalized centers.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def smallDensity : ℝ := Real.exp (-2) / 4

def lowerCenterBound : ℝ := smallDensity / 4

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Interpolation
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Auxiliary ordered clauses allow repeated variables. Commuting finite averaging
operators give the fixed-count partition interpolation corresponding to the
marked-Poisson comparison.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev AuxiliaryClause (n k : ℕ) := Fin k → (Fin n × Bool)

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Transfer
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The exact probability of distinct variables, birthday bounds, and deletion and
thinning comparisons transfer auxiliary probabilities to the proper-clause law.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def repeatPairs (k : ℕ) : ℝ := (k.choose 2 : ℝ)

@[simp] theorem repeatPairs_zero : repeatPairs 0 = 0 := by norm_num [repeatPairs]

def transferFactor (k : ℕ) : ℝ := Real.exp (-2 * (capMultiplier k : ℝ) * repeatPairs k)

def transferLower (k : ℕ) : ℝ := transferFactor k / 2

def samplingError (n k : ℕ) : ℝ :=
  (capMultiplier k : ℝ) * n / (fluctuationWindow n k)^2

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_CenterComparison
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Partition interpolation and concentration yield summable-error comparisons
for centers of two blocks and of neighboring sizes.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def densityWindow (n k : ℕ) : ℝ := (n : ℝ)^(-delta k)

def neighborFactor (k : ℕ) : ℝ := Real.exp (-2 * (capMultiplier k : ℝ))

def neighborLower (k : ℕ) : ℝ := neighborFactor k * transferLower k

structure CenterRegular (k n : ℕ) : Prop where
  size : k + 1 ≤ n
  repetition : 2 * repeatPairs k ≤ n
  error : concentrationError n k ≤ 1 / 2
  sampling : samplingError n k ≤ 1 / 4
  sumError : concentrationError n k < (transferLower k)^2 / 2
  neighborError : concentrationError n k < neighborLower k
  centerLower : lowerCenterBound ≤ center n k
  densitySmall : 2 * densityWindow n k ≤ lowerCenterBound
  windowLarge : (capMultiplier k : ℝ) ≤ fluctuationWindow n k

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RapidForcing_IntegerPrimrec
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Encodable Denumerable
namespace RapidForcing
namespace EffectiveArithmetic

lemma encode_int_ofNat (n : ℕ) : Encodable.encode (Int.ofNat n) = 2 * n := by
  simp [encode, Equiv.intEquivNat, Equiv.intEquivNatSumNat,
    Equiv.natSumNatEquivNat]
  change Nat.bit false n = _
  simp [Nat.bit_val]

lemma encode_int_negSucc (n : ℕ) : Encodable.encode (Int.negSucc n) = 2 * n + 1 := by
  simp [encode, Equiv.intEquivNat, Equiv.intEquivNatSumNat,
    Equiv.natSumNatEquivNat]

lemma ofNat_int (n : ℕ) : Denumerable.ofNat ℤ n =
    if n % 2 = 0 then Int.ofNat (n / 2) else Int.negSucc (n / 2) := by
  apply Encodable.encode_injective
  rw [encode_ofNat]
  split_ifs with hn
  · rw [encode_int_ofNat]
    omega
  · rw [encode_int_negSucc]
    omega

lemma primrec_int_ofNat : Primrec Int.ofNat :=
  Primrec.encode_iff.mp ((Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).of_eq
    (fun n => (encode_int_ofNat n).symm))

lemma primrec_int_negSucc : Primrec Int.negSucc :=
  Primrec.encode_iff.mp ((Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 1)).of_eq
      (fun n => (encode_int_negSucc n).symm))

lemma primrec_int_cases {A B : Type} [Primcodable A] [Primcodable B]
    {f : A → ℤ} (hf : Primrec f) {p q : A → ℕ → B}
    (hp : Primrec₂ p) (hq : Primrec₂ q) :
    Primrec (fun a => Int.rec (motive := fun _ => B) (p a) (q a) (f a)) := by
  have he := Primrec.encode.comp hf
  have hd := Primrec.nat_div.comp he (Primrec.const 2)
  have hb := Primrec.nat_mod.comp he (Primrec.const 2)
  have h := Primrec.ite (Primrec.eq.comp hb (Primrec.const 0))
    (hp.comp Primrec.id hd) (hq.comp Primrec.id hd)
  apply h.of_eq
  intro a
  have hh := ofNat_int (Encodable.encode (f a))
  rw [ofNat_encode] at hh
  conv_rhs => rw [hh]
  split_ifs <;> rfl

lemma primrec_int_natAbs : Primrec Int.natAbs := by
  have h := primrec_int_cases Primrec.id Primrec₂.right (Primrec.succ.comp Primrec.snd).to₂
  exact h.of_eq (fun z => by cases z <;> rfl)

lemma primrec_int_toNat : Primrec Int.toNat := by
  have h := primrec_int_cases Primrec.id Primrec₂.right (Primrec₂.const 0)
  exact h.of_eq (fun z => by cases z <;> rfl)

lemma primrec_int_neg : Primrec (fun z : ℤ => -z) := by
  have hn : Primrec (fun n : ℕ => -(n : ℤ)) :=
    (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 0)
      (primrec_int_negSucc.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))).of_eq
        (fun n => by cases n <;> simp [Int.negSucc_eq])
  have h := primrec_int_cases Primrec.id (hn.comp Primrec.snd).to₂
    (primrec_int_ofNat.comp (Primrec.succ.comp Primrec.snd)).to₂
  exact h.of_eq (fun z => by cases z <;> rfl)

end EffectiveArithmetic
end RapidForcing

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RapidForcing_ArithmeticAutomation
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Encodable Denumerable
namespace RapidForcing.EffectiveArithmetic

attribute [fun_prop] Primrec PrimrecPred Computable
attribute [fun_prop] Primrec.id Primrec.const Primrec.comp Primrec.fst Primrec.snd
  Primrec.pair Primrec.encode Primrec.decode Primrec.option_some Primrec.unpair
  Primrec.succ Primrec.pred Primrec.ite PrimrecPred.comp PrimrecPred.not PrimrecPred.and
  PrimrecPred.or Computable.id Computable.const Computable.comp Computable.fst Computable.snd
  Computable.pair Computable.encode Computable.decode Computable.option_some
attribute [fun_prop] primrec_int_ofNat primrec_int_negSucc primrec_int_natAbs
  primrec_int_toNat primrec_int_neg

@[fun_prop] lemma primrec_int_cast : Primrec (fun n : ℕ => (n : ℤ)) := primrec_int_ofNat

@[fun_prop] lemma primrec_nat_add : Primrec (fun p : ℕ × ℕ => p.1 + p.2) := Primrec.nat_add
@[fun_prop] lemma primrec_nat_sub : Primrec (fun p : ℕ × ℕ => p.1 - p.2) := Primrec.nat_sub
@[fun_prop] lemma primrec_nat_mul : Primrec (fun p : ℕ × ℕ => p.1 * p.2) := Primrec.nat_mul
@[fun_prop] lemma primrec_nat_mod : Primrec (fun p : ℕ × ℕ => p.1 % p.2) := Primrec.nat_mod
@[fun_prop] lemma primrec_nat_le : PrimrecPred (fun p : ℕ × ℕ => p.1 ≤ p.2) := Primrec.nat_le
@[fun_prop] lemma primrec_nat_lt : PrimrecPred (fun p : ℕ × ℕ => p.1 < p.2) := Primrec.nat_lt
@[fun_prop] lemma primrec_eq {A : Type} [Primcodable A] :
    PrimrecPred (fun p : A × A => p.1 = p.2) := Primrec.eq

@[fun_prop] lemma primrec_int_subNat : Primrec (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2) := by
  have h : Primrec (fun p : ℕ × ℕ => if p.2 ≤ p.1 then Int.ofNat (p.1 - p.2)
      else - Int.ofNat (p.2 - p.1)) := by fun_prop
  exact h.of_eq (fun p => by split_ifs <;>
    simp only [Int.ofNat_eq_natCast] <;> omega)

lemma int_difference_parts (z : ℤ) : (z.toNat : ℤ) - (-z).toNat = z := by omega

@[fun_prop] lemma primrec_int_add : Primrec (fun p : ℤ × ℤ => p.1 + p.2) := by
  have h : Primrec (fun p : ℤ × ℤ =>
      ((p.1.toNat + p.2.toNat : ℕ) : ℤ) - ((-p.1).toNat + (-p.2).toNat : ℕ)) :=
    primrec_int_subNat.comp (show Primrec (fun p : ℤ × ℤ =>
      (p.1.toNat + p.2.toNat, (-p.1).toNat + (-p.2).toNat)) by fun_prop)
  exact h.of_eq (fun p => by omega)

@[fun_prop] lemma primrec_int_sub : Primrec (fun p : ℤ × ℤ => p.1 - p.2) := by
  simpa [sub_eq_add_neg] using (show Primrec (fun p : ℤ × ℤ => p.1 + -p.2) by fun_prop)

@[fun_prop] lemma primrec_int_mul : Primrec (fun p : ℤ × ℤ => p.1 * p.2) := by
  have h : Primrec (fun p : ℤ × ℤ =>
    ((p.1.toNat * p.2.toNat + (-p.1).toNat * (-p.2).toNat : ℕ) : ℤ) -
      ((p.1.toNat * (-p.2).toNat + (-p.1).toNat * p.2.toNat : ℕ) : ℤ)) := by fun_prop
  apply h.of_eq
  intro p
  push_cast
  conv_rhs => rw [← int_difference_parts p.1, ← int_difference_parts p.2]
  ring

@[fun_prop] lemma primrec_int_le : PrimrecPred (fun p : ℤ × ℤ => p.1 ≤ p.2) := by
  have h : PrimrecPred (fun p : ℤ × ℤ =>
    p.1.toNat + (-p.2).toNat ≤ p.2.toNat + (-p.1).toNat) := by fun_prop
  exact h.of_eq (fun p => by omega)

@[fun_prop] lemma primrec_nat_gcd : Primrec (fun p : ℕ × ℕ => p.1.gcd p.2) := by
  have h : Primrec (fun p : ℕ × ℕ => Nat.findGreatest (fun k => p.1 % k = 0 ∧ p.2 % k = 0)
      (p.1 + p.2)) := by
    apply Primrec.nat_findGreatest (by fun_prop)
    unfold PrimrecRel
    fun_prop
  apply h.of_eq
  rintro ⟨m, n⟩
  by_cases hmn : m + n = 0
  · have hm : m = 0 := by omega
    have hn : n = 0 := by omega
    subst m; subst n; rfl
  have hg : m.gcd n ≤ m + n := by
    by_cases hm : 0 < m
    · exact (Nat.gcd_le_left n hm).trans (Nat.le_add_right _ _)
    · have hn : 0 < n := by omega
      exact (Nat.gcd_le_right m hn).trans (Nat.le_add_left _ _)
  have hgpos : 0 < m.gcd n := by
    by_cases hm : 0 < m
    · exact Nat.gcd_pos_of_pos_left n hm
    · exact Nat.gcd_pos_of_pos_right m (by omega)
  have hd : ∀ k, m % k = 0 ∧ n % k = 0 ↔ k ∣ m.gcd n := by
    intro k
    rw [← Nat.dvd_iff_mod_eq_zero, ← Nat.dvd_iff_mod_eq_zero, Nat.dvd_gcd_iff]
  apply le_antisymm
  · have hs := Nat.findGreatest_spec (P := fun k => m % k = 0 ∧ n % k = 0) hg ((hd _).mpr (dvd_refl _))
    exact Nat.le_of_dvd hgpos ((hd _).mp hs)
  · exact Nat.le_findGreatest hg ((hd _).mpr (dvd_refl _))

end RapidForcing.EffectiveArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RapidForcing_ComputableAutomation
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Encodable Denumerable
namespace RapidForcing.EffectiveArithmetic

attribute [fun_prop] Computable
attribute [fun_prop] Primrec.to_comp

def CompPred {A : Type} [Primcodable A] (p : A → Prop) [DecidablePred p] : Prop :=
  Computable (fun a => decide (p a))
attribute [fun_prop] CompPred

@[fun_prop] lemma compPred_primrec {A : Type} [Primcodable A] {p : A → Prop}
    [DecidablePred p] (hp : PrimrecPred p) : CompPred p := hp.decide.to_comp

@[fun_prop] lemma compPred_comp {A B : Type} [Primcodable A] [Primcodable B]
    {p : B → Prop} [DecidablePred p] {f : A → B}
    (hp : CompPred p) (hf : Computable f) : CompPred (fun a => p (f a)) := hp.comp hf

@[fun_prop] lemma compPred_and {A : Type} [Primcodable A] {p q : A → Prop}
    [DecidablePred p] [DecidablePred q] (hp : CompPred p) (hq : CompPred q) :
    CompPred (fun a => p a ∧ q a) := by
  exact (Primrec.and.to_comp.comp hp hq).of_eq (fun a => by simp)

@[fun_prop] lemma compPred_or {A : Type} [Primcodable A] {p q : A → Prop}
    [DecidablePred p] [DecidablePred q] (hp : CompPred p) (hq : CompPred q) :
    CompPred (fun a => p a ∨ q a) := by
  exact (Primrec.or.to_comp.comp hp hq).of_eq (fun a => by simp)

@[fun_prop] lemma compPred_not {A : Type} [Primcodable A] {p : A → Prop}
    [DecidablePred p] (hp : CompPred p) : CompPred (fun a => ¬p a) := by
  exact (Primrec.not.to_comp.comp hp).of_eq (fun a => by simp)

@[fun_prop] lemma computable_ite {A B : Type} [Primcodable A] [Primcodable B]
    {p : A → Prop} [DecidablePred p] {f g : A → B}
    (hp : CompPred p) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if p a then f a else g a) := by
  exact (Computable.cond hp hf hg).of_eq (fun a => by simp)

@[fun_prop] lemma compPred_decide {A : Type} [Primcodable A] {p : A → Prop}
    [DecidablePred p] (hp : CompPred p) : Computable (fun a => decide (p a)) := hp

lemma CompPred.of_eq {A : Type} [Primcodable A] {p q : A → Prop}
    [DecidablePred p] [DecidablePred q] (hp : CompPred p) (h : ∀ a, p a ↔ q a) : CompPred q :=
  Computable.of_eq hp (fun a => by simp [h a])

lemma computable_of_compGraph {A B : Type} [Primcodable A] [Primcodable B]
    (f : A → B) (R : A → B → Prop) [DecidableRel R]
    (hR : CompPred (fun p : A × B => R p.1 p.2))
    (h : ∀ a b, R a b ↔ b = f a) : Computable f := by
  let test : A → ℕ → Option B := fun a n =>
    (decode n).bind fun b => if R a b then some b else none
  have ht : Computable₂ test :=
    Computable.option_bind (Computable.decode.comp Computable.snd)
      (computable_ite (compPred_comp hR ((Computable.fst.comp Computable.fst).pair Computable.snd))
        (Computable.option_some.comp Computable.snd) (Computable.const none)).to₂
  apply (Partrec.rfindOpt ht).of_eq_tot
  intro a
  have hd : (Nat.rfindOpt (test a)).Dom := Nat.rfindOpt_dom.mpr
    ⟨encode (f a), f a, by simp [test, Encodable.encodek, (h a (f a)).mpr rfl]⟩
  have hm : (Nat.rfindOpt (test a)).get hd ∈ Nat.rfindOpt (test a) := ⟨hd, rfl⟩
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hm
  have he : (Nat.rfindOpt (test a)).get hd = f a := by
    simp only [test, Option.mem_bind_iff] at hn
    obtain ⟨b, _, hb⟩ := hn
    split_ifs at hb with hab
    · obtain rfl := Option.mem_some_iff.mp hb
      exact (h a _).mp hab
    · contradiction
  exact he ▸ hm

end RapidForcing.EffectiveArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RapidForcing_RationalProfiles
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators Topology
open Filter
namespace RapidForcing.EffectiveProfile

structure Ball where
  center : ℚ
  radius : ℚ
  deriving DecidableEq

def Ball.exact (q : ℚ) : Ball := ⟨q, 0⟩
def Ball.add (a b : Ball) : Ball := ⟨a.center + b.center, a.radius + b.radius⟩
def Ball.mul (a b : Ball) : Ball :=
  ⟨a.center * b.center,
    |a.center| * b.radius + |b.center| * a.radius + a.radius * b.radius⟩

def Ball.denInv (a : Ball) : Ball :=
  ⟨(max (1 / 16) a.center)⁻¹, 256 * a.radius⟩

def Ball.Covers (a : Ball) (x : ℝ) : Prop := |(a.center : ℝ) - x| ≤ (a.radius : ℝ)

lemma Ball.Covers.radius_nonneg {a : Ball} {x : ℝ} (h : a.Covers x) : 0 ≤ a.radius := by
  exact_mod_cast (abs_nonneg _).trans h

lemma Ball.covers_exact (q : ℚ) : (Ball.exact q).Covers q := by
  simp [Ball.exact, Covers]

lemma Ball.Covers.add {a b : Ball} {x y : ℝ} (ha : a.Covers x) (hb : b.Covers y) :
    (a.add b).Covers (x + y) := by
  dsimp [Covers, Ball.add] at *
  push_cast
  calc
    |(a.center : ℝ) + b.center - (x + y)| = |(a.center - x) + (b.center - y)| := by congr 1; ring
    _ ≤ |(a.center : ℝ) - x| + |(b.center : ℝ) - y| := abs_add_le _ _
    _ ≤ _ := add_le_add ha hb

lemma Ball.Covers.mul {a b : Ball} {x y : ℝ} (ha : a.Covers x) (hb : b.Covers y) :
    (a.mul b).Covers (x * y) := by
  have he1 : (0 : ℝ) ≤ a.radius := by exact_mod_cast ha.radius_nonneg
  have he2 : (0 : ℝ) ≤ b.radius := by exact_mod_cast hb.radius_nonneg
  change |((a.center * b.center : ℚ) : ℝ) - x * y| ≤ _
  simp only [Ball.mul, Rat.cast_mul, Rat.cast_add, Rat.cast_abs]
  calc
    |(a.center : ℝ) * b.center - x*y| =
      |(a.center : ℝ) * (b.center - y) + (b.center : ℝ) * (a.center - x) -
        (a.center - x) * (b.center - y)| := by congr 1; ring
    _ ≤ |(a.center : ℝ) * (b.center - y)| + |(b.center : ℝ) * (a.center - x)| +
        |((a.center : ℝ) - x) * (b.center - y)| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by
      simp only [abs_mul]
      gcongr
      · exact hb
      · exact ha
      · exact ha
      · exact hb

lemma clamp_dist (c x : ℝ) (hx : (1 / 16 : ℝ) ≤ x) :
    |max (1 / 16) c - x| ≤ |c - x| := by
  by_cases hc : (1 / 16 : ℝ) ≤ c
  · rw [max_eq_right hc]
  · rw [max_eq_left (le_of_not_ge hc), abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith)]
    linarith

lemma Ball.Covers.denInv {a : Ball} {x : ℝ} (ha : a.Covers x) (hx : (1 / 16 : ℝ) ≤ x) :
    a.denInv.Covers x⁻¹ := by
  have hz : (1 / 16 : ℝ) ≤ max (1 / 16) (a.center : ℝ) := le_max_left _ _
  have hp : 0 < max (1 / 16) (a.center : ℝ) := lt_of_lt_of_le (by norm_num) hz
  have hxp : 0 < x := by linarith
  have hprod : (1 / 256 : ℝ) ≤ max (1 / 16) (a.center : ℝ) * x := by nlinarith
  change |(((max (1 / 16) a.center)⁻¹ : ℚ) : ℝ) - x⁻¹| ≤ _
  simp only [Ball.denInv, Rat.cast_inv, Rat.cast_max, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat, Rat.cast_mul]
  rw [inv_sub_inv hp.ne' hxp.ne', abs_div, abs_mul, abs_of_pos hp, abs_of_pos hxp,
    (div_le_iff₀ (mul_pos hp hxp))]
  calc
    |x - max (1 / 16) (a.center : ℝ)| = |max (1 / 16) (a.center : ℝ) - x| := abs_sub_comm _ _
    _ ≤ |(a.center : ℝ) - x| := clamp_dist _ _ hx
    _ ≤ (a.radius : ℝ) := ha
    _ ≤ 256 * (a.radius : ℝ) * (max (1 / 16) (a.center : ℝ) * x) := by
      have hnon : (0 : ℝ) ≤ a.radius := by exact_mod_cast ha.radius_nonneg
      nlinarith

def Encloses (b : ℕ → Ball) (x : ℝ) : Prop :=
  (∀ k, (b k).Covers x) ∧ Tendsto (fun k => ((b k).radius : ℝ)) atTop (𝓝 0)

lemma Encloses.centers {b : ℕ → Ball} {x : ℝ} (h : Encloses b x) :
    Tendsto (fun k => ((b k).center : ℝ)) atTop (𝓝 x) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  exact squeeze_zero (fun _ => norm_nonneg _) (fun k => by simpa only [Real.norm_eq_abs, Ball.Covers] using h.1 k) h.2

lemma encloses_exact (q : ℚ) : Encloses (fun _ => Ball.exact q) q :=
  ⟨fun _ => Ball.covers_exact _, by simp [Ball.exact]⟩

lemma Encloses.add {a b : ℕ → Ball} {x y : ℝ} (ha : Encloses a x) (hb : Encloses b y) :
    Encloses (fun k => (a k).add (b k)) (x + y) :=
  ⟨fun k => (ha.1 k).add (hb.1 k), by simpa only [Ball.add, Rat.cast_add, add_zero] using ha.2.add hb.2⟩

lemma Encloses.mul {a b : ℕ → Ball} {x y : ℝ} (ha : Encloses a x) (hb : Encloses b y) :
    Encloses (fun k => (a k).mul (b k)) (x * y) := by
  refine ⟨fun k => (ha.1 k).mul (hb.1 k), ?_⟩
  simpa only [Ball.mul, Rat.cast_add, Rat.cast_mul, Rat.cast_abs, mul_zero, add_zero]
    using ((ha.centers.abs.mul hb.2).add (hb.centers.abs.mul ha.2)).add (ha.2.mul hb.2)

lemma Encloses.denInv {a : ℕ → Ball} {x : ℝ} (ha : Encloses a x) (hx : (1 / 16 : ℝ) ≤ x) :
    Encloses (fun k => (a k).denInv) x⁻¹ :=
  ⟨fun k => (ha.1 k).denInv hx, by simpa [Ball.denInv] using ha.2.const_mul 256⟩

end RapidForcing.EffectiveProfile

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RapidForcing_RatPrimrec
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Encodable Denumerable
namespace RapidForcing.EffectiveArithmetic

lemma rat_encoding (q : ℚ) : encode q = encode (q.num, q.den) := rfl

lemma rat_roundtrip (n : ℕ) : encode (decode (α := ℚ) n) =
    encode ((decode (α := ℤ × ℕ) n).bind fun p =>
      if 0 < p.2 ∧ p.1.natAbs.Coprime p.2 then some (encode p) else none) := by
  simp only [Encodable.decode_ofEquiv, Encodable.decode_sigma_val,
    Encodable.decode_nat, Option.map_some, Option.bind_some, Option.map_map]
  simp only [Encodable.decode, Encodable.decodeSubtype, Option.bind_some]
  dsimp only [Equiv.symm_symm, Equiv.sigmaEquivProd, Equiv.coe_fn_mk, Function.comp_def]
  split_ifs with h <;>
    simp_all [Encodable.encode_ofEquiv, Encodable.Subtype.encode_eq, Nat.Coprime]
  split_ifs with hh
  · exact False.elim (h hh.1 hh.2)
  · rfl

instance ratPrimcodable : Primcodable ℚ :=
  { toEncodable := Rat.instEncodable
    prim := by
      have hg : Primrec (fun p : ℤ × ℕ =>
          if 0 < p.2 ∧ p.1.natAbs.Coprime p.2 then some (encode p) else none) := by
        fun_prop
      have hb : Primrec (fun n : ℕ => (decode (α := ℤ × ℕ) n).bind fun p =>
          if 0 < p.2 ∧ p.1.natAbs.Coprime p.2 then some (encode p) else none) :=
        Primrec.option_bind Primrec.decode (hg.comp Primrec.snd).to₂
      exact (Primrec.nat_iff.mp (Primrec.encode.comp hb)).of_eq (fun n => (rat_roundtrip n).symm) }

@[fun_prop] lemma primrec_rat_num : Primrec Rat.num := by
  have hp : Primrec (fun q : ℚ => (decode (α := ℤ × ℕ) (encode q)).getD (0, 0)) :=
    (Primrec.option_getD.comp (Primrec.decode.comp Primrec.encode) (Primrec.const (0, 0)))
  exact (Primrec.fst.comp hp).of_eq fun q => by rw [rat_encoding, Encodable.encodek]; rfl

@[fun_prop] lemma primrec_rat_den : Primrec Rat.den := by
  have hp : Primrec (fun q : ℚ => (decode (α := ℤ × ℕ) (encode q)).getD (0, 0)) :=
    (Primrec.option_getD.comp (Primrec.decode.comp Primrec.encode) (Primrec.const (0, 0)))
  exact (Primrec.snd.comp hp).of_eq fun q => by rw [rat_encoding, Encodable.encodek]; rfl

end RapidForcing.EffectiveArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RapidForcing_RatComputable
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Encodable Denumerable
namespace RapidForcing.EffectiveArithmetic

lemma computable_of_graph {A B : Type} [Primcodable A] [Primcodable B]
    (f : A → B) (R : A → B → Prop) [DecidableRel R]
    (hR : PrimrecPred (fun p : A × B => R p.1 p.2))
    (h : ∀ a b, R a b ↔ b = f a) : Computable f := by
  let test : A → ℕ → Option B := fun a n =>
    (decode n).bind fun b => if R a b then some b else none
  have ht : Primrec₂ test :=
    Primrec.option_bind (Primrec.decode.comp Primrec.snd)
      (Primrec.ite (hR.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))
        (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂
  apply (Partrec.rfindOpt ht.to_comp).of_eq_tot
  intro a
  have hd : (Nat.rfindOpt (test a)).Dom := Nat.rfindOpt_dom.mpr
    ⟨encode (f a), f a, by simp [test, Encodable.encodek, (h a (f a)).mpr rfl]⟩
  have hm : (Nat.rfindOpt (test a)).get hd ∈ Nat.rfindOpt (test a) := ⟨hd, rfl⟩
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hm
  have he : (Nat.rfindOpt (test a)).get hd = f a := by
    simp only [test, Option.mem_bind_iff] at hn
    obtain ⟨b, _, hb⟩ := hn
    split_ifs at hb with hab
    · obtain rfl := Option.mem_some_iff.mp hb
      exact (h a _).mp hab
    · contradiction
  exact he ▸ hm

@[fun_prop] lemma primrec_rat_le : PrimrecPred (fun p : ℚ × ℚ => p.1 ≤ p.2) := by
  exact (show PrimrecPred (fun p : ℚ × ℚ => p.1.num * (p.2.den : ℤ) ≤
      p.2.num * (p.1.den : ℤ)) by fun_prop).of_eq (fun p => (Rat.le_iff _ _).symm)

@[fun_prop] lemma primrec_rat_lt : PrimrecPred (fun p : ℚ × ℚ => p.1 < p.2) := by
  exact (PrimrecPred.not (primrec_rat_le.comp (Primrec.snd.pair Primrec.fst))).of_eq
    (fun p => not_le)

lemma rat_div_graph (n : ℤ) (d : ℕ) (q : ℚ) (hd : d ≠ 0) :
    q.num * (d : ℤ) = n * (q.den : ℤ) ↔ q = (n : ℚ) / d := by
  have hq : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  conv_rhs => rw [← Rat.num_div_den q, div_eq_div_iff hq hd']
  exact_mod_cast (Iff.rfl : q.num * (d : ℤ) = n * (q.den : ℤ) ↔ _)

@[fun_prop] lemma computable_rat_divNat : Computable (fun p : ℤ × ℕ => (p.1 : ℚ) / p.2) := by
  apply computable_of_graph _ (fun p q =>
      if p.2 = 0 then q = 0 else q.num * (p.2 : ℤ) = p.1 * (q.den : ℤ))
  · have hi : PrimrecPred (fun p : (ℤ × ℕ) × ℚ =>
        (p.1.2 = 0 ∧ p.2 = 0) ∨ (p.1.2 ≠ 0 ∧ p.2.num * (p.1.2 : ℤ) = p.1.1 * (p.2.den : ℤ))) := by fun_prop
    exact hi.of_eq (fun p => by split_ifs <;> simp_all)
  · intro p q
    split_ifs with hd
    · simp [hd]
    · exact rat_div_graph _ _ _ hd

@[fun_prop] lemma computable_rat_castInt : Computable (fun z : ℤ => (z : ℚ)) := by
  simpa using computable_rat_divNat.comp (Computable.id.pair (Computable.const 1))

@[fun_prop] lemma computable_rat_castNat : Computable (fun n : ℕ => (n : ℚ)) := by
  simpa only [Int.cast_natCast] using computable_rat_castInt.comp primrec_int_cast.to_comp

@[fun_prop] lemma computable_rat_add : Computable (fun p : ℚ × ℚ => p.1 + p.2) := by
  have hh : Primrec (fun p : ℚ × ℚ =>
      (p.1.num * (p.2.den : ℤ) + p.2.num * (p.1.den : ℤ), p.1.den * p.2.den)) := by fun_prop
  apply (computable_rat_divNat.comp hh.to_comp).of_eq
  intro p
  dsimp; push_cast
  conv_rhs => rw [← Rat.num_div_den p.1, ← Rat.num_div_den p.2]
  have h1 : (p.1.den : ℚ) ≠ 0 := by exact_mod_cast p.1.den_nz
  have h2 : (p.2.den : ℚ) ≠ 0 := by exact_mod_cast p.2.den_nz
  field_simp

@[fun_prop] lemma computable_rat_mul : Computable (fun p : ℚ × ℚ => p.1 * p.2) := by
  have hh : Primrec (fun p : ℚ × ℚ => (p.1.num * p.2.num, p.1.den * p.2.den)) := by fun_prop
  apply (computable_rat_divNat.comp hh.to_comp).of_eq
  intro p
  dsimp; push_cast
  rw [mul_div_mul_comm, Rat.num_div_den, Rat.num_div_den]

@[fun_prop] lemma computable_rat_neg : Computable (fun q : ℚ => -q) := by
  have hh : Primrec (fun q : ℚ => (-q.num, q.den)) := by fun_prop
  apply (computable_rat_divNat.comp hh.to_comp).of_eq
  intro q
  simp only [Int.cast_neg, neg_div, Rat.num_div_den]

@[fun_prop] lemma computable_rat_sub : Computable (fun p : ℚ × ℚ => p.1 - p.2) := by
  simpa only [sub_eq_add_neg] using (show Computable (fun p : ℚ × ℚ => p.1 + -p.2) by fun_prop)

end RapidForcing.EffectiveArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RapidForcing_RatOperations
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Encodable Denumerable
namespace RapidForcing.EffectiveArithmetic

lemma rat_divInt_graph (n d : ℤ) (q : ℚ) (hd : d ≠ 0) :
    q.num * d = n * (q.den : ℤ) ↔ q = (n : ℚ) / d := by
  have hq : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  conv_rhs => rw [← Rat.num_div_den q, div_eq_div_iff hq hd']
  exact_mod_cast (Iff.rfl : q.num * d = n * (q.den : ℤ) ↔ _)

@[fun_prop] lemma computable_rat_divInt : Computable (fun p : ℤ × ℤ => (p.1 : ℚ) / p.2) := by
  apply computable_of_graph _ (fun p q =>
      if p.2 = 0 then q = 0 else q.num * p.2 = p.1 * (q.den : ℤ))
  · have hi : PrimrecPred (fun p : (ℤ × ℤ) × ℚ =>
        (p.1.2 = 0 ∧ p.2 = 0) ∨ (p.1.2 ≠ 0 ∧ p.2.num * p.1.2 = p.1.1 * (p.2.den : ℤ))) := by fun_prop
    exact hi.of_eq (fun p => by split_ifs <;> simp_all)
  · intro p q
    split_ifs with hd
    · simp [hd]
    · exact rat_divInt_graph _ _ _ hd

@[fun_prop] lemma computable_rat_inv : Computable (fun q : ℚ => q⁻¹) := by
  have := computable_rat_divInt.comp (show Computable (fun q : ℚ => ((q.den : ℤ), q.num)) by fun_prop)
  exact this.of_eq (fun q => by simpa [Int.cast_natCast, inv_div] using congrArg Inv.inv (Rat.num_div_den q))

@[fun_prop] lemma computable_rat_div : Computable (fun p : ℚ × ℚ => p.1 / p.2) := by
  simpa [div_eq_mul_inv] using (show Computable (fun p : ℚ × ℚ => p.1 * p.2⁻¹) by fun_prop)

@[fun_prop] lemma computable_rat_abs : Computable (fun q : ℚ => |q|) := by
  apply Computable.of_eq (show Computable (fun q : ℚ => if 0 ≤ q then q else -q) by fun_prop)
  intro q
  split_ifs with h
  · exact (abs_of_nonneg h).symm
  · exact (abs_of_neg (lt_of_not_ge h)).symm

@[fun_prop] lemma computable_rat_max : Computable (fun p : ℚ × ℚ => max p.1 p.2) := by
  simpa only [max_def] using (show Computable (fun p : ℚ × ℚ => if p.1 ≤ p.2 then p.2 else p.1) by fun_prop)

@[fun_prop] lemma computable_rat_pow : Computable (fun p : ℚ × ℕ => p.1 ^ p.2) := by
  have h := Computable.nat_rec (f := fun p : ℚ × ℕ => p.2)
    (g := fun _ => (1 : ℚ)) (h := fun p r => r.2 * p.1)
    (by fun_prop) (by fun_prop) (by unfold Computable₂; fun_prop)
  apply h.of_eq
  intro p
  induction p.2 <;> simp [pow_succ, *]

@[fun_prop] lemma computable_rat_natCeil : Computable (fun q : ℚ => ⌈q⌉₊) := by
  apply computable_of_compGraph _ (fun q n : _ =>
      if n = (0 : ℕ) then q ≤ 0 else (n - 1 : ℚ) < q ∧ q ≤ (n : ℚ))
  · have hi : CompPred (fun p : ℚ × ℕ =>
        (p.2 = 0 ∧ p.1 ≤ 0) ∨ (p.2 ≠ 0 ∧ (p.2 - 1 : ℚ) < p.1 ∧ p.1 ≤ (p.2 : ℚ))) := by fun_prop
    exact hi.of_eq (fun p => by split_ifs <;> simp_all)
  · intro q n
    by_cases hn : n = 0
    · simp [hn, eq_comm, Nat.ceil_eq_zero]
    · simp only [ite_eq_right hn]
      rw [eq_comm, Nat.ceil_eq_iff hn]
      simp only [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn), Nat.cast_one]

@[fun_prop] lemma computable_rat_natFloor : Computable (fun q : ℚ => ⌊q⌋₊) := by
  apply computable_of_compGraph _ (fun q n : _ =>
      if n = (0 : ℕ) then q < 1 else (n : ℚ) ≤ q ∧ q < (n : ℚ) + 1)
  · have hi : CompPred (fun p : ℚ × ℕ =>
        (p.2 = 0 ∧ p.1 < 1) ∨ (p.2 ≠ 0 ∧ (p.2 : ℚ) ≤ p.1 ∧ p.1 < (p.2 : ℚ) + 1)) := by fun_prop
    exact hi.of_eq (fun p => by split_ifs <;> simp_all)
  · intro q n
    by_cases hn : n = 0
    · simp [hn, eq_comm, Nat.floor_eq_zero]
    · simp only [ite_eq_right hn]
      rw [eq_comm, Nat.floor_eq_iff' hn]

end RapidForcing.EffectiveArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RapidForcing_ExprCoding
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


open Encodable Denumerable Nat.Partrec
namespace RapidForcing.EffectiveArithmetic

@[fun_prop] lemma primrec_code_pair : Primrec (fun p : Code × Code => Code.pair p.1 p.2) :=
  Code.primrec₂_pair
@[fun_prop] lemma primrec_code_comp : Primrec (fun p : Code × Code => Code.comp p.1 p.2) :=
  Code.primrec₂_comp
@[fun_prop] lemma primrec_code_prec : Primrec (fun p : Code × Code => Code.prec p.1 p.2) :=
  Code.primrec₂_prec
attribute [fun_prop] Nat.Partrec.Code.primrec_rfind'

end RapidForcing.EffectiveArithmetic

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RapidForcing_RecursiveComputable
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Encodable Denumerable Function Nat.Partrec
namespace RapidForcing.EffectiveArithmetic

attribute [fun_prop] Computable.option_getD
  Primrec.list_length Primrec.list_reverse Primrec.list_head? Primrec.list_tail
  Primrec.list_range

@[fun_prop] lemma primrec_list_cons {A : Type} [Primcodable A] :
    Primrec (fun p : A × List A => p.1 :: p.2) := Primrec.list_cons

lemma computable_list_casesOn {A B S : Type} [Primcodable A] [Primcodable B] [Primcodable S]
    {f : A → List B} {g : A → S} {h : A → B × List B → S}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => List.casesOn (motive := fun _ => S) (f a) (g a) fun b l => h a (b, l)) := by
  have hd : Computable (fun a => (f a).head?) := Primrec.list_head?.to_comp.comp hf
  have ht : Computable (fun a => (f a).tail) := Primrec.list_tail.to_comp.comp hf
  exact (Computable.option_casesOn hd hg
    (hh.comp Computable.fst (Computable.snd.pair (ht.comp Computable.fst))).to₂).of_eq
      (fun a => by cases hfa : f a <;> simp [hfa])

lemma computable_nat_iterate {A S : Type} [Primcodable A] [Primcodable S]
    {f : A → ℕ} {g : A → S} {h : A → S → S}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (h a)^[f a] (g a)) := by
  exact (Computable.nat_rec hf hg
    ((hh.comp Computable.fst (Computable.snd.comp Computable.snd)).to₂)).of_eq
    (fun a => by induction f a <;> simp [Function.iterate_succ_apply', *])

lemma computable_list_foldl {A B S : Type} [Primcodable A] [Primcodable B] [Primcodable S]
    {f : A → List B} {g : A → S} {h : A → S × B → S}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (f a).foldl (fun s b => h a (s, b)) (g a)) := by
  let G (a : A) (v : S × List B) : S × List B :=
    List.casesOn v.2 v fun b l => (h a (v.1, b), l)
  have hG : Computable₂ G := computable_list_casesOn
    (Computable.snd.comp Computable.snd) Computable.snd
    ((hh.comp (Computable.fst.comp Computable.fst)
      (((Computable.fst.comp Computable.snd).comp Computable.fst).pair (Computable.fst.comp Computable.snd))).pair
      (Computable.snd.comp Computable.snd)).to₂
  have F := computable_nat_iterate (Computable.list_length.comp hf) (hg.pair hf) hG
  have he (a : A) (n : ℕ) (l : List B) (x : S) :
      (G a)^[n] (x, l) = ((l.take n).foldl (fun s b => h a (s, b)) x, l.drop n) := by
    induction n generalizing l x with
    | zero => rfl
    | succ n ih => cases l <;> simp [iterate_succ, comp_apply, G, ih]
  exact (Computable.fst.comp F).of_eq (fun a => by rw [he]; simp)

lemma computable_list_foldr {A B S : Type} [Primcodable A] [Primcodable B] [Primcodable S]
    {f : A → List B} {g : A → S} {h : A → B × S → S}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (f a).foldr (fun b s => h a (b, s)) (g a)) := by
  exact (computable_list_foldl (Computable.list_reverse.comp hf) hg
    (hh.comp Computable.fst ((Computable.snd.pair Computable.fst).comp Computable.snd)).to₂).of_eq
      (fun a => by rw [List.foldl_reverse])

end RapidForcing.EffectiveArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RapidForcing_ComputableProfiles
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Encodable
open scoped BigOperators
namespace RapidForcing.EffectiveProfile
open EffectiveArithmetic

def ballEquiv : Ball ≃ ℚ × ℚ :=
  ⟨fun b => (b.center, b.radius), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩
instance instPrimcodableBall : Primcodable Ball := Primcodable.ofEquiv (ℚ × ℚ) ballEquiv
@[fun_prop] lemma primrec_ball_center : Primrec Ball.center := by
  exact Primrec.fst.comp (Primrec.of_equiv (e := ballEquiv))
@[fun_prop] lemma primrec_ball_radius : Primrec Ball.radius := by
  exact Primrec.snd.comp (Primrec.of_equiv (e := ballEquiv))
@[fun_prop] lemma primrec_ball_mk : Primrec (fun p : ℚ × ℚ => Ball.mk p.1 p.2) := by
  apply Primrec.encode_iff.mp
  exact (Primrec.encode : Primrec (@encode (ℚ × ℚ) _))
@[fun_prop] lemma computable_ball_exact : Computable Ball.exact := by
  unfold Ball.exact; fun_prop
@[fun_prop] lemma computable_ball_add : Computable (fun p : Ball × Ball => p.1.add p.2) := by
  unfold Ball.add; fun_prop
@[fun_prop] lemma computable_ball_mul : Computable (fun p : Ball × Ball => p.1.mul p.2) := by
  unfold Ball.mul; fun_prop
@[fun_prop] lemma computable_ball_denInv : Computable Ball.denInv := by
  unfold Ball.denInv; fun_prop
end RapidForcing.EffectiveProfile

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RapidForcing_SyntaxComputable
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Encodable
open scoped BigOperators
namespace RapidForcing.EffectiveArithmetic
lemma computable_list_map {A B C : Type} [Primcodable A] [Primcodable B] [Primcodable C]
    {f : A → List B} {g : A → B → C} (hf : Computable f) (hg : Computable₂ g) :
    Computable (fun a => (f a).map (g a)) := by
  have h := computable_list_foldr hf (Computable.const ([] : List C))
    (h := fun a p => g a p.1 :: p.2)
    ((Computable.list_cons.comp (hg.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).to₂)
  exact h.of_eq (fun a => by induction f a <;> simp [*])
end RapidForcing.EffectiveArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RapidForcing_BoundsPrograms
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Encodable
open scoped BigOperators
namespace RapidForcing.EffectiveArithmetic

lemma computable_list_sum {S : Type} [Primcodable S] [AddMonoid S]
    (hadd : Computable (fun p : S × S => p.1 + p.2)) :
    Computable (List.sum : List S → S) := by
  have h := computable_list_foldr Computable.id (Computable.const (0 : S))
    (hadd.comp Computable.snd).to₂
  exact h.of_eq (fun _ => rfl)

end RapidForcing.EffectiveArithmetic

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_RelaxedCandidates
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators Classical

abbrev DeletionCandidate (n : ℕ) := Fin n → Option Bool
abbrev SignedLiteral (n : ℕ) := Fin n × Bool

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ClauseClasses
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open scoped Classical

abbrev Triple (A : Type*) := A × A × A

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ActiveClauses
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open scoped Classical

abbrev IncidentClass (n : ℕ) :=
  (Fin 3 × SignedLiteral n × SignedLiteral n) ⊕ (Fin 3 × SignedLiteral n) ⊕ Unit
abbrev ActiveClause (n : ℕ) := Triple (SignedLiteral n) ⊕ Bool × IncidentClass n

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_EffectiveLog
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PeriodicLattice.CertifiedReal

open Encodable Filter
open scoped Topology
local instance effectiveLogRatPrimcodable : Primcodable ℚ := RecursiveArithmetic.ratPrimcodable

section
variable {A : Type*} [Primcodable A]

def logLower (z : ℕ) : ℚ := (decode z.unpair.1).getD 0
def logUpper (z : ℕ) : ℚ := (decode z.unpair.2.unpair.1).getD 0
def logAccuracy (z : ℕ) : ℕ := z.unpair.2.unpair.2

@[fun_prop] theorem logLower_computable : Computable logLower := by
  unfold logLower
  fun_prop
@[fun_prop] theorem logUpper_computable : Computable logUpper := by
  unfold logUpper
  fun_prop
@[fun_prop] theorem logAccuracy_computable : Computable logAccuracy := by
  unfold logAccuracy
  fun_prop

abbrev logTest (q : A × ℕ → ℚ) (e : ℚ × ℕ → ℚ) (an : A × ℕ) (z : ℕ) : Prop :=
  logUpper z - logLower z ≤ 2*qerror an.2 ∧
  e (logLower z, logAccuracy z) + 2*qerror (logAccuracy z) < q (an.1, logAccuracy z) ∧
  q (an.1, logAccuracy z) + 2*qerror (logAccuracy z) < e (logUpper z, logAccuracy z)

instance logTest_decidable (q : A × ℕ → ℚ) (e : ℚ × ℕ → ℚ) (an : A × ℕ) (z : ℕ) :
    Decidable (logTest q e an z) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem logTest_computable {q : A × ℕ → ℚ} {e : ℚ × ℕ → ℚ}
    (hq : Computable q) (he : Computable e) :
    Computable (fun p : (A × ℕ) × ℕ => decide (logTest q e p.1 p.2)) := by
  unfold logTest
  simp only [Bool.decide_and]
  apply Primrec.and.to_comp.comp
  · exact RecursiveArithmetic.ratLE.decide.to_comp.comp (by fun_prop) (by fun_prop)
  · apply Primrec.and.to_comp.comp
    · exact RecursiveArithmetic.ratLT.decide.to_comp.comp (by fun_prop) (by fun_prop)
    · exact RecursiveArithmetic.ratLT.decide.to_comp.comp (by fun_prop) (by fun_prop)

omit [Primcodable A] in
theorem logTest_exists {f : A → ℝ} (q : A × ℕ → ℚ) (e : ℚ × ℕ → ℚ)
    (eq : ∀ a n, |f a - (q (a,n) : ℝ)| ≤ error n)
    (ee : ∀ (a : ℚ) n, |Real.exp (a : ℝ) - (e (a,n) : ℝ)| ≤ error n)
    (hpos : ∀ a, 0 < f a) (an : A × ℕ) : ∃ z, logTest q e an z := by
  obtain ⟨l, hl, hl'⟩ := exists_rat_btwn
    (show Real.log (f an.1) - error an.2 < Real.log (f an.1) by linarith [error_pos an.2])
  obtain ⟨u, hu, hu'⟩ := exists_rat_btwn
    (show Real.log (f an.1) < Real.log (f an.1) + error an.2 by linarith [error_pos an.2])
  have hlExp : Real.exp (l : ℝ) < f an.1 := by
    rw [← Real.exp_log (hpos an.1)]
    exact Real.exp_lt_exp.mpr hl'
  have huExp : f an.1 < Real.exp (u : ℝ) := by
    rw [← Real.exp_log (hpos an.1)]
    exact Real.exp_lt_exp.mpr hu
  have tq := Effective.approximants_tendsto eq an.1
  have tl := Effective.approximants_tendsto ee l
  have tu := Effective.approximants_tendsto ee u
  have tl' := (tl.add (error_tendsto.const_mul 2)).eventually_lt tq
    (by simpa using hlExp)
  have tu' := (tq.add (error_tendsto.const_mul 2)).eventually_lt tu
    (by simpa using huExp)
  obtain ⟨s, hs, hs'⟩ := (tl'.and tu').exists
  refine ⟨Nat.pair (encode l) (Nat.pair (encode u) s), ?_⟩
  have hw : u-l ≤ 2*qerror an.2 := by
    have : (u : ℝ)-(l : ℝ) ≤ 2*error an.2 := by linarith
    exact_mod_cast (show (u : ℝ)-(l : ℝ) ≤ 2*(qerror an.2 : ℝ) by simpa using this)
  have hsl : e (l,s)+2*qerror s < q (an.1,s) := by
    exact_mod_cast (show (e (l,s) : ℝ)+2*(qerror s : ℝ) < (q (an.1,s) : ℝ) by simpa using hs)
  have hsu : q (an.1,s)+2*qerror s < e (u,s) := by
    exact_mod_cast (show (q (an.1,s) : ℝ)+2*(qerror s : ℝ) < (e (u,s) : ℝ) by simpa using hs')
  simpa only [logTest, logLower, logUpper, logAccuracy, Nat.unpair_pair, encodek, Option.getD_some]
    using And.intro hw (And.intro hsl hsu)

omit [Primcodable A] in
theorem logTest_sound {f : A → ℝ} (q : A × ℕ → ℚ) (e : ℚ × ℕ → ℚ)
    (eq : ∀ a n, |f a - (q (a,n) : ℝ)| ≤ error n)
    (ee : ∀ (a : ℚ) n, |Real.exp (a : ℝ) - (e (a,n) : ℝ)| ≤ error n)
    (hpos : ∀ a, 0 < f a) (a : A) (n z : ℕ) (hs : logTest q e (a,n) z) :
    |Real.log (f a) - (((logLower z+logUpper z)/2 : ℚ) : ℝ)| ≤ error n := by
  obtain ⟨hw, hl, hu⟩ := hs
  have el := ee (logLower z) (logAccuracy z)
  have eu := ee (logUpper z) (logAccuracy z)
  have ef := eq a (logAccuracy z)
  have hlr : (e (logLower z,logAccuracy z) : ℝ)+2*error (logAccuracy z) < q (a,logAccuracy z) := by
    simpa only [cast_qerror] using (show (e (logLower z,logAccuracy z) : ℝ)+2*(qerror (logAccuracy z) : ℝ) <
      (q (a,logAccuracy z) : ℝ) by exact_mod_cast hl)
  have hur : (q (a,logAccuracy z) : ℝ)+2*error (logAccuracy z) < e (logUpper z,logAccuracy z) := by
    simpa only [cast_qerror] using (show (q (a,logAccuracy z) : ℝ)+2*(qerror (logAccuracy z) : ℝ) <
      (e (logUpper z,logAccuracy z) : ℝ) by exact_mod_cast hu)
  have hlo : Real.exp (logLower z : ℝ) < f a := by
    have h1 := (abs_le.mp el).2
    have h2 := (abs_le.mp ef).1
    linarith
  have hhi : f a < Real.exp (logUpper z : ℝ) := by
    have h1 := (abs_le.mp eu).1
    have h2 := (abs_le.mp ef).2
    linarith
  have hloglo : (logLower z : ℝ) < Real.log (f a) := by
    rw [← Real.exp_log (hpos a)] at hlo
    exact Real.exp_lt_exp.mp hlo
  have hloghi : Real.log (f a) < (logUpper z : ℝ) := by
    rw [← Real.exp_log (hpos a)] at hhi
    exact Real.exp_lt_exp.mp hhi
  have hwidth : (logUpper z : ℝ)-(logLower z : ℝ) ≤ 2*error n := by
    simpa only [cast_qerror] using
      (show (logUpper z : ℝ)-(logLower z : ℝ) ≤ 2*(qerror n : ℝ) by exact_mod_cast hw)
  change |Real.log (f a) - (((logLower z+logUpper z)/2 : ℚ) : ℝ)| ≤ error n
  push_cast
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem Effective.log {f : A → ℝ} (hf : Effective f) (hpos : ∀ a, 0 < f a) :
    Effective (fun a => Real.log (f a)) := by
  obtain ⟨q, hq, eq⟩ := hf
  obtain ⟨e, he, ee⟩ := (rational (Computable.id : Computable (id : ℚ → ℚ))).exp
  change ∀ (a : ℚ) (n : ℕ), |Real.exp (a : ℝ) - (e (a,n) : ℝ)| ≤ error n at ee
  have hex := logTest_exists q e eq ee hpos
  let pick (an : A × ℕ) := Nat.find (hex an)
  have hpick : Computable pick := computable_find (logTest_computable hq he) hex
  refine ⟨fun an => (logLower (pick an)+logUpper (pick an))/2, by fun_prop, ?_⟩
  intro a n
  exact logTest_sound q e eq ee hpos a n (pick (a,n)) (Nat.find_spec (hex (a,n)))

end
end PeriodicLattice.CertifiedReal

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ArithmeticEnclosures
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability.FiniteArithmetic

open Filter RapidForcing.EffectiveProfile RapidForcing.EffectiveArithmetic
open PeriodicLattice.CertifiedReal
open scoped Topology
local instance arithmeticEnclosuresRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable

@[fun_prop] theorem rat_max_computable : Computable (fun p : ℚ × ℚ => max p.1 p.2) := by
  simpa only [max_def] using
    (show Computable (fun p : ℚ × ℚ => if p.1 ≤ p.2 then p.2 else p.1) by fun_prop)

theorem exp_effective : Effective (fun q : ℚ => Real.exp (q : ℝ)) :=
  (rational (Computable.id : Computable (id : ℚ → ℚ))).exp

theorem log_effective : Effective (fun q : ℚ => Real.log (max 1 (q : ℝ))) := by
  have he : Effective (fun q : ℚ => ((max 1 q : ℚ) : ℝ)) :=
    rational (show Computable (fun q : ℚ => max 1 q) by fun_prop)
  simpa only [Rat.cast_max, Rat.cast_one] using he.log
    (fun q => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (by exact_mod_cast le_max_left (1 : ℚ) q))

noncomputable def expApprox : ℚ × ℕ → ℚ := Classical.choose exp_effective
noncomputable def logApprox : ℚ × ℕ → ℚ := Classical.choose log_effective

@[fun_prop] theorem expApprox_computable : Computable expApprox := (Classical.choose_spec exp_effective).1
@[fun_prop] theorem logApprox_computable : Computable logApprox := (Classical.choose_spec log_effective).1

theorem expApprox_error (q : ℚ) (n : ℕ) :
    |Real.exp (q : ℝ) - (expApprox (q,n) : ℝ)| ≤ error n :=
  (Classical.choose_spec exp_effective).2 q n

theorem logApprox_error (q : ℚ) (n : ℕ) :
    |Real.log (max 1 (q : ℝ)) - (logApprox (q,n) : ℝ)| ≤ error n :=
  (Classical.choose_spec log_effective).2 q n

noncomputable def interval (l u : ℚ) : Ball := ⟨(l+u)/2, (u-l)/2⟩

@[fun_prop] theorem interval_computable : Computable (fun p : ℚ × ℚ => interval p.1 p.2) := by
  unfold interval
  fun_prop

theorem interval_covers {l u : ℚ} {x : ℝ} (hl : (l : ℝ) ≤ x) (hu : x ≤ (u : ℝ)) :
    (interval l u).Covers x := by
  unfold interval Ball.Covers
  push_cast
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem approximate_tendsto {f : ℚ → ℝ} {a : ℚ × ℕ → ℚ}
    (ha : ∀ q n, |f q - (a (q,n) : ℝ)| ≤ error n)
    {q : ℕ → ℚ} {x : ℝ} (hq : Tendsto (fun n => f (q n)) atTop (nhds x)) :
    Tendsto (fun n => (a (q n,n) : ℝ)) atTop (nhds x) := by
  have hz : Tendsto (fun n => (a (q n,n) : ℝ)-f (q n)) atTop (nhds 0) := by
    apply squeeze_zero_norm (fun n => ?_) error_tendsto
    simpa only [Real.norm_eq_abs, abs_sub_comm] using ha (q n) n
  simpa only [sub_add_cancel, zero_add] using hz.add hq

noncomputable def expBall (b : Ball) (n : ℕ) : Ball :=
  interval (expApprox (b.center-b.radius,n)-qerror n)
    (expApprox (b.center+b.radius,n)+qerror n)

noncomputable def logBall (b : Ball) (n : ℕ) : Ball :=
  interval (logApprox (b.center-b.radius,n)-qerror n)
    (logApprox (b.center+b.radius,n)+qerror n)

@[fun_prop] theorem expBall_computable : Computable (fun p : Ball × ℕ => expBall p.1 p.2) := by
  unfold expBall
  fun_prop
@[fun_prop] theorem logBall_computable : Computable (fun p : Ball × ℕ => logBall p.1 p.2) := by
  unfold logBall
  fun_prop

theorem expBall_covers {b : Ball} {x : ℝ} (hb : b.Covers x) (n : ℕ) :
    (expBall b n).Covers (Real.exp x) := by
  have he := abs_le.mp hb
  have hl := (abs_le.mp (expApprox_error (b.center-b.radius) n)).1
  have hu := (abs_le.mp (expApprox_error (b.center+b.radius) n)).2
  apply interval_covers
  · push_cast
    have := Real.exp_le_exp.mpr (show (b.center : ℝ)-b.radius ≤ x by linarith)
    simp only [Rat.cast_sub, cast_qerror] at hl ⊢
    linarith
  · push_cast
    have := Real.exp_le_exp.mpr (show x ≤ (b.center : ℝ)+b.radius by linarith)
    simp only [Rat.cast_add, cast_qerror] at hu ⊢
    linarith

theorem logBall_covers {b : Ball} {x : ℝ} (hb : b.Covers x) (n : ℕ) :
    (logBall b n).Covers (Real.log (max 1 x)) := by
  have he := abs_le.mp hb
  have hl := (abs_le.mp (logApprox_error (b.center-b.radius) n)).1
  have hu := (abs_le.mp (logApprox_error (b.center+b.radius) n)).2
  have hp (y : ℝ) : 0 < max 1 y := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  apply interval_covers
  · push_cast
    have := Real.log_le_log (hp ((b.center : ℝ)-b.radius))
      (max_le_max_left 1 (show (b.center : ℝ)-b.radius ≤ x by linarith))
    simp only [Rat.cast_sub, cast_qerror] at hl ⊢
    linarith
  · push_cast
    have := Real.log_le_log (hp x)
      (max_le_max_left 1 (show x ≤ (b.center : ℝ)+b.radius by linarith))
    simp only [Rat.cast_add, cast_qerror] at hu ⊢
    linarith

theorem Encloses.exp {b : ℕ → Ball} {x : ℝ} (hb : Encloses b x) :
    Encloses (fun n => expBall (b n) n) (Real.exp x) := by
  have hbl : Tendsto (fun n => (((b n).center-(b n).radius : ℚ) : ℝ)) atTop (nhds x) := by
    simpa only [Rat.cast_sub, sub_zero] using hb.centers.sub hb.2
  have hbu : Tendsto (fun n => (((b n).center+(b n).radius : ℚ) : ℝ)) atTop (nhds x) := by
    simpa only [Rat.cast_add, add_zero] using hb.centers.add hb.2
  have hl := approximate_tendsto expApprox_error
    (q := fun n => (b n).center-(b n).radius) (Real.continuous_exp.tendsto x |>.comp hbl)
  have hu := approximate_tendsto expApprox_error
    (q := fun n => (b n).center+(b n).radius) (Real.continuous_exp.tendsto x |>.comp hbu)
  refine ⟨fun n => expBall_covers (hb.1 n) n, ?_⟩
  have hlim := ((hu.add error_tendsto).sub (hl.sub error_tendsto)).div_const 2
  simpa only [expBall, interval, Rat.cast_div, Rat.cast_sub, Rat.cast_add,
    Rat.cast_ofNat, cast_qerror, add_zero, sub_zero, sub_self, zero_div] using hlim

theorem Encloses.log {b : ℕ → Ball} {x : ℝ} (hb : Encloses b x) :
    Encloses (fun n => logBall (b n) n) (Real.log (max 1 x)) := by
  have hp : max (1 : ℝ) x ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  have hbl : Tendsto (fun n => (((b n).center-(b n).radius : ℚ) : ℝ)) atTop (nhds x) := by
    simpa only [Rat.cast_sub, sub_zero] using hb.centers.sub hb.2
  have hbu : Tendsto (fun n => (((b n).center+(b n).radius : ℚ) : ℝ)) atTop (nhds x) := by
    simpa only [Rat.cast_add, add_zero] using hb.centers.add hb.2
  have hl := approximate_tendsto logApprox_error
    (q := fun n => (b n).center-(b n).radius) ((tendsto_const_nhds.max hbl).log hp)
  have hu := approximate_tendsto logApprox_error
    (q := fun n => (b n).center+(b n).radius) ((tendsto_const_nhds.max hbu).log hp)
  refine ⟨fun n => logBall_covers (hb.1 n) n, ?_⟩
  have hlim := ((hu.add error_tendsto).sub (hl.sub error_tendsto)).div_const 2
  simpa only [logBall, interval, Rat.cast_div, Rat.cast_sub, Rat.cast_add,
    Rat.cast_ofNat, cast_qerror, add_zero, sub_zero, sub_self, zero_div] using hlim

end FixedClauseThreshold.Computability.FiniteArithmetic

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ArithmeticSyntax
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability.FiniteArithmetic

open Encodable Nat.Partrec RapidForcing.EffectiveProfile RapidForcing.EffectiveArithmetic
open PeriodicLattice.CertifiedReal Filter
open scoped Topology
local instance arithmeticSyntaxRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable
local instance arithmeticSyntaxCodeEq : DecidableEq Code := Encodable.decidableEqOfEncodable Code

noncomputable def clampBall (b : Ball) : Ball := ⟨max 1 b.center, b.radius⟩

@[fun_prop] theorem clampBall_computable : Computable clampBall := by
  unfold clampBall
  fun_prop

theorem clampBall_covers {b : Ball} {x : ℝ} (hb : b.Covers x) :
    (clampBall b).Covers (max 1 x) := by
  have h := abs_max_sub_max_le_abs (b.center : ℝ) x 1
  simpa only [clampBall, Ball.Covers, Rat.cast_max, Rat.cast_one, max_comm] using h.trans hb

theorem encloses_clamp {b : ℕ → Ball} {x : ℝ} (hb : Encloses b x) :
    Encloses (fun n => clampBall (b n)) (max 1 x) :=
  ⟨fun n => clampBall_covers (hb.1 n), hb.2⟩

noncomputable def decodedRational (e : Code) : ℚ := (decode (encode e)).getD 0

@[fun_prop] theorem decodedRational_computable : Computable decodedRational := by
  unfold decodedRational
  fun_prop

noncomputable def expressionValue : Code → ℝ
  | .zero => 0
  | .succ => 1
  | .left => 2
  | .right => 3
  | .pair a b => expressionValue a + expressionValue b
  | .comp a b => expressionValue a * expressionValue b
  | .prec tag b => if tag = .zero then (decodedRational b : ℝ)
      else if tag = .succ then Real.exp (expressionValue b)
      else if tag = .left then Real.log (max 1 (expressionValue b))
      else (max 1 (expressionValue b))⁻¹
  | .rfind' a => -expressionValue a

noncomputable def expressionBall : Code → ℕ → Ball
  | .zero, _ => Ball.exact 0
  | .succ, _ => Ball.exact 1
  | .left, _ => Ball.exact 2
  | .right, _ => Ball.exact 3
  | .pair a b, n => (expressionBall a n).add (expressionBall b n)
  | .comp a b, n => (expressionBall a n).mul (expressionBall b n)
  | .prec tag b, n => if tag = .zero then Ball.exact (decodedRational b)
      else if tag = .succ then expBall (expressionBall b n) n
      else if tag = .left then logBall (expressionBall b n) n
      else (clampBall (expressionBall b n)).denInv
  | .rfind' a, n => (Ball.exact (-1)).mul (expressionBall a n)

@[fun_prop] theorem expressionBall_computable :
    Computable (fun p : Code × ℕ => expressionBall p.1 p.2) := by
  have h := Code.computable_recOn (c := fun p : Code × ℕ => p.1) Computable.fst
    (z := fun _ => Ball.exact 0) (by fun_prop)
    (s := fun _ => Ball.exact 1) (by fun_prop)
    (l := fun _ => Ball.exact 2) (by fun_prop)
    (r := fun _ => Ball.exact 3) (by fun_prop)
    (pr := fun _ p => p.2.2.1.add p.2.2.2) (by unfold Computable₂; fun_prop)
    (co := fun _ p => p.2.2.1.mul p.2.2.2) (by unfold Computable₂; fun_prop)
    (pc := fun x p => if p.1 = .zero then Ball.exact (decodedRational p.2.1)
      else if p.1 = .succ then expBall p.2.2.2 x.2
      else if p.1 = .left then logBall p.2.2.2 x.2
      else (clampBall p.2.2.2).denInv) (by unfold Computable₂; fun_prop)
    (rf := fun _ p => (Ball.exact (-1)).mul p.2) (by unfold Computable₂; fun_prop)
  apply h.of_eq
  intro p
  induction p.1 <;> simp_all only [expressionBall]

theorem expressionBall_encloses (e : Code) : Encloses (expressionBall e) (expressionValue e) := by
  induction e with
  | zero => simpa only [expressionBall, expressionValue, Rat.cast_zero] using encloses_exact 0
  | succ => simpa only [expressionBall, expressionValue, Rat.cast_one] using encloses_exact 1
  | left => exact encloses_exact 2
  | right => exact encloses_exact 3
  | pair a b ha hb => exact ha.add hb
  | comp a b ha hb => exact ha.mul hb
  | prec tag b _ hb =>
    by_cases hz : tag = .zero
    · simpa only [expressionBall, expressionValue, hz, ite_true] using encloses_exact (decodedRational b)
    · by_cases he : tag = .succ
      · simpa [expressionBall, expressionValue, he] using Encloses.exp hb
      · by_cases hl : tag = .left
        · simpa [expressionBall, expressionValue, hl] using Encloses.log hb
        · simpa only [expressionBall, expressionValue, hz, he, hl, ite_false] using
            (encloses_clamp hb).denInv (show (1/16 : ℝ) ≤ max 1 (expressionValue b) from
              (by norm_num : (1/16 : ℝ) ≤ 1).trans (le_max_left _ _))
  | rfind' a ha =>
    simpa only [expressionBall, expressionValue, Rat.cast_neg, Rat.cast_one, neg_one_mul] using
      (encloses_exact (-1)).mul ha

end FixedClauseThreshold.Computability.FiniteArithmetic

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_ArithmeticConstructors
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability.FiniteArithmetic

open Encodable Denumerable Nat.Partrec
open scoped BigOperators
local instance arithmeticConstructorsRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable

noncomputable def rationalExpression (q : ℚ) : Code :=
  .prec .zero (ofNat Code (encode q))

@[fun_prop] theorem rationalExpression_computable : Computable rationalExpression := by
  have : Computable (ofNat Code) := (Primrec.ofNat Code).to_comp
  unfold rationalExpression
  fun_prop

@[simp] theorem rationalExpression_value (q : ℚ) :
    expressionValue (rationalExpression q) = q := by
  simp only [rationalExpression, expressionValue, ite_true, decodedRational,
    encode_ofNat, encodek, Option.getD_some]

def exponentialExpression (e : Code) : Code := .prec .succ e
def positiveLogExpression (e : Code) : Code := .prec .left e

@[simp] theorem exponentialExpression_value (e : Code) :
    expressionValue (exponentialExpression e) = Real.exp (expressionValue e) := by
  simp [exponentialExpression, expressionValue]
@[simp] theorem positiveLogExpression_value (e : Code) :
    expressionValue (positiveLogExpression e) = Real.log (max 1 (expressionValue e)) := by
  simp [positiveLogExpression, expressionValue]

noncomputable def scaledLogExpression (q : ℚ) (e : Code) : Code :=
  .pair (.rfind' (positiveLogExpression (rationalExpression q⁻¹)))
    (positiveLogExpression (.comp (rationalExpression q⁻¹) e))

theorem scaledLogExpression_value {q : ℚ} {e : Code}
    (hq : 0 < q) (hq1 : q ≤ 1) (he : (q : ℝ) ≤ expressionValue e) :
    expressionValue (scaledLogExpression q e) = Real.log (expressionValue e) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1' : (q : ℝ) ≤ 1 := by exact_mod_cast hq1
  have hi : (1 : ℝ) ≤ (q : ℝ)⁻¹ := (one_le_inv₀ hq').mpr hq1'
  have he' : (1 : ℝ) ≤ (q : ℝ)⁻¹ * expressionValue e := by
    calc
      1 = (q : ℝ)⁻¹ * q := (inv_mul_cancel₀ hq'.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hq'.le)
  simp only [scaledLogExpression, expressionValue, positiveLogExpression_value,
    rationalExpression_value, Rat.cast_inv, max_eq_right hi, max_eq_right he']
  rw [Real.log_mul (inv_ne_zero hq'.ne') (ne_of_gt (hq'.trans_le he))]
  ring

def sumExpressions (es : List Code) : Code := es.foldr Code.pair .zero

@[fun_prop] theorem sumExpressions_computable : Computable sumExpressions := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const Code.zero)
    ((Code.primrec₂_pair.comp Primrec.fst Primrec.snd).comp Primrec.snd).to₂).to_comp

@[simp] theorem sumExpressions_value (es : List Code) :
    expressionValue (sumExpressions es) = (es.map expressionValue).sum := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa only [sumExpressions, List.foldr_cons, expressionValue,
      List.map_cons, List.sum_cons] using congrArg (expressionValue e + ·) ih

end FixedClauseThreshold.Computability.FiniteArithmetic

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_WeightedExpressions
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability.FiniteArithmetic

open Nat.Partrec RapidForcing.EffectiveArithmetic RapidForcing.EffectiveProfile
local instance weightedExpressionsRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable

theorem rational_abs_le_num (q : ℚ) : |(q : ℝ)| ≤ (q.num.natAbs : ℝ) := by
  have hd : (1 : ℝ) ≤ q.den := by exact_mod_cast q.pos
  have he : (q : ℝ) = (q.num : ℝ) / q.den := by
    conv_lhs => rw [← Rat.num_div_den q]
    push_cast
    rfl
  rw [he, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ q.den)]
  calc
    |(q.num : ℝ)| / q.den ≤ |(q.num : ℝ)| :=
      div_le_self (abs_nonneg _) hd
    _ = (q.num.natAbs : ℝ) := by simp

noncomputable def expressionBound (e : Code) : ℕ :=
  (expressionBall e 0).center.num.natAbs + (expressionBall e 0).radius.num.natAbs

attribute [local irreducible] expressionBall

@[fun_prop] theorem expressionBound_computable : Computable expressionBound := by
  have hb : Computable (fun e : Code => expressionBall e 0) :=
    Computable.comp (f := fun p : Code × ℕ => expressionBall p.1 p.2)
      (g := fun e : Code => (e, (0 : ℕ))) expressionBall_computable
      (Computable.id.pair (Computable.const 0))
  have hf : Computable (fun b : Ball => b.center.num.natAbs + b.radius.num.natAbs) := by
    fun_prop
  exact hf.comp hb

theorem expressionBound_valid (e : Code) : |expressionValue e| ≤ expressionBound e := by
  have h := (expressionBall_encloses e).1 0
  have hr := rational_abs_le_num (expressionBall e 0).radius
  have hc := rational_abs_le_num (expressionBall e 0).center
  have hrad : ((expressionBall e 0).radius : ℝ) ≤
      |((expressionBall e 0).radius : ℝ)| := le_abs_self _
  change _ ≤ (((expressionBall e 0).center.num.natAbs +
    (expressionBall e 0).radius.num.natAbs : ℕ) : ℝ)
  push_cast
  have ht := abs_add_le (expressionValue e - ((expressionBall e 0).center : ℝ))
    ((expressionBall e 0).center : ℝ)
  rw [sub_add_cancel] at ht
  have h' : |expressionValue e - ((expressionBall e 0).center : ℝ)| ≤
      ((expressionBall e 0).radius : ℝ) := by simpa only [Ball.Covers, abs_sub_comm] using h
  linarith

noncomputable def mixtureBound (bs : List (ℚ × Code)) : ℕ :=
  (bs.map (fun b => expressionBound b.2)).sum

noncomputable def mixtureExpression (bs : List (ℚ × Code)) : Code :=
  sumExpressions (bs.map (fun b => .comp (rationalExpression b.1) (exponentialExpression b.2)))

noncomputable def logMixtureExpression (bs : List (ℚ × Code)) : Code :=
  scaledLogExpression ((3 : ℚ)^mixtureBound bs)⁻¹ (mixtureExpression bs)

@[fun_prop] theorem mixtureBound_computable : Computable mixtureBound := by
  unfold mixtureBound
  apply (computable_list_sum (by fun_prop : Computable (fun p : ℕ × ℕ => p.1+p.2))).comp
  apply computable_list_map Computable.id
  unfold Computable₂
  fun_prop

@[fun_prop] theorem mixtureExpression_computable : Computable mixtureExpression := by
  unfold mixtureExpression
  apply sumExpressions_computable.comp
  apply computable_list_map Computable.id
  unfold Computable₂
  unfold exponentialExpression
  fun_prop

@[fun_prop] theorem logMixtureExpression_computable : Computable logMixtureExpression := by
  unfold logMixtureExpression scaledLogExpression positiveLogExpression
  fun_prop

theorem mixtureExpression_value (bs : List (ℚ × Code)) :
    expressionValue (mixtureExpression bs) =
      (bs.map (fun b => (b.1 : ℝ)*Real.exp (expressionValue b.2))).sum := by
  simp only [mixtureExpression, sumExpressions_value, List.map_map, Function.comp_def,
    expressionValue, rationalExpression_value, exponentialExpression_value]

theorem small_exp_lower (N : ℕ) :
    ((3 : ℝ)^N)⁻¹ ≤ Real.exp (-(N : ℝ)) := by
  rw [Real.exp_neg, show Real.exp (N : ℝ) = (Real.exp 1)^N by
    rw [← Real.exp_nat_mul]; simp]
  apply inv_anti₀ (pow_pos (Real.exp_pos 1) N)
  exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le N

theorem logMixtureExpression_value (bs : List (ℚ × Code))
    (hw : ∀ b ∈ bs, 0 ≤ b.1) (hs : (bs.map Prod.fst).sum = 1) :
    expressionValue (logMixtureExpression bs) =
      Real.log ((bs.map (fun b => (b.1 : ℝ)*Real.exp (expressionValue b.2))).sum) := by
  have hB (b : ℚ × Code) (hb : b ∈ bs) :
      -(mixtureBound bs : ℝ) ≤ expressionValue b.2 := by
    have hle : expressionBound b.2 ≤ mixtureBound bs :=
      List.single_le_sum (fun (x : ℕ) _ => Nat.zero_le x) _
        (List.mem_map.mpr ⟨b, hb, rfl⟩)
    have hcast : (expressionBound b.2 : ℝ) ≤ mixtureBound bs := by exact_mod_cast hle
    have he := (abs_le.mp (expressionBound_valid b.2)).1
    linarith
  have hsum : (bs.map (fun b => (b.1 : ℝ))).sum = 1 := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) hs
    simpa only [Rat.cast_one, Rat.cast_list_sum, List.map_map, Function.comp_def] using h
  have he : ((3 : ℝ)^mixtureBound bs)⁻¹ ≤
      (bs.map (fun b => (b.1 : ℝ)*Real.exp (expressionValue b.2))).sum := by
    calc
      _ = (bs.map (fun b => (b.1 : ℝ)*((3 : ℝ)^mixtureBound bs)⁻¹)).sum := by
        rw [List.sum_map_mul_right, hsum, one_mul]
      _ ≤ _ := by
        apply List.sum_le_sum
        intro b hb
        exact mul_le_mul_of_nonneg_left
          ((small_exp_lower _).trans (Real.exp_le_exp.mpr (hB b hb)))
          (by exact_mod_cast hw b hb)
  unfold logMixtureExpression
  rw [scaledLogExpression_value, mixtureExpression_value]
  · positivity
  · exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  · simpa only [Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat, mixtureExpression_value] using he

end FixedClauseThreshold.Computability.FiniteArithmetic

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_PhysicalExpressions
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability.FiniteArithmetic

open Nat.Partrec DilutedSpinGlass RapidForcing.EffectiveArithmetic
open scoped BigOperators
local instance physicalExpressionsRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable

noncomputable def logTwoExpression : Code := positiveLogExpression .left

theorem logTwoExpression_value : expressionValue logTwoExpression = Real.log 2 := by
  norm_num [logTwoExpression, positiveLogExpression_value, expressionValue]

noncomputable def binaryLogMeanExpression (x y : Code) : Code :=
  logMixtureExpression [(1/2, x), (1/2, y)]

noncomputable def binaryLogSumExpression (x y : Code) : Code :=
  .pair logTwoExpression (binaryLogMeanExpression x y)

@[fun_prop] theorem binaryLogMeanExpression_computable :
    Computable (fun p : Code × Code => binaryLogMeanExpression p.1 p.2) := by
  unfold binaryLogMeanExpression
  fun_prop

@[fun_prop] theorem binaryLogSumExpression_computable :
    Computable (fun p : Code × Code => binaryLogSumExpression p.1 p.2) := by
  unfold binaryLogSumExpression
  fun_prop

theorem binaryLogMeanExpression_value (x y : Code) :
    expressionValue (binaryLogMeanExpression x y) =
      Real.log ((Real.exp (expressionValue x)+Real.exp (expressionValue y))/2) := by
  rw [binaryLogMeanExpression, logMixtureExpression_value]
  · congr 1
    norm_num
    ring
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> norm_num
  · norm_num

theorem binaryLogSumExpression_value (x y : Code) :
    expressionValue (binaryLogSumExpression x y) =
      Real.log (Real.exp (expressionValue x)+Real.exp (expressionValue y)) := by
  rw [binaryLogSumExpression, expressionValue, logTwoExpression_value,
    binaryLogMeanExpression_value, Real.log_div (by positivity) (by norm_num)]
  ring

def signedExpression (x : Code) (b : Bool) : Code := if b then x else .rfind' x

@[fun_prop] theorem signedExpression_computable :
    Computable (fun p : Code × Bool => signedExpression p.1 p.2) := by
  unfold signedExpression
  fun_prop

noncomputable def logQExpression (x : Code) (b : Bool) : Code :=
  .pair (signedExpression x b) (.rfind' (binaryLogSumExpression (.rfind' x) x))

end FixedClauseThreshold.Computability.FiniteArithmetic

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_CavityExpressions
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability.FiniteArithmetic

open Nat.Partrec DilutedSpinGlass RapidForcing.EffectiveArithmetic
open scoped BigOperators
local instance cavityExpressionsRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable

theorem appendSpin_three (a b ε : Bool) :
    appendSpin (p := 3) ![a,b] ε = ![a,b,ε] := by
  funext i
  fin_cases i <;> rfl

abbrev SiteExpressionDatum := (Fin 3 → Bool) × (Fin 2 → Code)

end FixedClauseThreshold.Computability.FiniteArithmetic

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_HierarchyTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Nat.Partrec Encodable Denumerable FiniteArithmetic
open RapidForcing.EffectiveArithmetic

abbrev ExpressionTable := List (List Code × Code)

end FixedClauseThreshold.Computability

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_IncidentObstruction
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

abbrev BadIncident (n : ℕ) := (Fin 3 × SignedLiteral n) ⊕ Unit

end FixedClauseThreshold.Computability

end OAI
end


