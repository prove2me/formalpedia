-- Prove2me | Definitions.Def_OAIQ093D008
-- name    : OAIQ093D008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T16:04:02.865596+00:00
-- url     : https://prove2.me/theorems/713c681c-df6e-4844-b5cf-d0d02cc24dff
-- title:
--   Definitions bundle OAIQ093D008 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 176 declarations of OpenAI's Lean: 61 definitions, 2 inductive types or structures, 2 instances and 111 theorems. The definitions and types are `OAI.PolycyclicRecognition.CartanWordModel.coneIdealWordCost`, `OAI.PolycyclicRecognition.CartanWordModel.coneMixedWords`, `OAI.PolycyclicRecognition.CartanWordModel.coneOriginalWord`, `OAI.PolycyclicRecognition.CartanWordModel.directionalVisitPath`, `OAI.PolycyclicRecognition.CartanWordModel.heightConePreimage`, `OAI.PolycyclicRecognition.CartanWordModel.innerHaarNormedAddCommGroup`, `OAI.PolycyclicRecognition.CartanWordModel.innerHaarNormedSpace`, `OAI.PolycyclicRecognition.CartanWordModel.instNormedAddCommGroupSubtypeMemLieIdealRealCartanRootIdeal`, `OAI.PolycyclicRecognition.CartanWordModel.instNormedSpaceRealSubtypeMemLieIdealCartanRootIdeal`, `OAI.PolycyclicRecognition.CartanWordModel.kernelHaarNormedAddCommGroup`, `OAI.PolycyclicRecognition.CartanWordModel.kernelHaarNormedSpace`, `OAI.PolycyclicRecognition.CartanWordModel.positiveHeightConePreimage`, `OAI.PolycyclicRecognition.CartanWordModel.sampledDirectionalVisitPath`, `OAI.PolycyclicRecognition.CartanWordModel.segmentScaledWord`, `OAI.PolycyclicRecognition.CartanWordModel.segmentSupportDirection`, `OAI.PolycyclicRecognition.CartanWordModel.segmentSupportExponent`, `OAI.PolycyclicRecognition.CartanWordModel.segmentVisitPath`, `OAI.PolycyclicRecognition.CartanWordModel.segmentWordPath`, `OAI.PolycyclicRecognition.CartanWordModel.templateScaledWord`, `OAI.PolycyclicRecognition.CartanWordModel.templateSupportExponent`, `OAI.PolycyclicRecognition.CartanWordModel.templateVisitPath`, `OAI.PolycyclicRecognition.CartanWordModel.templateWordPath`, `OAI.PolycyclicRecognition.CartanWordModel.wordDegreeBound`, `OAI.PolycyclicRecognition.ComplexCartan.phaseVector`, `OAI.PolycyclicRecognition.ComplexCartan.rotationLinear`, `OAI.PolycyclicRecognition.ComplexTriangularAdjoint.nilradicalRotation`, `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput`, `OAI.PolycyclicRecognition.HasPolynomialLineCoordinates`, `OAI.PolycyclicRecognition.HasSemidirectPolynomialCoordinates`, `OAI.PolycyclicRecognition.LieCodimensionOneData.normedIdeal`, `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput`, `OAI.PolycyclicRecognition.NilpotentPublishedInputs`, `OAI.PolycyclicRecognition.PolynomialExponentialCoordinates`, `OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.derivationAction`, `OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.groupAutomorphism`, `OAI.PolycyclicRecognition.booleanStepRepresentation`, `OAI.PolycyclicRecognition.bracketWordDifferential`, `OAI.PolycyclicRecognition.cartanResidualDerivation`, `OAI.PolycyclicRecognition.cartanScalarDerivation`, `OAI.PolycyclicRecognition.cartanScalarOperator` and 23 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `PolycyclicRecognition_Algebra_BooleanPartitionMaps`, `PolycyclicRecognition_Algebra_CollinearDynkin`, `PolycyclicRecognition_Algebra_ConeIdealGroupConjugation`, `PolycyclicRecognition_Algebra_CoordinateMatrixRepresentation`, `PolycyclicRecognition_Algebra_CoordinateOrbitRepresentation`, `PolycyclicRecognition_Algebra_DynkinFiniteDifference`, `PolycyclicRecognition_Algebra_DynkinInput`, `PolycyclicRecognition_Algebra_DynkinIntegration`, `PolycyclicRecognition_Algebra_DynkinJacobian`, `PolycyclicRecognition_Algebra_DynkinLocalParameters`, `PolycyclicRecognition_Algebra_DynkinWords`, `PolycyclicRecognition_Algebra_MixedWordBasis`, `PolycyclicRecognition_Algebra_MixedWordIdeal`, `PolycyclicRecognition_Algebra_NilpotentAutomorphism`, `PolycyclicRecognition_Algebra_NilpotentIdealNorm`, `PolycyclicRecognition_Algebra_NilpotentPolynomialOperations`, `PolycyclicRecognition_Algebra_NilpotentPublishedInputs`, `PolycyclicRecognition_Algebra_NilpotentQuotientIntegration`, `PolycyclicRecognition_Algebra_PolynomialCoordinateCurves`, `PolycyclicRecognition_Algebra_PolynomialCoordinateOrbit`, `PolycyclicRecognition_Algebra_PolynomialCurveOperations`, `PolycyclicRecognition_Algebra_PolynomialDerivationAction`, `PolycyclicRecognition_Algebra_RealTorusAction`, `PolycyclicRecognition_Analysis_ConeIdealInnerHaar`, `PolycyclicRecognition_Analysis_ConeKernelHaar`, `PolycyclicRecognition_Analysis_DynkinHaarConstruction`, `PolycyclicRecognition_Analysis_MixedWordBoxModel`, `PolycyclicRecognition_Analysis_NilpotentBoxes`, `PolycyclicRecognition_Analysis_NilpotentHaarConstruction`, `PolycyclicRecognition_Analysis_TemplateSupportDirections`, `PolycyclicRecognition_Geometry_CartanBoxMaps`, `PolycyclicRecognition_Geometry_CartanConeIdeal`, `PolycyclicRecognition_Geometry_CartanDirectionalVisits`, `PolycyclicRecognition_Geometry_CartanPolarConeKernel`, `PolycyclicRecognition_Geometry_CartanPolarProbeTemplates`, `PolycyclicRecognition_Geometry_CartanResidualDerivation`, `PolycyclicRecognition_Geometry_CartanSampledVisits`, `PolycyclicRecognition_Geometry_CartanSegmentVisits`, `PolycyclicRecognition_Geometry_CartanSegmentWordPath`, `PolycyclicRecognition_Geometry_CartanSupportLegs`, `PolycyclicRecognition_Geometry_CartanTemplateVisits`, `PolycyclicRecognition_Geometry_CartanTemplateWordPath`, `PolycyclicRecognition_Geometry_ComplexAdjointKernel`, `PolycyclicRecognition_Geometry_ComplexCartanRotations`, `PolycyclicRecognition_Geometry_ComplexNilradical`, `PolycyclicRecognition_Geometry_ComplexRotationTorus`, `PolycyclicRecognition_Geometry_CoordinateLieBrackets`, `PolycyclicRecognition_Geometry_DerivationFlowRepresentation`, `PolycyclicRecognition_Geometry_DynkinLocalExponential`, `PolycyclicRecognition_Geometry_ExponentialAutomorphismTopology`, `PolycyclicRecognition_Geometry_ExponentialProduct`, `PolycyclicRecognition_Geometry_ExponentialRangeSubgroup`, `PolycyclicRecognition_Geometry_ExponentialRepresentationInput`, `PolycyclicRecognition_Geometry_IntegratedNilradicalRotations`, `PolycyclicRecognition_Geometry_IntrinsicDerivationFlow`, `PolycyclicRecognition_Geometry_LieIntegrationInput`, `PolycyclicRecognition_Geometry_LieWordDerivative`, `PolycyclicRecognition_Geometry_LieWordDifference`, `PolycyclicRecognition_Geometry_LieWordDifferential`, `PolycyclicRecognition_Geometry_NilpotentDerivationFlowSmooth`, `PolycyclicRecognition_Geometry_NilpotentExponentialSurjective`, `PolycyclicRecognition_Geometry_NilpotentSemidirectGroup`, `PolycyclicRecognition_Geometry_NilradicalRotationAction`, `PolycyclicRecognition_Geometry_PolynomialExponentialCoordinates`, `PolycyclicRecognition_Geometry_PolynomialLieWordCoordinates`, `PolycyclicRecognition_Geometry_PolynomialModelExponential`, `PolycyclicRecognition_Geometry_SemidirectCoordinateOrbit`, `PolycyclicRecognition_Geometry_SemidirectIntegration`, `PolycyclicRecognition_Geometry_SemidirectPolynomialCurves`, `PolycyclicRecognition_Geometry_SmoothCoordinateAction`.
--
--   **Imports.** It imports the published bundle `Def_PolycyclicRecognition`; the bundles `OAIQ093D001`, `OAIQ093D002` and `OAIQ093D003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ093D012`, `OAIQ093D014`, `OAIQ093D015` and `OAIQ093D026`; the statements `OAI.PolycyclicRecognition.CartanWordModel.cartan_normal_occupation_error_tendsto_zero`, `OAI.PolycyclicRecognition.CartanWordModel.cartan_profile_segment_volume_sequence`, `OAI.PolycyclicRecognition.CartanWordModel.eventually_root_neighbor_labels_eq`, `OAI.PolycyclicRecognition.CartanWordModel.exists_compact_measurable_box_profiles`, `OAI.PolycyclicRecognition.CartanWordModel.exists_compact_template_profile_paths`, `OAI.PolycyclicRecognition.CartanWordModel.exists_controlled_increment_volume`, `OAI_PolycyclicRecognition_CartanWordModel_exists_coupled_profile_comparison_region`, `OAI_PolycyclicRecognition_CartanWordModel_exists_directional_visit_bound`, `OAI.PolycyclicRecognition.CartanWordModel.exists_good_conjugated_word_paths`, `OAI_PolycyclicRecognition_CartanWordModel_exists_interval_recurrence_cells_sequence`, `OAI_PolycyclicRecognition_CartanWordModel_exists_metric_basepoint_comparison`, `OAI.PolycyclicRecognition.CartanWordModel.exists_segmentWordPath_bound`, `OAI.PolycyclicRecognition.CartanWordModel.exists_sequence_path_tuple_lifts`, `OAI.PolycyclicRecognition.CartanWordModel.exists_source_target_comparison_schemes`, `OAI.PolycyclicRecognition.CartanWordModel.exists_templateWordPath_bound`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_neighbor_label_threshold`, `OAI.PolycyclicRecognition.CartanWordModel.good_affine_templates_support_le`, `OAI.PolycyclicRecognition.CartanWordModel.source_target_product_exponent_le`, `OAI_PolycyclicRecognition_CartanWordModel_supported_switch_profiles_agree_on`, `OAI.PolycyclicRecognition.CartanWordModel.templateSupport_le_of_recurrent_segment_cells_sequence`, `OAI.PolycyclicRecognition.CartanWordModel.terminal_product_exponent_le`, `OAI.PolycyclicRecognition.cartan_cocycle_approximation`, `OAI_PolycyclicRecognition_cartan_cocycle_compact_words`, `OAI.PolycyclicRecognition.cartan_cocycle_polynomial_boxes`, `OAI.PolycyclicRecognition.exists_bounded_box_profile_anchors`, `OAI.PolycyclicRecognition.exists_cartan_n_log_metric_bound`, `OAI_PolycyclicRecognition_exists_compact_allowed_cartan_profiles` and `OAI.PolycyclicRecognition.exponentialLinearRealizationInput_intrinsic`; the proofs of `OAI_PolycyclicRecognition_CartanWordModel_exists_directional_visit_bound`, `OAI.PolycyclicRecognition.CartanWordModel.exists_segmentWordPath_bound`, `OAI.PolycyclicRecognition.CartanWordModel.exists_templateWordPath_bound`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_neighbor_label_threshold` and `OAI_PolycyclicRecognition_CartanWordModel_supported_switch_profiles_agree_on`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D001
import Definitions.Def_OAIQ093D002
import Definitions.Def_OAIQ093D003

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BooleanPartitionMaps
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Evaluation and split refinement maps for finite Boolean partitions -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
variable {X I : Type} (a : I → X → Bool)

abbrev booleanStepRepresentation : Rep ℤ PUnit.{1} := Rep.trivial ℤ PUnit.{1} (booleanStepRing a)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DynkinWords
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded finite Dynkin expansions

The analytic BCH input is separated from its elementary coordinate estimate.
A degree-`c` expansion in right-nested words, with uniformly bounded
coefficients, has polynomial growth in the number of input factors.
-/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

variable {L J : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]

/-- A finite expansion of degree at most `c` in `n` input logarithms. -/
def finiteDynkinPolynomial {c n : ℕ} (coeff : DynkinCoefficients c n) (X : Fin n → L) : L :=
  ∑ d : Fin c, ∑ w : Fin (d.val + 1) → Fin n,
    coeff d w • evalBracketWord X (rightNestedWord d.val w)

/-- Lie homomorphisms preserve the finite Dynkin polynomial. -/
theorem finiteDynkinPolynomial_map {L' : Type*} [LieRing L'] [LieAlgebra ℝ L']
    (f : L →ₗ⁅ℝ⁆ L') {c n : ℕ} (coeff : DynkinCoefficients c n) (X : Fin n → L) :
    f (finiteDynkinPolynomial coeff X) = finiteDynkinPolynomial coeff (fun i => f (X i)) := by
  simp only [finiteDynkinPolynomial, map_sum, map_smul, evalBracketWord_map]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DynkinInput
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The precise finite BCH input

Published source: F. Baudoin, *An Introduction to the Geometry of Stochastic
Flows* (Imperial College Press, 2004), Appendix B.5, equation (B.2) and the
multiple-exponential formula on p.124; Appendix B.6, p.126, makes the formula
global for nilpotent groups. Author's copy:
https://fabricebaudoin.blog/wp-content/uploads/2019/12/source.pdf

We use only its finite-degree consequence. Grouping the terms of the
multiple-exponential formula by their ordered letter word leaves at most
`2^(d-1)` cuts of a degree-`d` word. Each coefficient before grouping has
absolute value at most one. Thus `2^c` bounds each grouped coefficient for
all degrees at most `c`. The actual exponential is characterized by its
one-parameter subgroups and their derivatives, not by an arbitrary chart.
This is an explicit published-input parameter, never a global axiom.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule
open scoped BigOperators Manifold

variable (E G : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

/-- The bounded finite Dynkin expansion, specialized to the actual tangent
Lie algebra and its intrinsic exponential. No metric growth estimate is part
of this published hypothesis. -/
def NilpotentDynkinExpansionInput [T2Space G] : Prop :=
  ∀ (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G), IsGroupExponential Exp →
    ∀ c : ℕ, lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
      (GroupLieAlgebra (𝓘(ℝ, E)) G) c = ⊥ →
    ∀ n : ℕ, ∃ coeff : DynkinCoefficients c n,
      (∀ d w, |coeff d w| ≤ (2 : ℝ) ^ c) ∧
      ∀ X : Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G,
        (List.ofFn (fun i => Exp (X i))).prod = Exp (finiteDynkinPolynomial coeff X)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NilpotentBoxes
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products in actual nilpotent exponential boxes

The published finite BCH identity is transported to a chosen Lie-algebra
model. The uniform normalized structure constants then give the polynomial
product bound in the manuscript's box calculus, for every height scale and
letter support. No coordinate growth conclusion is assumed as an input.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule
open scoped BigOperators Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

/-- Transport only the finite expansion needed by the model. -/
theorem model_finiteDynkinExpansion
    (dynkin : NilpotentDynkinExpansionInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    {c : ℕ} (hc : lowerCentralSeries ℝ L L c = ⊥) (n : ℕ) :
    ∃ coeff : DynkinCoefficients c n, (∀ d w, |coeff d w| ≤ (2 : ℝ) ^ c) ∧
      ∀ X : Fin n → L, (List.ofFn (fun i => Exp (e (X i)))).prod =
        Exp (e (finiteDynkinPolynomial coeff X)) := by
  have hc' : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
      (GroupLieAlgebra (𝓘(ℝ, E)) G) c = ⊥ := by
    rw [← LieIdeal.lowerCentralSeries_map_eq c e.surjective, hc]
    simp only [LieIdeal.map_eq_bot_iff, bot_le]
  obtain ⟨coeff, hcoeff, hprod⟩ := dynkin Exp hExp c hc' n
  refine ⟨coeff, hcoeff, fun X => ?_⟩
  exact (hprod (fun i => e (X i))).trans
    (congrArg Exp (finiteDynkinPolynomial_map e.toLieHom coeff X).symm)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CollinearDynkin
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Collinear restrictions of the finite BCH formula

All nonlinear bracket terms vanish on a line. The derivative of a genuine
one-parameter subgroup then determines the remaining linear term, without
assuming injectivity of the exponential.
-/

noncomputable section
namespace PolycyclicRecognition

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L]

theorem finiteDynkinPolynomial_zero {c n : ℕ} (coeff : DynkinCoefficients c n) :
    finiteDynkinPolynomial coeff (0 : Fin n → L) = 0 := by
  have hw (w : FreeMagma (Fin n)) : evalBracketWord (0 : Fin n → L) w = 0 := by
    induction w using FreeMagma.rec with
    | of i => rfl
    | mul u v hu hv => simp only [evalBracketWord, hu, hv, lie_zero]
  simp only [finiteDynkinPolynomial, hw, smul_zero, Finset.sum_const_zero]

theorem eval_rightNestedWord_succ_collinear (a : I → ℝ) (v : L)
    (d : ℕ) (w : Fin (d + 2) → I) :
    evalBracketWord (fun i => a i • v) (rightNestedWord (d + 1) w) = 0 := by
  induction d with
  | zero => simp [rightNestedWord, evalBracketWord, lie_smul, smul_lie]
  | succ d ih =>
    change ⁅a (w 0) • v,
      evalBracketWord (fun i => a i • v) (rightNestedWord (d + 1) (fun i => w i.succ))⁆ = 0
    rw [ih, lie_zero]

theorem finiteDynkinPolynomial_collinear_smul {c n : ℕ}
    (coeff : DynkinCoefficients c n) (a : Fin n → ℝ) (v : L) (s : ℝ) :
    finiteDynkinPolynomial coeff (fun i => (s * a i) • v) =
      s • finiteDynkinPolynomial coeff (fun i => a i • v) := by
  have hw (k : ℕ) (w : Fin (k + 1) → Fin n) :
      evalBracketWord (fun i => (s * a i) • v) (rightNestedWord k w) =
        s • evalBracketWord (fun i => a i • v) (rightNestedWord k w) := by
    cases k with
    | zero => simp only [rightNestedWord, evalBracketWord, smul_smul]
    | succ k => simp only [eval_rightNestedWord_succ_collinear, smul_zero]
  simp only [finiteDynkinPolynomial, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro w _
  rw [hw, smul_smul, smul_smul, mul_comm (coeff d w) s]

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

/-- A single nonzero logarithm is fixed by the BCH polynomial, as follows
from the actual derivative of its exponential curve. -/
theorem finiteDynkinPolynomial_single_of_product
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {c n : ℕ} (coeff : DynkinCoefficients c n)
    (hprod : ∀ X : Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G,
      (List.ofFn (fun i => Exp (X i))).prod = Exp (finiteDynkinPolynomial coeff X))
    (i : Fin n) (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    finiteDynkinPolynomial coeff (Pi.single i v) = v := by
  classical
  apply hExp.eq_of_oneParameter_eq
  intro s
  have hbase : (fun j : Fin n => ((Pi.single i (1 : ℝ) : Fin n → ℝ) j) • v) = Pi.single i v := by
    funext j
    by_cases h : j = i <;> simp [h]
  have hscaled : (fun j : Fin n => (s * ((Pi.single i (1 : ℝ) : Fin n → ℝ) j)) • v) =
      Pi.single i (s • v) := by
    funext j
    by_cases h : j = i <;> simp [h]
  rw [← hbase, ← finiteDynkinPolynomial_collinear_smul, hscaled, ← hprod]
  simpa only [Pi.single_eq_same] using list_prod_ofFn_eq_single
    (fun j => Exp ((Pi.single i (s • v) :
      Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G) j)) i (by
      intro j hj
      simp [Pi.single_eq_of_ne hj, hExp.map_zero])

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_LieIntegrationInput
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Published integration input for nilpotent subalgebras

J. M. Lee, *Introduction to Smooth Manifolds*, second edition, GTM 218,
Springer (2013), Theorem 20.19 (p.530) and Proposition 20.8(g) (p.520).
https://doi.org/10.1007/978-1-4419-9982-5
Theorem 20.19 integrates a Lie algebra homomorphism from a simply connected
Lie group; Proposition 20.8(g) supplies exponential compatibility. We retain
only nilpotent source groups, the smooth homomorphism, its prescribed
differential and its action on the intrinsic exponential. Closedness is proved separately from the
already available global charts, rather than added to the input.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {EN N EG G : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace N] [ChartedSpace EN N] [Group N] [LieGroup (𝓘(ℝ, EN)) ⊤ N]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace G] [ChartedSpace EG G] [Group G] [LieGroup (𝓘(ℝ, EG)) ⊤ G]

/-- Integration plus the two global charts yields a closed subgroup map
whose range is exactly the exponential image of the Lie-algebra range. -/
theorem exists_closed_integration
    [SimplyConnectedSpace N]
    (integrate : NilpotentLieIntegrationInput (EN := EN) (N := N) (EG := EG) (G := G))
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, EN)) N))
    (j : GroupLieAlgebra (𝓘(ℝ, EN)) N →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EG)) G)
    (hj : Function.Injective j)
    (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N)
    (ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G)
    (hExpN : IsGroupExponential ExpN) (hExpG : IsGroupExponential ExpG)
    (cN : GroupLieAlgebra (𝓘(ℝ, EN)) N ≃ₜ N) (hcN : ∀ x, cN x = ExpN x)
    (cG : GroupLieAlgebra (𝓘(ℝ, EG)) G ≃ₜ G) (hcG : ∀ x, cG x = ExpG x) :
    ∃ ι : N →* G, Topology.IsClosedEmbedding ι ∧
      ContMDiff (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ∞ ι ∧
      (∀ x, mfderiv (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ι 1 x = j x) ∧
      (∀ x, ι (ExpN x) = ExpG (j x)) ∧ Set.range ι = ExpG '' Set.range j := by
  obtain ⟨ι, hsmooth, hderiv, hι⟩ := integrate inferInstance hnil j ExpN ExpG hExpN hExpG
  refine ⟨ι, isClosedEmbedding_of_exponential_compatibility cN cG ExpN ExpG hcN hcG
    j.toLinearMap hj ι hι, hsmooth, hderiv, hι, ?_⟩
  ext g
  constructor
  · rintro ⟨n, rfl⟩
    obtain ⟨x, hx⟩ := cN.surjective n
    rw [hcN] at hx
    exact ⟨j x, ⟨x, rfl⟩, (hι x).symm.trans (congrArg ι hx)⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨ExpN x, hι x⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentQuotientIntegration
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating a nilpotent algebra quotient with a continuous section

Lee's Lie correspondence supplies the integrated homomorphism.
Surjectivity, the kernel description, and compact lifts follow from
the exponential charts.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {EN N EQ Q : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace N] [ChartedSpace EN N] [Group N] [LieGroup (𝓘(ℝ, EN)) ⊤ N]
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [FiniteDimensional ℝ EQ]
  [TopologicalSpace Q] [ChartedSpace EQ Q] [Group Q] [LieGroup (𝓘(ℝ, EQ)) ⊤ Q]

/-- A surjective Lie algebra homomorphism integrates to a surjective group
homomorphism with a continuous section obtained from a linear section in
logarithmic coordinates. -/
theorem exists_surjective_integration_with_section
    [SimplyConnectedSpace N]
    (integrate : NilpotentLieIntegrationInput (EN := EN) (N := N) (EG := EQ) (G := Q))
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, EN)) N))
    (j : GroupLieAlgebra (𝓘(ℝ, EN)) N →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EQ)) Q)
    (hj : Function.Surjective j)
    (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N)
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, EQ)) Q → Q)
    (hExpN : IsGroupExponential ExpN) (hExpQ : IsGroupExponential ExpQ)
    (cN : GroupLieAlgebra (𝓘(ℝ, EN)) N ≃ₜ N) (hcN : ∀ x, cN x = ExpN x)
    (cQ : GroupLieAlgebra (𝓘(ℝ, EQ)) Q ≃ₜ Q) (hcQ : ∀ x, cQ x = ExpQ x) :
    ∃ (π : N →* Q) (s : C(Q, N)),
      ContMDiff (𝓘(ℝ, EN)) (𝓘(ℝ, EQ)) ∞ π ∧
      (∀ x, π (ExpN x) = ExpQ (j x)) ∧
      (∀ x, cQ.symm (π x) = j (cN.symm x)) ∧
      (∀ y, π (s y) = y) ∧ Function.Surjective π ∧
      (π.ker : Set N) = cN '' (j.ker : Set (GroupLieAlgebra (𝓘(ℝ, EN)) N)) ∧
      ∀ K : Set Q, IsCompact K → ∃ C : Set N, IsCompact C ∧ π '' C = K := by
  obtain ⟨π, hsmooth, _hdiff, hπexp⟩ :=
    integrate inferInstance hnil j ExpN ExpQ hExpN hExpQ
  obtain ⟨σ, hσ⟩ := j.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hj)
  have hσapply (y) : j (σ y) = y :=
    LinearMap.congr_fun hσ y
  let s : C(Q, N) :=
    ⟨fun y => cN (σ (cQ.symm y)),
      cN.continuous.comp (σ.toContinuousLinearMap.continuous.comp cQ.symm.continuous)⟩
  have hchart (x) : π (cN x) = cQ (j x) := by rw [hcN, hcQ, hπexp]
  have hlog (x : N) : cQ.symm (π x) = j (cN.symm x) := by
    obtain ⟨v, rfl⟩ := cN.surjective x
    rw [hchart, cQ.symm_apply_apply, cN.symm_apply_apply]
  have hc0 : cQ (0 : GroupLieAlgebra (𝓘(ℝ, EQ)) Q) = 1 :=
    (hcQ 0).trans hExpQ.map_zero
  have hlog0 : cQ.symm 1 = 0 := by
    apply cQ.injective
    rw [cQ.apply_symm_apply]
    exact hc0.symm
  have hs (y : Q) : π (s y) = y := by
    change π (cN (σ (cQ.symm y))) = y
    rw [hchart, hσapply, cQ.apply_symm_apply]
  refine ⟨π, s, hsmooth, hπexp, hlog, hs, (fun y => ⟨s y, hs y⟩), ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      have hx' : π x = 1 := hx
      refine ⟨cN.symm x, ?_, cN.apply_symm_apply x⟩
      change j (cN.symm x) = 0
      rw [← hlog, hx']
      exact hlog0
    · rintro ⟨v, hv, rfl⟩
      change π (cN v) = 1
      rw [hchart, show j v = 0 from hv, hcQ, hExpQ.map_zero]
  · intro K hK
    refine ⟨s '' K, hK.image s.continuous, ?_⟩
    ext y
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      rwa [hs]
    · intro hy
      exact ⟨s y, ⟨y, hy, rfl⟩, hs y⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_MixedWordIdeal
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mixed-word ideal used by the cone quotients -/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- Every ideal containing the outside letters contains every mixed word. -/
theorem eval_mixed_mem_ideal (X : I → L) (outside : I → Prop)
    (J : LieIdeal ℝ L) (hJ : ∀ i, outside i → X i ∈ J)
    (w : FreeMagma I) (hw : IsMixedWord outside w) : evalBracketWord X w ∈ J := by
  induction w using FreeMagma.rec with
  | of i => exact hJ i hw
  | mul u v hu hv =>
    rcases hw with hw | hw
    · exact lie_mem_left ℝ L J _ _ (hu hw)
    · exact J.lie_mem (hv hw)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanConeIdeal
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mixed-word ideal contains every outside generalized weight space -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set

set_option maxHeartbeats 1000000 in
/-- A pure word has weight in any additively closed set containing all of
its letter weights. -/
theorem bracketWordWeight_mem_of_pure
    {I H : Type*} [AddCommGroup H] [Module ℝ H]
    (α : I → H →ₗ[ℝ] ℝ) (C : Set (H →ₗ[ℝ] ℝ))
    (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (w : FreeMagma I) (hw : ¬IsMixedWord (fun i => α i ∉ C) w) :
    bracketWordWeight α w ∈ C := by
  induction w using FreeMagma.rec with
  | of i => exact Classical.not_not.mp hw
  | mul u v hu hv =>
    exact hadd _ (hu (fun h => hw (Or.inl h))) _ (hv (fun h => hw (Or.inr h)))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_MixedWordBasis
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite mixed-word spanning pools for the cone ideals -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

def coneMixedWords (C : Set (H →ₗ[ℝ] ℝ)) :=
  {w : M.wordList // IsMixedWord (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) w}

instance instFintypeConeMixedWords (C : Set (H →ₗ[ℝ] ℝ)) : Fintype (M.coneMixedWords C) := by
  classical
  unfold coneMixedWords
  infer_instance

instance instDecidableEqConeMixedWords (C : Set (H →ₗ[ℝ] ℝ)) : DecidableEq (M.coneMixedWords C) :=
  Classical.decEq _

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MixedWordBoxModel
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete nilpotent box model of a cone ideal

The finite mixed words generate the ideal even as a vector space. Using
them as an alphabet allows the existing box calculus to apply directly.
Flattening this alphabet retains the original word and its exact width.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule LieAlgebra
open scoped BigOperators

namespace CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

def coneOriginalWord (C : Set (H →ₗ[ℝ] ℝ))
    (w : FreeMagma (M.coneMixedWords C)) : FreeMagma (Fin M.letterCount) :=
  substituteBracketWord (fun i => i.val.val) w

def coneIdealWordCost (C : Set (H →ₗ[ℝ] ℝ)) (s : Fin M.letterCount → ℝ)
    (w : FreeMagma (M.coneMixedWords C)) : ℝ :=
  bracketWordExponent (fun i : M.coneMixedWords C => bracketWordExponent s i.val.val) w

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentAutomorphism
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating the needed nilpotent automorphisms

The finite published Dynkin identity and bijectivity of the intrinsic
exponential suffice to integrate any Lie automorphism of the nilpotent
model. No general Lie-integration theorem is assumed here.
-/

noncomputable section

namespace PolycyclicRecognition

open LieModule
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hbij : Function.Bijective Exp)

/-- A finite Lie polynomial commutes with `F`, so the same Dynkin formula
on both sides proves multiplicativity after exponentiation. -/
theorem exponentialConjugate_map_mul
    (dynkin : NilpotentDynkinExpansionInput E G) (hExp : IsGroupExponential Exp)
    {c : ℕ} (hc : lowerCentralSeries ℝ L L c = ⊥)
    (F : L ≃ₗ⁅ℝ⁆ L) (g k : G) :
    exponentialConjugate e Exp hbij F (g * k) =
      exponentialConjugate e Exp hbij F g * exponentialConjugate e Exp hbij F k := by
  obtain ⟨x, rfl⟩ := (hbij.comp e.bijective).surjective g
  obtain ⟨y, rfl⟩ := (hbij.comp e.bijective).surjective k
  change exponentialConjugate e Exp hbij F (Exp (e x) * Exp (e y)) =
    exponentialConjugate e Exp hbij F (Exp (e x)) *
    exponentialConjugate e Exp hbij F (Exp (e y))
  obtain ⟨coeff, _, hprod⟩ := model_finiteDynkinExpansion dynkin e Exp hExp hc 2
  have hp (u v : L) : Exp (e u) * Exp (e v) =
      Exp (e (finiteDynkinPolynomial coeff ![u, v])) := by
    simpa [List.ofFn_succ] using hprod ![u, v]
  rw [hp, exponentialConjugate_apply_exp, exponentialConjugate_apply_exp,
    exponentialConjugate_apply_exp, hp]
  congr 2
  calc
    F (finiteDynkinPolynomial coeff ![x, y]) =
        finiteDynkinPolynomial coeff (fun i => F (![x, y] i)) :=
      finiteDynkinPolynomial_map F.toLieHom coeff ![x, y]
    _ = _ := by
      congr 1
      funext i
      fin_cases i <;> rfl

/-- The group automorphism needed for exact weight dilation. -/
def integrateNilpotentLieEquiv
    (dynkin : NilpotentDynkinExpansionInput E G) (hExp : IsGroupExponential Exp)
    {c : ℕ} (hc : lowerCentralSeries ℝ L L c = ⊥) (F : L ≃ₗ⁅ℝ⁆ L) : G ≃* G where
  __ := exponentialConjugate e Exp hbij F
  map_mul' := exponentialConjugate_map_mul e Exp hbij dynkin hExp hc F

@[simp] theorem integrateNilpotentLieEquiv_apply_exp
    (dynkin : NilpotentDynkinExpansionInput E G) (hExp : IsGroupExponential Exp)
    {c : ℕ} (hc : lowerCentralSeries ℝ L L c = ⊥) (F : L ≃ₗ⁅ℝ⁆ L) (x : L) :
    integrateNilpotentLieEquiv e Exp hbij dynkin hExp hc F (Exp (e x)) = Exp (e (F x)) :=
  exponentialConjugate_apply_exp e Exp hbij F x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanBoxMaps
attribute [-instance] _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Propagating root-action bounds through Cartan boxes

A Lie map which preserves the letter root spaces has a polynomial bound in
every maximizing box. The proof propagates the bounds on letters through
actual bracket words, then through their coordinate basis. This is the
algebraic step in the box-conjugation estimate.
-/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators Manifold

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype I] [DecidableEq I]

namespace CartanWordModel

variable [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (LieAlgebra.ad ℝ L x) = 0)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- A fixed degree bound for the finite list of actual words. -/
def wordDegreeBound : ℕ := ∑ w : M.wordList, bracketWordLength (w : FreeMagma (Fin M.letterCount))

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ConeIdealGroupConjugation
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Strict-width inclusions for actual group conjugation -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra Filter
open scoped Topology

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

local instance instNormedAddCommGroupSubtypeMemLieIdealRealCartanRootIdeal : NormedAddCommGroup (cartanRootIdeal H) :=
  NormedAddCommGroup.induced _ _ (finBasis ℝ (cartanRootIdeal H)).equivFun.toLinearMap
    (finBasis ℝ (cartanRootIdeal H)).equivFun.injective
local instance instNormedSpaceRealSubtypeMemLieIdealCartanRootIdeal : NormedSpace ℝ (cartanRootIdeal H) :=
  NormedSpace.induced ℝ _ _ (finBasis ℝ (cartanRootIdeal H)).equivFun.toLinearMap

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialProduct
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products of exponential curves

Coordinates of the second kind require only smoothness of each individual
one-parameter subgroup. Their differential at zero is the sum of the
specified tangent vectors.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

theorem tangentCombination_succ {n : ℕ}
    (v : Fin (n + 1) → E) :
    ((1 : ℝ →L[ℝ] ℝ).smulRight (v 0)).comp
        (ContinuousLinearMap.proj (0 : Fin (n + 1))) +
      (tangentCombination (E := E) (v ∘ Fin.succ)).comp (coordinateTail n) =
      tangentCombination (E := E) v := by
  ext x
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    tangentCombination_apply, coordinateTail_apply]
  change x 0 • v 0 + ∑ i : Fin n, x i.succ • v i.succ =
    ∑ i : Fin (n + 1), x i • v i
  rw [Fin.sum_univ_succ]

omit [LieGroup (𝓘(ℝ, E)) ⊤ G] in
theorem IsGroupExponential.exponentialProduct_zero
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {n : ℕ} (v : Fin n → E) :
    exponentialProduct Exp v 0 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Exp ((0 : ℝ) • v 0) * exponentialProduct Exp (v ∘ Fin.succ) 0 = 1
    rw [zero_smul, ih, mul_one]
    exact hExp.map_zero

theorem IsGroupExponential.contMDiff_exponentialProduct
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {n : ℕ} (v : Fin n → E) :
    ContMDiff (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, E)) ∞ (exponentialProduct Exp v) := by
  induction n with
  | zero => exact contMDiff_const
  | succ n ih =>
    have hhead := (hExp.contMDiff_curve (v 0)).comp
      (ContinuousLinearMap.proj (0 : Fin (n + 1)) : (Fin (n + 1) → ℝ) →L[ℝ] ℝ).contDiff.contMDiff
    have htail := (ih (v ∘ Fin.succ)).comp (coordinateTail n).contDiff.contMDiff
    exact hhead.mul htail

theorem IsGroupExponential.hasMFDerivAt_exponentialProduct_zero
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {n : ℕ} (v : Fin n → E) :
    HasMFDerivAt (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, E))
      (exponentialProduct Exp v) 0 (tangentCombination (E := E) v) := by
  induction n with
  | zero =>
    apply (hasMFDerivAt_const (I := 𝓘(ℝ, Fin 0 → ℝ)) (I' := 𝓘(ℝ, E))
      (1 : G) (0 : Fin 0 → ℝ)).congr_mfderiv
    change (0 : (Fin 0 → ℝ) →L[ℝ] E) = tangentCombination (E := E) v
    simp [tangentCombination]
  | succ n ih =>
    have hhead := (hExp.hasMFDerivAt_zero (v 0)).comp (0 : Fin (n + 1) → ℝ)
      (ContinuousLinearMap.proj (0 : Fin (n + 1)) :
        (Fin (n + 1) → ℝ) →L[ℝ] ℝ).hasFDerivAt.hasMFDerivAt
    have htail := (ih (v ∘ Fin.succ)).comp (0 : Fin (n + 1) → ℝ)
      (coordinateTail n).hasFDerivAt.hasMFDerivAt
    have hp := PolycyclicRecognition.HasMFDerivAt.mul_at_one hhead htail (by
      change Exp ((0 : ℝ) • v 0) = 1
      rw [zero_smul]
      exact hExp.map_zero)
      (by simpa using hExp.exponentialProduct_zero (v ∘ Fin.succ))
    apply hp.congr_mfderiv
    exact tangentCombination_succ v

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateOrbitRepresentation
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linearizing a group through its translated coordinate functions

Right translates of separating coordinates span a faithful representation.
A uniform finite-dimensional space containing those translates makes the
representation finite dimensional; polynomial multiplication will supply it.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G I : Type*} [Group G] (q : I → G → ℝ)

theorem coordinate_mem_orbitSpan (i : I) : q i ∈ coordinateOrbitSpan q := by
  apply Submodule.subset_span
  refine ⟨(1, i), ?_⟩
  funext x
  exact congrArg (q i) (mul_one x)

theorem rightTranslate_mem_coordinateOrbitSpan (g : G) {f : G → ℝ}
    (hf : f ∈ coordinateOrbitSpan q) :
    rightTranslateLinear g f ∈ coordinateOrbitSpan q := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨h, i⟩, rfl⟩ := hf
    apply Submodule.subset_span
    refine ⟨(g * h, i), ?_⟩
    funext x
    exact congrArg (q i) (mul_assoc x g h).symm
  | zero => exact (coordinateOrbitSpan q).zero_mem
  | add f h _ _ hf hh => exact (coordinateOrbitSpan q).add_mem hf hh
  | smul a f _ hf => exact (coordinateOrbitSpan q).smul_mem a hf

def coordinateOrbitRepresentation : Representation ℝ G (coordinateOrbitSpan q) where
  toFun g :=
    { toFun f := ⟨rightTranslateLinear g f, rightTranslate_mem_coordinateOrbitSpan q g f.2⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    exact congrArg (f : G → ℝ) (mul_one x)
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    exact congrArg (f : G → ℝ) (mul_assoc x g h).symm

@[simp] theorem coordinateOrbitRepresentation_apply (g : G)
    (f : coordinateOrbitSpan q) (x : G) :
    (coordinateOrbitRepresentation q g f : G → ℝ) x = (f : G → ℝ) (x * g) := rfl

theorem coordinateOrbitRepresentation_injective
    (hq : Function.Injective (fun g : G => fun i : I => q i g)) :
    Function.Injective (coordinateOrbitRepresentation q) := by
  intro g h he
  apply hq
  funext i
  let f : coordinateOrbitSpan q := ⟨q i, coordinate_mem_orbitSpan q i⟩
  have hf := congrArg (fun A : Module.End ℝ (coordinateOrbitSpan q) =>
    (A f : G → ℝ) 1) he
  simpa only [coordinateOrbitRepresentation_apply, one_mul] using hf

theorem finiteDimensional_coordinateOrbitSpan {J : Type*} [Finite J]
    (b : J → G → ℝ)
    (hb : ∀ (g : G) (i : I), (fun x => q i (x * g)) ∈ Submodule.span ℝ (Set.range b)) :
    FiniteDimensional ℝ (coordinateOrbitSpan q) := by
  have : FiniteDimensional ℝ (Submodule.span ℝ (Set.range b)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range b)
  apply Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℝ (Set.range b))
  apply Submodule.span_le.mpr
  rintro f ⟨⟨g, i⟩, rfl⟩
  exact hb g i

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothCoordinateAction
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth finite-dimensional actions from coordinate translates

This construction needs smooth coordinate functions, without assuming that
straight lines are exponential curves.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {G I W : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [Group G]
  [LieGroup (𝓘(ℝ, G)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (q : I → G → ℝ) (B : W ≃ₗ[ℝ] coordinateOrbitSpan q)

def smoothCoordinateAction : Representation ℝ G W :=
  B.symm.conjRingEquiv.toMonoidHom.comp (coordinateOrbitRepresentation q)

omit [NormedAddCommGroup G] [NormedSpace ℝ G]
  [LieGroup (𝓘(ℝ, G)) ⊤ G] [FiniteDimensional ℝ W] in
theorem smoothCoordinateAction_eval (g : G) (v : W) (a : G) :
    (B (smoothCoordinateAction q B g v) : G → ℝ) a = (B v : G → ℝ) (a * g) := by
  change (B (B.symm (_)) : G → ℝ) a = _
  rw [B.apply_symm_apply]
  rfl

theorem contDiff_coordinateTranslate (hq : ∀ i, ContDiff ℝ ∞ (q i))
    {f : G → ℝ} (hf : f ∈ coordinateOrbitSpan q) (a : G) :
    ContDiff ℝ ∞ (fun g => f (a * g)) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨h, i⟩, rfl⟩ := hf
    exact (hq i).comp (((contMDiff_mul_right (I := 𝓘(ℝ, G)) (a := h)).contDiff).comp
      ((contMDiff_mul_left (I := 𝓘(ℝ, G)) (a := a)).contDiff))
  | zero => exact contDiff_const
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact hf.const_smul c

theorem contDiff_smoothCoordinateAction (hq : ∀ i, ContDiff ℝ ∞ (q i)) (v : W) :
    ContDiff ℝ ∞ (fun g => smoothCoordinateAction q B g v) := by
  let e := (coordinateOrbitSpan q).subtype.comp B.toLinearMap
  apply contDiff_of_coordinateEvaluations e (Subtype.coe_injective.comp B.injective)
  intro a
  change ContDiff ℝ ∞ (fun g => (B (smoothCoordinateAction q B g v) : G → ℝ) a)
  simp only [smoothCoordinateAction_eval]
  exact contDiff_coordinateTranslate q hq (B v).2 a

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateMatrixRepresentation
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Matrix representations from finite-dimensional coordinate orbits -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {G I : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [Group G] [LieGroup (𝓘(ℝ, G)) ⊤ G] {m : ℕ}
  (q : I → G → ℝ) (B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan q)

def coordinateMatrixRepresentation : G →* Matrix.GeneralLinearGroup (Fin m) ℝ :=
  (Units.map LinearMap.toMatrixAlgEquiv'.toMonoidHom).comp
    (smoothCoordinateAction q B).asGroupHom

omit [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [LieGroup (𝓘(ℝ, G)) ⊤ G] in
theorem coordinateMatrixRepresentation_injective
    (hq : Function.Injective (fun g => fun i => q i g)) :
    Function.Injective (coordinateMatrixRepresentation q B) := by
  intro x y h
  have hA := LinearMap.toMatrixAlgEquiv'.injective (congrArg Units.val h)
  apply coordinateOrbitRepresentation_injective q hq
  exact B.symm.conjRingEquiv.injective hA

omit [FiniteDimensional ℝ G] in
theorem contDiff_coordinateMatrixRepresentation (hq : ∀ i, ContDiff ℝ ∞ (q i)) :
    ContDiff ℝ ∞ (fun g => (coordinateMatrixRepresentation q B g : Matrix (Fin m) (Fin m) ℝ)) := by
  let e : (Fin m → Fin m → ℝ) ≃ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ := LinearEquiv.refl ℝ _
  have hf : ContDiff ℝ ∞ (fun g => fun i j => smoothCoordinateAction q B g (Pi.single j 1) i) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact contDiff_pi.mp (contDiff_smoothCoordinateAction q B hq (Pi.single j 1)) i
  exact e.toContinuousLinearEquiv.contDiff.comp hf

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_LieWordDifferential
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.wordBasisOfDet_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Differentials of bracket words and the lower central series

Changing the basepoint in the differential of a Lie polynomial changes its
linear part only by a map that raises the lower central series. This is the
algebraic part of the Jacobian computation for nilpotent exponential coordinates.
-/

noncomputable section
namespace PolycyclicRecognition

open LieModule
open scoped BigOperators

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L]

def bracketWordDifferential (X : I → L) (dX : I → L →ₗ[ℝ] L) :
    FreeMagma I → L →ₗ[ℝ] L
  | .of i => dX i
  | .mul u v => (rightBracketLinear (evalBracketWord X v)).comp (bracketWordDifferential X dX u) +
      (LieAlgebra.ad ℝ L (evalBracketWord X u)).comp (bracketWordDifferential X dX v)

@[simp] theorem bracketWordDifferential_of (X : I → L) (dX : I → L →ₗ[ℝ] L)
    (i : I) (z : L) : bracketWordDifferential X dX (.of i) z = dX i z := rfl

@[simp] theorem bracketWordDifferential_mul (X : I → L) (dX : I → L →ₗ[ℝ] L)
    (u v : FreeMagma I) (z : L) :
    bracketWordDifferential X dX (u * v) z =
      ⁅bracketWordDifferential X dX u z, evalBracketWord X v⁆ +
        ⁅evalBracketWord X u, bracketWordDifferential X dX v z⁆ := rfl

theorem bracketWordDifferential_mem (X : I → L) (dX : I → L →ₗ[ℝ] L)
    (J : LieIdeal ℝ L) (z : L) (hz : ∀ i, dX i z ∈ J) (w : FreeMagma I) :
    bracketWordDifferential X dX w z ∈ J := by
  induction w using FreeMagma.rec with
  | of i => exact hz i
  | mul u v hu hv =>
    exact J.add_mem (lie_mem_left ℝ L J _ _ hu) (lie_mem_right ℝ L J _ _ hv)

theorem bracketWordDifferential_mul_mem_succ
    (X : I → L) (dX : I → L →ₗ[ℝ] L) (k : ℕ) (z : L)
    (hz : ∀ i, dX i z ∈ lowerCentralSeries ℝ L L k) (u v : FreeMagma I) :
    bracketWordDifferential X dX (u * v) z ∈ lowerCentralSeries ℝ L L (k + 1) := by
  have hu := bracketWordDifferential_mem X dX (lowerCentralSeries ℝ L L k) z hz u
  have hv := bracketWordDifferential_mem X dX (lowerCentralSeries ℝ L L k) z hz v
  have hright : ⁅evalBracketWord X u, bracketWordDifferential X dX v z⁆ ∈
      lowerCentralSeries ℝ L L (k + 1) := by
    rw [lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) hv
  have hleft : ⁅evalBracketWord X v, bracketWordDifferential X dX u z⁆ ∈
      lowerCentralSeries ℝ L L (k + 1) := by
    rw [lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) hu
  rw [bracketWordDifferential_mul]
  apply (lowerCentralSeries ℝ L L (k + 1)).add_mem _ hright
  rw [← lie_skew]
  exact (lowerCentralSeries ℝ L L (k + 1)).neg_mem hleft

theorem bracketWordDifferential_sub_mem_succ
    (X Y : I → L) (dX : I → L →ₗ[ℝ] L) (k : ℕ) (z : L)
    (hz : ∀ i, dX i z ∈ lowerCentralSeries ℝ L L k) (w : FreeMagma I) :
    bracketWordDifferential X dX w z - bracketWordDifferential Y dX w z ∈
      lowerCentralSeries ℝ L L (k + 1) := by
  cases w with
  | of i => simpa only [bracketWordDifferential_of, sub_self] using
      (lowerCentralSeries ℝ L L (k + 1)).zero_mem
  | mul u v =>
    exact (lowerCentralSeries ℝ L L (k + 1)).sub_mem
      (bracketWordDifferential_mul_mem_succ X dX k z hz u v)
      (bracketWordDifferential_mul_mem_succ Y dX k z hz u v)

def finiteDynkinDifferential {c n : ℕ} (coeff : DynkinCoefficients c n)
    (X : Fin n → L) (dX : Fin n → L →ₗ[ℝ] L) : L →ₗ[ℝ] L :=
  ∑ d : Fin c, ∑ w : Fin (d.val + 1) → Fin n,
    coeff d w • bracketWordDifferential X dX (rightNestedWord d.val w)

theorem finiteDynkinDifferential_sub_mem_succ {c n : ℕ}
    (coeff : DynkinCoefficients c n) (X Y : Fin n → L) (dX : Fin n → L →ₗ[ℝ] L)
    (k : ℕ) (z : L) (hz : ∀ i, dX i z ∈ lowerCentralSeries ℝ L L k) :
    finiteDynkinDifferential coeff X dX z - finiteDynkinDifferential coeff Y dX z ∈
      lowerCentralSeries ℝ L L (k + 1) := by
  simp only [finiteDynkinDifferential, LinearMap.sum_apply, LinearMap.smul_apply,
    ← Finset.sum_sub_distrib, ← smul_sub]
  apply (lowerCentralSeries ℝ L L (k + 1)).sum_mem
  intro d _
  apply (lowerCentralSeries ℝ L L (k + 1)).sum_mem
  intro w _
  exact (lowerCentralSeries ℝ L L (k + 1)).smul_mem (coeff d w)
    (bracketWordDifferential_sub_mem_succ X Y dX k z hz _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_LieWordDifference
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite differences of Lie words along the lower central series

The nonlinear part of a bracket polynomial raises the filtration also for
finite differences, not just infinitesimal ones. This supports the explicit
inverse of a BCH translation.
-/

noncomputable section
namespace PolycyclicRecognition

open LieModule

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L]

theorem evalBracketWord_sub_mem (X Y : I → L) (J : LieIdeal ℝ L)
    (hXY : ∀ i, X i - Y i ∈ J) (w : FreeMagma I) :
    evalBracketWord X w - evalBracketWord Y w ∈ J := by
  induction w using FreeMagma.rec with
  | of i => exact hXY i
  | mul u v hu hv =>
    rw [evalBracketWord, evalBracketWord, lie_sub_lie_decomposition]
    exact J.add_mem (lie_mem_left ℝ L J _ _ hu) (lie_mem_right ℝ L J _ _ hv)

theorem evalBracketWord_mul_sub_mem_succ (X Y : I → L) (k : ℕ)
    (hXY : ∀ i, X i - Y i ∈ lowerCentralSeries ℝ L L k) (u v : FreeMagma I) :
    evalBracketWord X (.mul u v) - evalBracketWord Y (.mul u v) ∈
      lowerCentralSeries ℝ L L (k + 1) := by
  have hu := evalBracketWord_sub_mem X Y (lowerCentralSeries ℝ L L k) hXY u
  have hv := evalBracketWord_sub_mem X Y (lowerCentralSeries ℝ L L k) hXY v
  change ⁅evalBracketWord X u, evalBracketWord X v⁆ -
    ⁅evalBracketWord Y u, evalBracketWord Y v⁆ ∈ lowerCentralSeries ℝ L L (k + 1)
  rw [lie_sub_lie_decomposition]
  apply (lowerCentralSeries ℝ L L (k + 1)).add_mem
  · have hh : ⁅evalBracketWord X v, evalBracketWord X u - evalBracketWord Y u⁆ ∈
        lowerCentralSeries ℝ L L (k + 1) := by
      rw [lowerCentralSeries_succ]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) hu
    rw [← lie_skew]
    exact (lowerCentralSeries ℝ L L (k + 1)).neg_mem hh
  · rw [lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) hv

theorem evalBracketWord_sub_linear_mem_succ (X Y : I → L) (k : ℕ)
    (hXY : ∀ i, X i - Y i ∈ lowerCentralSeries ℝ L L k) (w : FreeMagma I) :
    (evalBracketWord X w - evalBracketWord Y w) - wordLinearPart w (X - Y) ∈
      lowerCentralSeries ℝ L L (k + 1) := by
  cases w with
  | of i =>
    simpa only [evalBracketWord, wordLinearPart, LinearMap.proj_apply, Pi.sub_apply, sub_self]
      using (lowerCentralSeries ℝ L L (k + 1)).zero_mem
  | mul u v =>
    simpa only [wordLinearPart, LinearMap.zero_apply, sub_zero]
      using evalBracketWord_mul_sub_mem_succ X Y k hXY u v

theorem finiteDynkinPolynomial_sub_linear_mem_succ {c n : ℕ}
    (coeff : DynkinCoefficients c n) (X Y : Fin n → L) (k : ℕ)
    (hXY : ∀ i, X i - Y i ∈ lowerCentralSeries ℝ L L k) :
    (finiteDynkinPolynomial coeff X - finiteDynkinPolynomial coeff Y) -
        finiteDynkinLinearPart coeff (X - Y) ∈ lowerCentralSeries ℝ L L (k + 1) := by
  simp only [finiteDynkinPolynomial, finiteDynkinLinearPart, LinearMap.sum_apply,
    LinearMap.smul_apply, ← Finset.sum_sub_distrib, ← smul_sub]
  apply (lowerCentralSeries ℝ L L (k + 1)).sum_mem
  intro d _
  apply (lowerCentralSeries ℝ L L (k + 1)).sum_mem
  intro w _
  exact (lowerCentralSeries ℝ L L (k + 1)).smul_mem (coeff d w)
    (evalBracketWord_sub_linear_mem_succ X Y k hXY _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DynkinFiniteDifference
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Global inverses for nilpotent BCH translations

Axis normalization fixes the linear term. Every other term raises the
lower central series, so the finite correction construction applies.
-/

noncomputable section
namespace PolycyclicRecognition

open LieModule

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

theorem finiteDynkinPolynomial_collinear_eq_linear {c n : ℕ}
    (coeff : DynkinCoefficients c n) (a : Fin n → ℝ) (v : L) :
    finiteDynkinPolynomial coeff (fun i => a i • v) =
      finiteDynkinLinearPart coeff (fun i => a i • v) := by
  have hw (k : ℕ) (w : Fin (k + 1) → Fin n) :
      evalBracketWord (fun i => a i • v) (rightNestedWord k w) =
        wordLinearPart (rightNestedWord k w) (fun i => a i • v) := by
    cases k with
    | zero => rfl
    | succ k => rw [eval_rightNestedWord_succ_collinear]; rfl
  simp only [finiteDynkinPolynomial, finiteDynkinLinearPart, LinearMap.sum_apply,
    LinearMap.smul_apply, hw]

theorem finiteDynkinPolynomial_single_eq_linear {c n : ℕ}
    (coeff : DynkinCoefficients c n) (i : Fin n) (v : L) :
    finiteDynkinPolynomial coeff (Pi.single i v) =
      finiteDynkinLinearPart coeff (Pi.single i v) := by
  classical
  have heq : (Pi.single i v : Fin n → L) =
      fun j => ((Pi.single i (1 : ℝ) : Fin n → ℝ) j) • v := by
    funext j
    by_cases h : j = i <;> simp [h]
  rw [heq]
  exact finiteDynkinPolynomial_collinear_eq_linear coeff _ v

theorem binaryDynkinLinearPart {c : ℕ} (coeff : DynkinCoefficients c 2)
    (haxis : ∀ (i : Fin 2) (v : L), finiteDynkinPolynomial coeff (Pi.single i v) = v)
    (x y : L) : finiteDynkinLinearPart coeff ![x, y] = x + y := by
  have hsplit : ![x, y] = (Pi.single 0 x : Fin 2 → L) + Pi.single 1 y := by
    funext i
    fin_cases i <;> simp
  rw [hsplit, map_add, ← finiteDynkinPolynomial_single_eq_linear,
    ← finiteDynkinPolynomial_single_eq_linear, haxis, haxis]

theorem binaryDynkin_raises_difference {c : ℕ} (coeff : DynkinCoefficients c 2)
    (haxis : ∀ (i : Fin 2) (v : L), finiteDynkinPolynomial coeff (Pi.single i v) = v)
    (a : L) (k : ℕ) (x y : L) (hxy : x - y ∈ lowerCentralSeries ℝ L L k) :
    (finiteDynkinPolynomial coeff ![a, x] - finiteDynkinPolynomial coeff ![a, y]) -
        (x - y) ∈ lowerCentralSeries ℝ L L (k + 1) := by
  have hh := finiteDynkinPolynomial_sub_linear_mem_succ coeff ![a, x] ![a, y] k (by
    intro i
    fin_cases i
    · simp
    · exact hxy)
  have hdiff : ![a, x] - ![a, y] = ![0, x - y] := by
    funext i
    fin_cases i <;> simp
  rw [hdiff, binaryDynkinLinearPart coeff haxis, zero_add] at hh
  exact hh

theorem binaryDynkin_raises_left_difference {c : ℕ} (coeff : DynkinCoefficients c 2)
    (haxis : ∀ (i : Fin 2) (v : L), finiteDynkinPolynomial coeff (Pi.single i v) = v)
    (a : L) (k : ℕ) (x y : L) (hxy : x - y ∈ lowerCentralSeries ℝ L L k) :
    (finiteDynkinPolynomial coeff ![x, a] - finiteDynkinPolynomial coeff ![y, a]) -
        (x - y) ∈ lowerCentralSeries ℝ L L (k + 1) := by
  have hh := finiteDynkinPolynomial_sub_linear_mem_succ coeff ![x, a] ![y, a] k (by
    intro i
    fin_cases i
    · exact hxy
    · simp)
  have hdiff : ![x, a] - ![y, a] = ![x - y, 0] := by
    funext i
    fin_cases i <;> simp
  rw [hdiff, binaryDynkinLinearPart coeff haxis, add_zero] at hh
  exact hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DynkinIntegration
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integration from a common finite BCH formula

A common two-factor BCH formula for the source and target makes
exponential conjugation of a Lie algebra homomorphism multiplicative.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {E G F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [ChartedSpace F H] [Group H] [LieGroup (𝓘(ℝ, F)) ⊤ H]
  (cG : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
  (cH : GroupLieAlgebra (𝓘(ℝ, F)) H ≃ₜ H)
  (hG : IsGroupExponential cG) (hH : IsGroupExponential cH)
  {c : ℕ} (coeff : DynkinCoefficients c 2)
  (hprodG : ∀ x y, cG x * cG y = cG (finiteDynkinPolynomial coeff ![x, y]))
  (hprodH : ∀ x y, cH x * cH y = cH (finiteDynkinPolynomial coeff ![x, y]))
  (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, F)) H)

def exponentialHomOfDynkin : G →* H where
  toFun g := cH (j (cG.symm g))
  map_one' := by
    erw [← hG.map_zero, Homeomorph.symm_apply_apply, map_zero]
    exact hH.map_zero
  map_mul' g k := by
    obtain ⟨x, rfl⟩ := cG.surjective g
    obtain ⟨y, rfl⟩ := cG.surjective k
    erw [hprodG, Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply,
      Homeomorph.symm_apply_apply, hprodH, finiteDynkinPolynomial_map]
    congr 2
    funext i
    fin_cases i <;> rfl

@[simp] theorem exponentialHomOfDynkin_apply_exp
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    exponentialHomOfDynkin cG cH hG hH coeff hprodG hprodH j (cG x) = cH (j x) := by
  change cH (j (cG.symm (cG x))) = _
  rw [Homeomorph.symm_apply_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_LieWordDerivative
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual derivatives of finite Lie polynomials

The finite-dimensional bracket is continuous in the given norm. The resulting
differential is the algebraic word differential.
-/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

theorem hasFDerivAt_evalBracketWord {I : Type*}
    (X : L → I → L) (dX : I → L →ₗ[ℝ] L) (z : L)
    (hX : ∀ i, HasFDerivAt (fun y => X y i) (dX i).toContinuousLinearMap z)
    (w : FreeMagma I) :
    HasFDerivAt (fun y => evalBracketWord (X y) w)
      (bracketWordDifferential (X z) dX w).toContinuousLinearMap z := by
  induction w using FreeMagma.rec with
  | of i => exact hX i
  | mul u v hu hv =>
    have hh := (normedLieBracket (L := L)).hasFDerivAt_of_bilinear hu hv
    apply hh.congr_fderiv
    ext a
    change ⁅evalBracketWord (X z) u, bracketWordDifferential (X z) dX v a⁆ +
        ⁅bracketWordDifferential (X z) dX u a, evalBracketWord (X z) v⁆ =
      ⁅bracketWordDifferential (X z) dX u a, evalBracketWord (X z) v⁆ +
        ⁅evalBracketWord (X z) u, bracketWordDifferential (X z) dX v a⁆
    exact add_comm _ _

theorem hasFDerivAt_finiteDynkinPolynomial {c n : ℕ}
    (coeff : DynkinCoefficients c n) (X : L → Fin n → L)
    (dX : Fin n → L →ₗ[ℝ] L) (z : L)
    (hX : ∀ i, HasFDerivAt (fun y => X y i) (dX i).toContinuousLinearMap z) :
    HasFDerivAt (fun y => finiteDynkinPolynomial coeff (X y))
      (finiteDynkinDifferential coeff (X z) dX).toContinuousLinearMap z := by
  have hh := HasFDerivAt.sum fun d (_ : d ∈ Finset.univ) =>
    HasFDerivAt.sum fun w (_ : w ∈ Finset.univ) =>
      (hasFDerivAt_evalBracketWord X dX z hX (rightNestedWord d.val w)).const_smul (coeff d w)
  have hfun : (∑ d : Fin c, ∑ w : Fin (d.val + 1) → Fin n,
      coeff d w • fun y => evalBracketWord (X y) (rightNestedWord d.val w)) =
      fun y => finiteDynkinPolynomial coeff (X y) := by
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, finiteDynkinPolynomial]
  rw [hfun] at hh
  apply hh.congr_fderiv
  ext a
  simp only [sum_apply, smul_apply,
    LinearMap.coe_toContinuousLinearMap', finiteDynkinDifferential,
    LinearMap.sum_apply, LinearMap.smul_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DynkinJacobian
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unit Jacobian of left translation in nilpotent BCH coordinates -/

noncomputable section
namespace PolycyclicRecognition

open LieModule

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

theorem hasFDerivAt_rightDynkin {c : ℕ} (coeff : DynkinCoefficients c 2) (x y : L) :
    HasFDerivAt (fun z => finiteDynkinPolynomial coeff ![x, z])
      (finiteDynkinDifferential coeff ![x, y] (rightVariableDifferential (L := L))).toContinuousLinearMap y := by
  apply hasFDerivAt_finiteDynkinPolynomial coeff (fun z => ![x, z]) (rightVariableDifferential (L := L)) y
  intro i
  fin_cases i
  · exact hasFDerivAt_const (𝕜 := ℝ) x y
  · exact hasFDerivAt_id (𝕜 := ℝ) y

theorem rightDynkinDifferential_zero {c : ℕ} (coeff : DynkinCoefficients c 2)
    (hunit : ∀ y : L, finiteDynkinPolynomial coeff ![0, y] = y) :
    finiteDynkinDifferential coeff ![0, 0] (rightVariableDifferential (L := L)) = 1 := by
  have hd := hasFDerivAt_rightDynkin coeff (0 : L) 0
  have heq : (fun y : L => finiteDynkinPolynomial coeff ![0, y]) = id := funext hunit
  rw [heq] at hd
  have hh := hd.unique (hasFDerivAt_id (𝕜 := ℝ) (0 : L))
  ext v
  exact congrArg (fun D : L →L[ℝ] L => D v) hh

theorem rightDynkinDifferential_det {c : ℕ} (coeff : DynkinCoefficients c 2)
    (hunit : ∀ y : L, finiteDynkinPolynomial coeff ![0, y] = y)
    {d : ℕ} (hd : lowerCentralSeries ℝ L L d = ⊥) (x y : L) :
    LinearMap.det (finiteDynkinDifferential coeff ![x, y] (rightVariableDifferential (L := L))) = 1 := by
  apply det_eq_one_of_raises_filtration (fun k => (lowerCentralSeries ℝ L L k).toSubmodule)
    (by simp) (congrArg LieSubmodule.toSubmodule hd)
  intro k v hv
  have hh := finiteDynkinDifferential_sub_mem_succ coeff ![x, y] ![0, 0]
    (rightVariableDifferential (L := L)) k v (by
      intro i
      fin_cases i
      · exact (lowerCentralSeries ℝ L L k).zero_mem
      · exact hv)
  rw [rightDynkinDifferential_zero coeff hunit] at hh
  exact hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CoordinateLieBrackets
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Lie law in a chosen basis

Transport the original bracket to Euclidean coordinates, retaining its exact
word identities. A bound on basis structure constants gives a bound in the
finite-dimensional parameter space used for normalized-law compactness.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}
  (b : Basis (Fin n) ℝ L)

/-- Word evaluation commutes exactly with the coordinate transport. -/
theorem evalBilinearWord_basisBracket {I : Type*} (X : I → L) (w : FreeMagma I) :
    evalBilinearWord (basisBracket b) (fun i => b.equivFun (X i)) w =
      b.equivFun (evalBracketWord X w) := by
  induction w using FreeMagma.rec with
  | of i => rfl
  | mul a c ha hc =>
    simp only [evalBilinearWord, ha, hc, basisBracket_apply, LinearEquiv.symm_apply_apply,
      evalBracketWord]


end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DynkinLocalParameters
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local BCH parameters without an exponential bijection

The basis-input BCH polynomial is smooth and has derivative the identity
at zero. Its derivative follows from the one-coordinate restrictions,
already determined by the actual exponential curves.
-/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped ContDiff

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {c n : ℕ}

theorem basisDynkinParameter_eq (coeff : DynkinCoefficients c n)
    (b : Basis (Fin n) ℝ L) (x : Fin n → ℝ) :
    basisDynkinParameter coeff b x =
      b.equivFun (finiteDynkinPolynomial coeff (fun i => x i • b i)) := by
  unfold basisDynkinParameter bilinearDynkinPolynomial finiteDynkinPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [evalBilinearWord_basisBracket, map_smul]

theorem contDiff_basisDynkinParameter (coeff : DynkinCoefficients c n)
    (b : Basis (Fin n) ℝ L) : ContDiff ℝ ∞ (basisDynkinParameter coeff b) := by
  have hX : ∀ i : Fin n, ContDiff ℝ ∞
      (fun x : Fin n → ℝ => b.equivFun (x i • b i)) := by
    intro i
    let d : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
      (ContinuousLinearMap.proj i).smulRight (b.equivFun (b i))
    have heq : (fun x : Fin n → ℝ => b.equivFun (x i • b i)) = d := by
      funext x
      exact map_smul b.equivFun (x i) (b i)
    rw [heq]
    exact d.contDiff

  exact contDiff_bilinearDynkinPolynomial coeff
    (fun _ : Fin n → ℝ => basisBracket b)
    (fun (x : Fin n → ℝ) i => b.equivFun (x i • b i)) contDiff_const hX

@[simp] theorem basisDynkinParameter_zero (coeff : DynkinCoefficients c n)
    (b : Basis (Fin n) ℝ L) : basisDynkinParameter coeff b 0 = 0 := by
  rw [basisDynkinParameter_eq]
  simp only [Pi.zero_apply, zero_smul]
  exact (congrArg b.equivFun (finiteDynkinPolynomial_zero coeff)).trans (map_zero _)

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

theorem basisDynkinParameter_single_of_product
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (coeff : DynkinCoefficients c n)
    (hprod : ∀ X : Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G,
      (List.ofFn (fun i => Exp (X i))).prod = Exp (finiteDynkinPolynomial coeff X))
    (b : Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) (i : Fin n) (s : ℝ) :
    basisDynkinParameter coeff b (Pi.single i s) = Pi.single i s := by
  classical
  have heq : (fun j => (Pi.single i s : Fin n → ℝ) j • b j) = Pi.single i (s • b i) := by
    funext j
    by_cases h : j = i <;> simp [h]
  rw [basisDynkinParameter_eq, heq,
    finiteDynkinPolynomial_single_of_product hExp coeff hprod]
  ext j
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, Basis.equivFun_self]
  by_cases h : i = j <;> simp [h, eq_comm]

theorem hasFDerivAt_basisDynkinParameter_zero
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (coeff : DynkinCoefficients c n)
    (hprod : ∀ X : Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G,
      (List.ofFn (fun i => Exp (X i))).prod = Exp (finiteDynkinPolynomial coeff X))
    (b : Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    HasFDerivAt (basisDynkinParameter coeff b) (ContinuousLinearMap.id ℝ (Fin n → ℝ)) 0 := by
  have hd := (contDiff_basisDynkinParameter coeff b).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hcol (i : Fin n) : fderiv ℝ (basisDynkinParameter coeff b) 0 (Pi.single i 1) =
      Pi.single i 1 := by
    have hh := (hd 0).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      (hasDerivAt_single i (0 : ℝ)) (by simp)
    have heq : (fun s : ℝ => basisDynkinParameter coeff b (Pi.single i s)) =
        fun s => (Pi.single i s : Fin n → ℝ) := by
      funext s
      exact basisDynkinParameter_single_of_product hExp coeff hprod b i s
    change HasDerivAt (fun s : ℝ => basisDynkinParameter coeff b (Pi.single i s)) _ 0 at hh
    rw [heq] at hh
    exact hh.unique (hasDerivAt_single i (0 : ℝ))
  apply (hd 0).hasFDerivAt.congr_fderiv
  apply ContinuousLinearMap.ext
  intro x
  change fderiv ℝ (basisDynkinParameter coeff b) 0 x = x
  calc
    _ = fderiv ℝ (basisDynkinParameter coeff b) 0 (∑ i, x i • Pi.single i 1) :=
      congrArg _ (pi_eq_sum_univ' x)
    _ = ∑ i, x i • Pi.single i 1 := by simp only [map_sum, map_smul, hcol]
    _ = x := (pi_eq_sum_univ' x).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentIdealNorm
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A compatible norm on the codimension-one ideal -/

noncomputable section
namespace PolycyclicRecognition.LieCodimensionOneData

variable {L : Type*} [RealNormedLieAlgebra L] (C : LieCodimensionOneData L)

@[instance_reducible]
def normedIdeal : RealNormedLieAlgebra C.ideal := by
  let : NormedAddCommGroup C.ideal := NormedAddCommGroup.induced C.ideal L
    C.ideal.incl Subtype.val_injective
  let : NormedSpace ℝ C.ideal := NormedSpace.induced ℝ C.ideal L C.ideal.incl.toLinearMap
  exact { (inferInstance : NormedAddCommGroup C.ideal),
    (inferInstance : LieRing C.ideal), (inferInstance : NormedSpace ℝ C.ideal),
    (inferInstance : LieAlgebra ℝ C.ideal) with }

end PolycyclicRecognition.LieCodimensionOneData

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentDerivationFlowSmooth
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial dependence of a nilpotent derivation flow -/

noncomputable section
namespace PolycyclicRecognition

open scoped ContDiff

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

local instance instModuleRat_solutions_1 : Module ℚ L := Module.compHom L (algebraMap ℚ ℝ)

local instance q145LieRatGeometryNilpotentDerivationFlowSmooth_re7aceb_1 : LieAlgebra ℚ L where
  lie_smul t x y := lie_smul (algebraMap ℚ ℝ t) x y
omit [FiniteDimensional ℝ L] in
theorem nilpotentDerivationFlow_eq_sum {k : ℕ} (hk : D.toLinearMap ^ k = 0)
    (t : ℝ) (x : L) :
    nilpotentDerivationFlow D hD t x =
      ∑ i ∈ Finset.range k, t ^ i • (((i.factorial : ℚ)⁻¹ • D.toLinearMap ^ i) x) := by
  change IsNilpotent.exp (t • D.toLinearMap) x = _
  have ht : (t • D.toLinearMap) ^ k = 0 := by rw [smul_pow, hk, smul_zero]
  rw [IsNilpotent.exp_eq_sum ht]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_pow]
  apply Finset.sum_congr rfl
  intro i _
  exact smul_comm _ _ _

theorem contDiff_nilpotentDerivationFlow {r : ℕ∞ω} :
    ContDiff ℝ r (fun p : ℝ × L => nilpotentDerivationFlow D hD p.1 p.2) := by
  have hnil := hD
  obtain ⟨k, hk⟩ := hnil
  have heq : (fun p : ℝ × L => nilpotentDerivationFlow D hD p.1 p.2) =
      fun p => ∑ i ∈ Finset.range k,
        p.1 ^ i • (((i.factorial : ℚ)⁻¹ • D.toLinearMap ^ i) p.2) := by
    funext p
    exact nilpotentDerivationFlow_eq_sum D hD hk p.1 p.2
  rw [heq]
  apply ContDiff.sum
  intro i _
  exact (contDiff_fst.pow i).smul
    ((((i.factorial : ℚ)⁻¹ • D.toLinearMap ^ i).toContinuousLinearMap.contDiff).comp contDiff_snd)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentPolynomialOperations
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Composing the polynomial operations used in a nilpotent extension -/

noncomputable section
namespace PolycyclicRecognition

open scoped ContDiff

variable {L V : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {r : ℕ∞ω}

theorem contDiff_derivationFlow_comp
    (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)
    {f : V → ℝ} {g : V → L} (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g) :
    ContDiff ℝ r (fun x => nilpotentDerivationFlow D hD (f x) (g x)) := by
  have hp : ContDiff ℝ r (fun x : V => (f x, g x)) := hf.prodMk hg
  have h := ContDiff.comp
    (f := fun x : V => (f x, g x))
    (g := fun p : ℝ × L => nilpotentDerivationFlow D hD p.1 p.2)
    (contDiff_nilpotentDerivationFlow D hD (r := r)) hp
  exact h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialRangeSubgroup
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The BCH exponential image is a subgroup

Once local exponential coordinates put a neighborhood in the image,
connectedness gives surjectivity. No injectivity is needed for this step.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Manifold Topology

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

def exponentialRangeSubgroup
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {c : ℕ} (coeff : DynkinCoefficients c 2)
    (hprod : ∀ x y, Exp x * Exp y = Exp (finiteDynkinPolynomial coeff ![x, y])) :
    Subgroup G where
  carrier := range Exp
  one_mem' := ⟨0, hExp.map_zero⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨finiteDynkinPolynomial coeff ![x, y], (hprod x y).symm⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, hExp.map_neg x⟩

theorem exponential_surjective_of_range_mem_nhds [PreconnectedSpace G]
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {c : ℕ} (coeff : DynkinCoefficients c 2)
    (hprod : ∀ x y, Exp x * Exp y = Exp (finiteDynkinPolynomial coeff ![x, y]))
    (hopen : range Exp ∈ 𝓝 (1 : G)) : Function.Surjective Exp := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let H := exponentialRangeSubgroup hExp coeff hprod
  have hH : IsOpen (H : Set G) := H.isOpen_of_mem_nhds hopen
  have htop : (H : Set G) = univ :=
    (show IsClopen (H : Set G) from ⟨H.isClosed_of_isOpen hH, hH⟩).eq_univ ⟨1, H.one_mem⟩
  intro g
  exact (show g ∈ (H : Set G) from htop ▸ mem_univ g)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_DynkinLocalExponential
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local regularity of the intrinsic exponential from BCH

The BCH basis-input polynomial has identity derivative. Composing its local
inverse with the smooth product of one-parameter subgroups constructs local
exponential coordinates, without an assumed global logarithm.
-/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped Manifold ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

omit [FiniteDimensional ℝ E] [LieGroup (𝓘(ℝ, E)) ⊤ G] in
theorem exponentialProduct_eq_list_prod
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) {n : ℕ}
    (v : Fin n → E) (x : Fin n → ℝ) :
    exponentialProduct Exp v x = (List.ofFn (fun i => Exp (x i • v i))).prod := by
  induction n with
  | zero => simp [exponentialProduct]
  | succ n ih =>
    simp only [exponentialProduct, List.ofFn_succ, List.prod_cons]
    rw [ih]
    rfl

theorem exponential_comp_basisDynkinParameter
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} {c n : ℕ}
    (coeff : DynkinCoefficients c n)
    (hprod : ∀ X : Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G,
      (List.ofFn (fun i => Exp (X i))).prod = Exp (finiteDynkinPolynomial coeff X))
    (b : Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    (Exp ∘ b.equivFun.symm) ∘ basisDynkinParameter coeff b =
      exponentialProduct Exp (fun i => (b i : E)) := by
  funext x
  change Exp (b.equivFun.symm (basisDynkinParameter coeff b x)) = _
  rw [basisDynkinParameter_eq, b.equivFun.symm_apply_apply]
  exact (hprod _).symm.trans
    (exponentialProduct_eq_list_prod Exp (fun i => (b i : E)) x).symm

theorem local_exponential_regularity_of_dynkin
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {c n : ℕ} (coeff : DynkinCoefficients c n)
    (hprod : ∀ X : Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G,
      (List.ofFn (fun i => Exp (X i))).prod = Exp (finiteDynkinPolynomial coeff X))
    (b : Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    ContMDiffAt (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, E)) ∞ (Exp ∘ b.equivFun.symm) 0 ∧
      HasMFDerivAt (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, E)) (Exp ∘ b.equivFun.symm) 0
        (tangentCombination (E := E) (fun i => (b i : E))) := by
  apply regularity_of_unit_parameter (E := E) (M := G) (basisDynkinParameter coeff b)
    (contDiff_basisDynkinParameter coeff b).contDiffAt
    (hasFDerivAt_basisDynkinParameter_zero hExp coeff hprod b)
    (basisDynkinParameter_zero coeff b)
  · rw [exponential_comp_basisDynkinParameter coeff hprod b]
    exact (hExp.contMDiff_exponentialProduct (fun i => (b i : E))).contMDiffAt
  · rw [exponential_comp_basisDynkinParameter coeff hprod b]
    exact hExp.hasMFDerivAt_exponentialProduct_zero (fun i => (b i : E))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentExponentialSurjective
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Surjectivity of the nilpotent exponential from finite BCH

Local regularity gives a neighborhood in the exponential image. The binary
BCH formula makes that image a subgroup, so connectedness gives surjectivity.
No global exponential chart is assumed.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Set Filter
open scoped Manifold Topology

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

omit [T2Space G] in
theorem range_exponential_mem_nhds_of_basis_formula
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {c n : ℕ} (coeff : DynkinCoefficients c n)
    (hprod : ∀ X : Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G,
      (List.ofFn (fun i => Exp (X i))).prod = Exp (finiteDynkinPolynomial coeff X))
    (b : Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    range Exp ∈ 𝓝 (1 : G) := by
  let d : (Fin n → ℝ) ≃L[ℝ] E := b.equivFun.symm.toContinuousLinearEquiv.trans
    (tangentSpaceCastModel (𝓘(ℝ, E)) (1 : G))
  have hcomb : tangentCombination (E := E) (fun i => (b i : E)) = d.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    exact (tangentCombination_apply (E := E) (fun i => (b i : E)) x).trans
      (b.equivFun_symm_apply x).symm
  obtain ⟨hf, hd⟩ := local_exponential_regularity_of_dynkin hExp coeff hprod b
  rw [hcomb] at hd
  have hm := (locally_injective_open_of_mfderiv_equiv d hf hd).2
  have hz : (Exp ∘ b.equivFun.symm) 0 = 1 := by
    simp only [Function.comp_apply, map_zero, hExp.map_zero]
  have hmem : range (Exp ∘ b.equivFun.symm) ∈ 𝓝 (1 : G) := by
    rw [← hz, ← hm]
    exact Filter.range_mem_map
  apply mem_of_superset hmem
  rintro _ ⟨x, rfl⟩
  exact ⟨b.equivFun.symm x, rfl⟩

theorem exponential_surjective_of_nilpotent_dynkin [PreconnectedSpace G]
    (dynkin : NilpotentDynkinExpansionInput E G)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    Function.Surjective Exp := by
  obtain ⟨c, hc⟩ := (isNilpotent_iff ℝ _ _).mp hnil
  let b := finBasis ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
  obtain ⟨coeffN, _, hprodN⟩ := dynkin Exp hExp c hc (finrank ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
  have hmem := range_exponential_mem_nhds_of_basis_formula hExp coeffN hprodN b
  obtain ⟨coeff, _, hprod⟩ := dynkin Exp hExp c hc 2
  apply exponential_surjective_of_range_mem_nhds hExp coeff (fun x y => ?_) hmem
  simpa only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    mul_one, Matrix.cons_val_zero, Matrix.cons_val_succ] using hprod ![x, y]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PolynomialExponentialCoordinates
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial group coordinates on a nilpotent algebra

Transport an existing model through its global exponential chart. The finite
BCH law makes the transported operations analytic. Its actual tangent bracket
is identified by differentiating the chart as a group homomorphism.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

class PolynomialExponentialCoordinates (L : Type*) [RealNormedLieAlgebra L]
    [FiniteDimensional ℝ L] where
  [group : Group L]
  [lieGroup : LieGroup (𝓘(ℝ, L)) ⊤ L]
  one_eq_zero : (1 : L) = 0
  inv_eq_neg : ∀ x : L, x⁻¹ = -x
  degree : ℕ
  coefficients : DynkinCoefficients degree 2
  mul_eq : ∀ x y : L, x * y = finiteDynkinPolynomial coefficients ![x, y]
  tangentEquiv : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, L)) L
  tangentEquiv_apply : ∀ x : L, tangentEquiv x = x

attribute [instance] PolynomialExponentialCoordinates.group
attribute [instance_reducible] PolynomialExponentialCoordinates.group
attribute [instance] PolynomialExponentialCoordinates.lieGroup

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialDerivationAction
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derivation flows act on polynomial exponential groups -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

namespace PolynomialExponentialCoordinates

def groupAutomorphism (e : L ≃ₗ⁅ℝ⁆ L) : MulAut L where
  toEquiv := e.toLinearEquiv.toEquiv
  map_mul' x y := by
    rw [P.mul_eq, P.mul_eq]
    have h := finiteDynkinPolynomial_map e.toLieHom P.coefficients ![x, y]
    change e (finiteDynkinPolynomial P.coefficients ![x, y]) = _ at h
    change e (finiteDynkinPolynomial P.coefficients ![x, y]) = _
    rw [h]
    congr 1
    funext i
    fin_cases i <;> rfl

@[simp] theorem groupAutomorphism_apply (e : L ≃ₗ⁅ℝ⁆ L) (x : L) :
    groupAutomorphism (P := P) e x = e x := rfl

def derivationAction (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap) :
    Multiplicative ℝ →* MulAut L where
  toFun t := groupAutomorphism (P := P) (nilpotentDerivationFlow D hD t.toAdd)
  map_one' := by
    ext x
    exact nilpotentDerivationFlow_zero D hD x
  map_mul' s t := by
    ext x
    exact nilpotentDerivationFlow_add D hD s.toAdd t.toAdd x

@[simp] theorem derivationAction_apply (D : LieDerivation ℝ L L)
    (hD : IsNilpotent D.toLinearMap) (t : Multiplicative ℝ) (x : L) :
    derivationAction (P := P) D hD t x = nilpotentDerivationFlow D hD t.toAdd x := rfl

end PolynomialExponentialCoordinates
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentSemidirectGroup
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Analytic semidirect products for the nilpotent induction

The carrier is the vector space `L × ℝ`. Its operations are polynomial because
the action is the exponential of a nilpotent derivation.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

def derivationSemidirectEquiv : (L × ℝ) ≃
    (L ⋊[PolynomialExponentialCoordinates.derivationAction D hD] Multiplicative ℝ) where
  toFun p := ⟨p.1, Multiplicative.ofAdd p.2⟩
  invFun p := (p.left, p.right.toAdd)
  left_inv _ := rfl
  right_inv _ := rfl

@[instance_reducible] def derivationSemidirectGroup : Group (L × ℝ) :=
  (derivationSemidirectEquiv D hD).group

section Operations

theorem derivationSemidirect_mul (x y : L × ℝ) :
    (derivationSemidirectGroup D hD).mul x y =
      (x.1 * nilpotentDerivationFlow D hD x.2 y.1, x.2 + y.2) := rfl

theorem derivationSemidirect_one :
    (derivationSemidirectGroup D hD).one = (0, 0) := by
  change ((1 : L), (0 : ℝ)) = (0, 0)
  rw [P.one_eq_zero]

theorem derivationSemidirect_inv (x : L × ℝ) :
    (derivationSemidirectGroup D hD).inv x =
      (nilpotentDerivationFlow D hD (-x.2) (-x.1), -x.2) := by
  change (nilpotentDerivationFlow D hD (-x.2) (x.1⁻¹), -x.2) = _
  rw [P.inv_eq_neg]

omit P in
theorem contDiff_derivationSemidirect_inv {r : ℕ∞ω} :
    ContDiff ℝ r (fun p : L × ℝ =>
      (nilpotentDerivationFlow D hD (-p.2) (-p.1), -p.2)) := by
  exact (contDiff_derivationFlow_comp D hD contDiff_snd.neg contDiff_fst.neg).prodMk
    contDiff_snd.neg

end Operations
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PolynomialModelExponential
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.derivationAction_apply _root_.OAI.PolycyclicRecognition.PolynomialExponentialCoordinates.groupAutomorphism_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Straight one-parameter subgroups in polynomial exponential coordinates -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

theorem PolynomialExponentialCoordinates.axis_normalized (i : Fin 2) (v : L) :
    finiteDynkinPolynomial P.coefficients (Pi.single i v) = v := by
  fin_cases i
  · change finiteDynkinPolynomial P.coefficients (Pi.single (0 : Fin 2) v) = v
    have heq : (Pi.single (0 : Fin 2) v) = ![v, 0] := by
      ext j
      fin_cases j <;> simp
    rw [heq, ← P.mul_eq, ← P.one_eq_zero, mul_one]
  · change finiteDynkinPolynomial P.coefficients (Pi.single (1 : Fin 2) v) = v
    have heq : (Pi.single (1 : Fin 2) v) = ![0, v] := by
      ext j
      fin_cases j <;> simp
    rw [heq, ← P.mul_eq, ← P.one_eq_zero, one_mul]

theorem PolynomialExponentialCoordinates.smul_mul (v : L) (s t : ℝ) :
    (s • v) * (t • v) = (s + t) • v := by
  rw [P.mul_eq]
  have heq : (fun i : Fin 2 => ![s, t] i • v) = ![s • v, t • v] := by
    ext i
    fin_cases i <;> rfl
  have h := finiteDynkinPolynomial_collinear_eq_linear P.coefficients ![s, t] v
  rw [heq, binaryDynkinLinearPart P.coefficients
    (PolynomialExponentialCoordinates.axis_normalized)] at h
  exact h.trans (add_smul s t v).symm

theorem PolynomialExponentialCoordinates.isGroupExponential_identity :
    IsGroupExponential (fun x : GroupLieAlgebra (𝓘(ℝ, L)) L => (x : L)) := by
  refine ⟨P.one_eq_zero.symm, ?_, ?_⟩
  · intro v s t
    exact (PolynomialExponentialCoordinates.smul_mul (L := L) (v : L) s t).symm
  · intro v
    exact ((hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const (show L from v)).hasMFDerivAt

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCoordinateOrbit
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-dimensional coordinate orbits from polynomial multiplication

The coefficients may be arbitrary functions of the right factor. Only the
finite polynomial dependence on the left coordinates is needed here.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G I : Type*} [Group G] (q : I → G → ℝ)

theorem finiteDimensional_coordinateOrbitSpan_of_polynomial [Finite I]
    (p : I → MvPolynomial I (G → ℝ))
    (hmul : ∀ (g : G) (i : I) (x : G),
      q i (x * g) = coordinatePolynomialEvaluation q (p i) g x) :
    FiniteDimensional ℝ (coordinateOrbitSpan q) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let J := Σ i : I, ↥(p i).support
  let : Fintype J := by dsimp [J]; infer_instance
  let b : J → G → ℝ := fun j => coordinateMonomial q j.2.val
  apply finiteDimensional_coordinateOrbitSpan q b
  intro g i
  have heq : (fun x => q i (x * g)) = coordinatePolynomialEvaluation q (p i) g :=
    funext (hmul g i)
  rw [heq, coordinatePolynomialEvaluation_eq_sum]
  apply Submodule.sum_mem
  intro d hd
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨⟨i, ⟨d, hd⟩⟩, rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PolynomialLieWordCoordinates
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate polynomials for finite Lie expressions -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {L I J S A : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
  [CommRing A] [Algebra ℝ A] (b : Module.Basis J ℝ L)

theorem eval_bracketCoordinatePolynomial
    (X : I → J → MvPolynomial S A) (f : A →ₐ[ℝ] ℝ) (a : S → ℝ)
    (Y : I → L) (hX : ∀ i j, (X i j).eval₂ f.toRingHom a = b.repr (Y i) j)
    (w : FreeMagma I) (j : J) :
    (bracketCoordinatePolynomial b X w j).eval₂ f.toRingHom a =
      b.repr (evalBracketWord Y w) j := by
  have hc (r : ℝ) : f.toRingHom (algebraMap ℝ A r) = r := f.commutes r
  induction w using FreeMagma.rec generalizing j with
  | of i => exact hX i j
  | mul u v hu hv =>
    simp only [bracketCoordinatePolynomial, MvPolynomial.eval₂_sum,
      MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, hc, hu, hv, evalBracketWord]
    rw [basis_bracket_coordinate]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring

def dynkinCoordinatePolynomial {c n : ℕ} (coeff : DynkinCoefficients c n)
    (X : Fin n → J → MvPolynomial S A) (j : J) : MvPolynomial S A :=
  ∑ d : Fin c, ∑ w : Fin (d.val + 1) → Fin n,
    MvPolynomial.C (algebraMap ℝ A (coeff d w)) *
      bracketCoordinatePolynomial b X (rightNestedWord d.val w) j

theorem eval_dynkinCoordinatePolynomial {c n : ℕ} (coeff : DynkinCoefficients c n)
    (X : Fin n → J → MvPolynomial S A) (f : A →ₐ[ℝ] ℝ) (a : S → ℝ)
    (Y : Fin n → L) (hX : ∀ i j, (X i j).eval₂ f.toRingHom a = b.repr (Y i) j)
    (j : J) :
    (dynkinCoordinatePolynomial b coeff X j).eval₂ f.toRingHom a =
      b.repr (finiteDynkinPolynomial coeff Y) j := by
  have hc (r : ℝ) : f.toRingHom (algebraMap ℝ A r) = r := f.commutes r
  simp only [dynkinCoordinatePolynomial, finiteDynkinPolynomial,
    MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    hc, eval_bracketCoordinatePolynomial b X f a Y hX,
    map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCoordinateCurves
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial scalar curves in polynomial group coordinates -/

noncomputable section
namespace PolycyclicRecognition

variable {L J : Type*} [RealNormedLieAlgebra L] [Fintype J]
  (b : Module.Basis J ℝ L)

def HasPolynomialLineCoordinates (F : ℝ → L) : Prop :=
  ∀ j, (fun t => b.repr (F t) j) ∈ polynomialFunctions

omit [Fintype J] in
theorem hasPolynomialLineCoordinates_line (v : L) : HasPolynomialLineCoordinates b (fun t => t • v) := by
  intro j
  simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using
    polynomialFunctions_linear (b.repr v j)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialCurveOperations
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial curves under linear maps and nilpotent derivation flows -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  {n : ℕ} (b : Module.Basis (Fin n) ℝ L)

local instance polynomialCurveModuleRat : Module ℚ L := Module.compHom L (algebraMap ℚ ℝ)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemidirectCoordinateOrbit
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial coordinate orbits in the nilpotent semidirect construction -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators ContDiff

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n : ℕ}
  (b : Module.Basis (Fin n) ℝ L)
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

local instance semidirectCoordinateModuleRat : Module ℚ L := Module.compHom L (algebraMap ℚ ℝ)

def semidirectCoordinate : (Fin n ⊕ Unit) → (L × ℝ) → ℝ
  | .inl i, p => b.repr p.1 i
  | .inr _, p => p.2

omit P in
theorem contDiff_semidirectCoordinate (i : Fin n ⊕ Unit) :
    ContDiff ℝ ∞ (semidirectCoordinate b i) := by
  cases i with
  | inl i => exact (contDiff_pi.mp b.equivFun.toContinuousLinearEquiv.contDiff i).comp contDiff_fst
  | inr i => exact contDiff_snd

def semidirectFlowCoordinatePolynomial (k : ℕ) (j : Fin n) :
    MvPolynomial (Fin n ⊕ Unit) ((L × ℝ) → ℝ) :=
  ∑ i ∈ Finset.range k,
    MvPolynomial.C (fun g => b.repr (((i.factorial : ℚ)⁻¹ • D.toLinearMap ^ i) g.1) j) *
      MvPolynomial.X (.inr ()) ^ i

omit [FiniteDimensional ℝ L] P in
theorem semidirectFlowCoordinatePolynomial_eval {k : ℕ} (hk : D.toLinearMap ^ k = 0)
    (x g : L × ℝ) (j : Fin n) :
    coordinatePolynomialEvaluation (semidirectCoordinate b)
      (semidirectFlowCoordinatePolynomial b D k j) g x =
      b.repr (nilpotentDerivationFlow D hD x.2 g.1) j := by
  rw [nilpotentDerivationFlow_eq_sum D hD hk]
  simp only [semidirectFlowCoordinatePolynomial, coordinatePolynomialEvaluation,
    MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X, Pi.evalRingHom_apply,
    semidirectCoordinate, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_comm _ _

def semidirectProductCoordinatePolynomial (k : ℕ) :
    (Fin n ⊕ Unit) → MvPolynomial (Fin n ⊕ Unit) ((L × ℝ) → ℝ)
  | .inl j => dynkinCoordinatePolynomial b P.coefficients
      ![(fun i => MvPolynomial.X (.inl i)), semidirectFlowCoordinatePolynomial b D k] j
  | .inr _ => MvPolynomial.X (.inr ()) + MvPolynomial.C (fun g => g.2)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemidirectPolynomialCurves
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial scalar curves in semidirect coordinates -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n : ℕ}
  (b : Module.Basis (Fin n) ℝ L)
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

def HasSemidirectPolynomialCoordinates (F : ℝ → L × ℝ) : Prop :=
  ∀ i, (fun t => semidirectCoordinate b i (F t)) ∈ polynomialFunctions

omit [FiniteDimensional ℝ L] P in
theorem hasSemidirectPolynomialCoordinates_const (v : L × ℝ) :
    HasSemidirectPolynomialCoordinates b (fun _ => v) :=
  fun _ => polynomialFunctions_const _

omit [FiniteDimensional ℝ L] P in
theorem hasSemidirectPolynomialCoordinates_line (v : L × ℝ) :
    HasSemidirectPolynomialCoordinates b (fun t => t • v) := by
  intro i
  cases i with
  | inl i => exact hasPolynomialLineCoordinates_line b v.1 i
  | inr i => exact polynomialFunctions_linear v.2

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_DynkinHaarConstruction
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Haar measure derived from a finite BCH chart

The global chart and its group multiplication formula suffice: the Jacobian
of every left translation is one because its nonconstant part raises the
lower central series. No Haar compatibility is assumed.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory LieModule

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [MeasurableSpace L] [BorelSpace L]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

theorem dynkin_chart_map_isHaar
    (chart : L ≃ₜ G) (hzero : chart 0 = 1)
    {c : ℕ} (coeff : DynkinCoefficients c 2)
    (hprod : ∀ x y, chart x * chart y = chart (finiteDynkinPolynomial coeff ![x, y]))
    {d : ℕ} (hd : lowerCentralSeries ℝ L L d = ⊥)
    (μ : Measure L) [μ.IsAddHaarMeasure] : (Measure.map chart μ).IsHaarMeasure := by
  have hunit : ∀ y : L, finiteDynkinPolynomial coeff ![0, y] = y := by
    intro y
    apply chart.injective
    rw [← hprod, hzero, one_mul]
  apply homeomorph_map_isHaar_of_translations chart μ
  intro g
  have heq : (fun z => chart.symm (g * chart z)) =
      fun z => finiteDynkinPolynomial coeff ![chart.symm g, z] := by
    funext z
    apply chart.injective
    simp only [chart.apply_symm_apply, ← hprod]
  have hbij : Function.Bijective (fun z => chart.symm (g * chart z)) :=
    chart.symm.bijective.comp ((Group.mulLeft_bijective g).comp chart.bijective)
  rw [heq] at hbij ⊢
  apply map_eq_self_of_unit_jacobian μ _
    (fun y => (finiteDynkinDifferential coeff ![chart.symm g, y]
      (rightVariableDifferential (L := L))).toContinuousLinearMap)
    (fun y => hasFDerivAt_rightDynkin coeff (chart.symm g) y) hbij
  intro y
  exact rightDynkinDifferential_det coeff hunit hd (chart.symm g) y

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_NilpotentHaarConstruction
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Haar measure from nilpotent exponential coordinates

A global exponential homeomorphism and the finite BCH formula imply
Lebesgue invariance in every linear basis.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory LieModule Module
open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G] [SimplyConnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]

theorem NilpotentGlobalExponentialChartInput.toCoordinates
    (charts : NilpotentGlobalExponentialChartInput E G)
    (dynkin : NilpotentDynkinExpansionInput E G) :
    NilpotentExponentialCoordinatesInput E G := by
  intro Exp hExp hnil
  obtain ⟨chart, hchart⟩ := charts Exp hExp hnil
  refine ⟨⟨chart, hchart⟩, ?_⟩
  let L := GroupLieAlgebra (𝓘(ℝ, E)) G
  let : NormedAddCommGroup L := by
    change NormedAddCommGroup E
    exact inferInstance
  let : NormedSpace ℝ L := by
    change NormedSpace ℝ E
    exact inferInstance
  let : RealNormedLieAlgebra L :=
    { (inferInstance : NormedAddCommGroup L), (inferInstance : LieRing L),
      (inferInstance : NormedSpace ℝ L), (inferInstance : LieAlgebra ℝ L) with }
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : MeasurableSpace L := borel L
  let : BorelSpace L := ⟨rfl⟩
  obtain ⟨d, hd⟩ := (isNilpotent_iff ℝ _ _).mp hnil
  obtain ⟨coeff, _, hprod⟩ := dynkin Exp hExp d hd 2
  have hmul (x y : L) : chart x * chart y =
      chart (finiteDynkinPolynomial coeff ![x, y]) := by
    simpa only [hchart, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
      List.prod_nil, mul_one, Matrix.cons_val_zero, Matrix.cons_val_succ] using
      hprod ![x, y]
  intro n b
  let e := b.equivFun.symm.toContinuousLinearEquiv
  let μ : Measure L := Measure.map e volume
  let hμ : μ.IsAddHaarMeasure := e.isAddHaarMeasure_map volume
  have hh := @dynkin_chart_map_isHaar L _
    (by change FiniteDimensional ℝ E; infer_instance) (borel L) ⟨rfl⟩ G _ _ _ _ _
    chart ((hchart 0).trans hExp.map_zero) _ coeff hmul _ hd μ hμ
  have hmap : Measure.map chart μ = Measure.map (Exp ∘ b.equivFun.symm) volume := by
    rw [Measure.map_map chart.measurable e.continuous.measurable]
    congr 1
    funext x
    exact hchart (b.equivFun.symm x)
  exact hmap ▸ hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanResidualDerivation
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual nilpotent residual derivation

Subtracting the scalar weight derivation from the Cartan adjoint action gives
one globally nilpotent derivation, not merely separate nilpotent operators on
its root spaces. Its finite exponential is therefore an actual Lie automorphism.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped DirectSum

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : TriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
/-- The scalar part of the Cartan adjoint operator on the generalized-root
sum, before exponentiation. -/
def cartanScalarOperator (h : H) : L →ₗ[ℝ] L := by
  classical
  exact (DirectSum.toModule ℝ (Weight ℝ H L) L
    (fun χ => χ h • (genWeightSpace L χ).toSubmodule.subtype)).comp
      (cartanWeightDecomposition T H).symm.toLinearMap

set_option maxHeartbeats 1000000 in
theorem cartanScalarOperator_apply_root (h : H) (χ : Weight ℝ H L) {x : L}
    (hx : x ∈ rootSpace H χ) : cartanScalarOperator T H h x = χ h • x := by
  classical
  let S := fun χ : Weight ℝ H L => (genWeightSpace L χ).toSubmodule
  have he : cartanWeightDecomposition T H
      (DirectSum.lof ℝ (Weight ℝ H L) (fun χ => S χ) χ ⟨x, hx⟩) = x :=
    DirectSum.coeLinearMap_lof S χ ⟨x, hx⟩
  change (DirectSum.toModule ℝ (Weight ℝ H L) L
    (fun χ => χ h • (S χ).subtype)) ((cartanWeightDecomposition T H).symm x) = _
  rw [← he, LinearEquiv.symm_apply_apply, DirectSum.toModule_lof]
  rw [he]
  rfl

set_option maxHeartbeats 1000000 in
theorem cartanScalarOperator_apply_genWeight (h : H) (χ : H → ℝ) {x : L}
    (hx : x ∈ genWeightSpace L χ) : cartanScalarOperator T H h x = χ h • x := by
  by_cases hχ : genWeightSpace L χ = ⊥
  · have hx0 : x = 0 := by simpa only [hχ, LieSubmodule.mem_bot] using hx
    simp [hx0]
  · exact cartanScalarOperator_apply_root T H h ⟨χ, hχ⟩ hx

set_option maxHeartbeats 1000000 in
/-- Weight addition in brackets is precisely the derivation identity for
the scalar part. -/
theorem cartanScalarOperator_leibniz (h : H) (x y : L) :
    cartanScalarOperator T H h ⁅x, y⁆ =
      ⁅x, cartanScalarOperator T H h y⁆ + ⁅cartanScalarOperator T H h x, y⁆ := by
  apply cartan_root_induction T H (x := x)
  · intro χ u hu
    apply cartan_root_induction T H (x := y)
    · intro ψ v hv
      rw [cartanScalarOperator_apply_genWeight T H h (χ + ψ)
        (lie_mem_genWeightSpace_of_mem_genWeightSpace hu hv),
        cartanScalarOperator_apply_root T H h χ hu,
        cartanScalarOperator_apply_root T H h ψ hv]
      simp only [Pi.add_apply, add_smul, lie_smul, smul_lie, add_comm]
    · simp
    · intro v w hv hw
      simp only [lie_add, map_add, hv, hw]
      abel
  · simp
  · intro u v hu hv
    simp only [add_lie, map_add, hu, hv]
    abel

set_option maxHeartbeats 1000000 in
/-- The scalar part as a genuine derivation of the ambient Lie algebra. -/
def cartanScalarDerivation (h : H) : LieDerivation ℝ L L where
  __ := cartanScalarOperator T H h
  leibniz' x y := by
    rw [cartanScalarOperator_leibniz, sub_eq_add_neg,
      ← lie_skew (cartanScalarOperator T H h x) y]

set_option maxHeartbeats 1000000 in
/-- The globally defined residual action. The library's `inner h` sends
`x` to `[x,h]`, hence the minus sign. -/
def cartanResidualDerivation (h : H) : LieDerivation ℝ L L :=
  -LieDerivation.inner ℝ L L (h : L) - cartanScalarDerivation T H h

set_option maxHeartbeats 1000000 in
theorem cartanResidualDerivation_apply_root (h : H) (χ : Weight ℝ H L) {x : L}
    (hx : x ∈ rootSpace H χ) :
    cartanResidualDerivation T H h x = ⁅(h : L), x⁆ - χ h • x := by
  change -⁅x, (h : L)⁆ - cartanScalarOperator T H h x = _
  rw [cartanScalarOperator_apply_root T H h χ hx, ← lie_skew, neg_neg]

set_option maxHeartbeats 1000000 in
theorem cartanResidualDerivation_root_mem (h : H) (χ : Weight ℝ H L) {x : L}
    (hx : x ∈ rootSpace H χ) : cartanResidualDerivation T H h x ∈ rootSpace H χ := by
  rw [cartanResidualDerivation_apply_root T H h χ hx]
  exact (rootSpace H χ).sub_mem ((rootSpace H χ).lie_mem hx) ((rootSpace H χ).smul_mem _ hx)

set_option maxHeartbeats 1000000 in
theorem cartanResidualDerivation_pow_root (h : H) (χ : Weight ℝ H L) (k : ℕ) {x : L}
    (hx : x ∈ rootSpace H χ) :
    ((cartanResidualDerivation T H h).toLinearMap ^ k) x =
      ((ad ℝ L h - χ h • 1) ^ k) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply]
    change ((cartanResidualDerivation T H h).toLinearMap ^ k)
      (cartanResidualDerivation T H h x) = _
    rw [ih (cartanResidualDerivation_root_mem T H h χ hx),
      cartanResidualDerivation_apply_root T H h χ hx,
      pow_succ, Module.End.mul_apply]
    rfl

set_option maxHeartbeats 1000000 in
/-- The ambient dimension is a simultaneous nilpotence bound on every root. -/
theorem cartanResidualDerivation_pow_eq_zero (h : H) :
    (cartanResidualDerivation T H h).toLinearMap ^ finrank ℝ L = 0 := by
  apply LinearMap.ext
  intro x
  change ((cartanResidualDerivation T H h).toLinearMap ^ finrank ℝ L) x = 0
  apply cartan_root_induction T H (x := x)
  · intro χ v hv
    rw [cartanResidualDerivation_pow_root T H h χ (finrank ℝ L) hv]
    have he := genWeightSpace_le_genWeightSpaceOf L h (χ : H → ℝ) hv
    change v ∈ (ad ℝ L h).maxGenEigenspace (χ h) at he
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
      Module.End.genEigenspace_nat] at he
    exact he
  · simp
  · intro u v hu hv
    rw [map_add, hu, hv, add_zero]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConeIdealInnerHaar
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One ideal Haar measure for both boxes and ambient conjugation -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra MeasureTheory
open scoped Manifold ENNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

local instance innerHaarNormedAddCommGroup : NormedAddCommGroup (cartanRootIdeal H) :=
  NormedAddCommGroup.induced _ _ (finBasis ℝ (cartanRootIdeal H)).equivFun.toLinearMap
    (finBasis ℝ (cartanRootIdeal H)).equivFun.injective
local instance innerHaarNormedSpace : NormedSpace ℝ (cartanRootIdeal H) :=
  NormedSpace.induced ℝ _ _ (finBasis ℝ (cartanRootIdeal H)).equivFun.toLinearMap

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ConeKernelHaar
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugation-invariant Haar measure on the actual cone kernel -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra MeasureTheory
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

local instance kernelHaarNormedAddCommGroup : NormedAddCommGroup (cartanRootIdeal H) :=
  NormedAddCommGroup.induced _ _ (finBasis ℝ (cartanRootIdeal H)).equivFun.toLinearMap
    (finBasis ℝ (cartanRootIdeal H)).equivFun.injective
local instance kernelHaarNormedSpace : NormedSpace ℝ (cartanRootIdeal H) :=
  NormedSpace.induced ℝ _ _ (finBasis ℝ (cartanRootIdeal H)).equivFun.toLinearMap

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialRepresentationInput
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential compatibility in the published faithful realization

Onshuus–Post (2022), Proposition 2.4 and proof, give a faithful inducing
linear Lie realization of a simply connected real triangular group.
Lee, *Introduction to Smooth Manifolds*, second edition (2013), Theorem 8.44
(p.195) and Proposition 20.8(g) (p.520), give its Lie algebra map and
exponential compatibility. Only these properties are retained below.

https://doi.org/10.1112/blms.12574
https://doi.org/10.1007/978-1-4419-9982-5

The action and all bounds remain proved consequences, not part of the input.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]

/-- Faithful linear realization with its intrinsic exponential identity.
No metric distortion estimate is included. -/
def ExponentialLinearRealizationInput [SimplyConnectedSpace G] : Prop :=
  (∃ a, Nonempty (TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)) →
    ∀ (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G), IsGroupExponential Exp →
      ∃ m : ℕ, 0 < m ∧ ∃ (ρ : G →* (Matrix (Fin m) (Fin m) ℝ)ˣ)
        (j : GroupLieAlgebra (𝓘(ℝ, EG)) G →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ),
        Topology.IsInducing (fun g => (ρ g : Matrix (Fin m) (Fin m) ℝ)) ∧
        ∀ x, ρ (Exp x) = algebraExpUnit (j x)

open Module LieAlgebra LieModule

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentPublishedInputs
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nilpotent published-input family used by the Cartan construction

The finite BCH expansion follows Baudoin (2004), Appendix B.5--B.6.
The intrinsic adjoint calculation and integration into arbitrary Lie groups
give model existence, global coordinates, integration, and exponential
Haar compatibility.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

structure NilpotentPublishedInputs : Prop where
  dynkin : ∀ (L : Type) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    (N : NilpotentLieModel L), NilpotentDynkinExpansionInput N.modelSpace N.carrier

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexCartanRotations
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rotations on complex Cartan weight spaces

The imaginary parts of the generalized weights define genuine Lie algebra
automorphisms. Their coefficient vectors lie in a fixed compact torus. These
are the rotations to be removed in the real-triangulable model construction.
-/

noncomputable section
namespace PolycyclicRecognition.ComplexCartan

open LieAlgebra LieModule Module
open scoped DirectSum

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

set_option maxHeartbeats 1000000 in
def rotationLinear (h : H) : L →ₗ[ℂ] L := weightOperator H (fun χ => phase H h χ)

set_option maxHeartbeats 1000000 in
theorem rotationLinear_apply (h : H) (χ : Weight ℂ H L) {x : L}
    (hx : x ∈ genWeightSpace L χ) : rotationLinear H h x = phase H h χ • x :=
  weightOperator_apply H _ χ hx

set_option maxHeartbeats 1000000 in
theorem rotationLinear_apply_genWeight (h : H) (χ : H → ℂ) {x : L}
    (hx : x ∈ genWeightSpace L χ) : rotationLinear H h x = phase H h χ • x := by
  by_cases hχ : genWeightSpace L χ = ⊥
  · have hx0 : x = 0 := by simpa only [hχ, LieSubmodule.mem_bot] using hx
    simp [hx0]
  · exact rotationLinear_apply H h ⟨χ, hχ⟩ hx

set_option maxHeartbeats 1000000 in
theorem rotationLinear_map_lie (h : H) (x y : L) :
    rotationLinear H h ⁅x, y⁆ = ⁅rotationLinear H h x, rotationLinear H h y⁆ := by
  apply root_induction H (x := x)
  · intro χ u hu
    apply root_induction H (x := y)
    · intro ψ v hv
      rw [rotationLinear_apply_genWeight H h (χ + ψ)
        (lie_mem_genWeightSpace_of_mem_genWeightSpace hu hv),
        rotationLinear_apply H h χ hu, rotationLinear_apply H h ψ hv,
        phase_add_weight]
      simp only [lie_smul, smul_lie, smul_smul, mul_comm]
    · simp
    · intro v w hv hw
      simp only [lie_add, map_add, hv, hw]
  · simp
  · intro u v hu hv
    simp only [add_lie, map_add, hu, hv]

set_option maxHeartbeats 1000000 in
@[simp] theorem rotationLinear_add_apply (h k : H) (x : L) :
    rotationLinear H (h + k) x = rotationLinear H h (rotationLinear H k x) := by
  apply root_induction H (x := x)
  · intro χ u hu
    rw [rotationLinear_apply H (h + k) χ hu, rotationLinear_apply H k χ hu,
      map_smul, rotationLinear_apply H h χ hu, phase_add, smul_smul, mul_comm]
  · simp
  · intro u v hu hv
    simp only [map_add, hu, hv]

set_option maxHeartbeats 1000000 in
@[simp] theorem rotationLinear_zero_apply (x : L) : rotationLinear H 0 x = x := by
  apply root_induction H (x := x)
  · intro χ u hu
    rw [rotationLinear_apply H 0 χ hu, phase_zero, one_smul]
  · simp
  · intro u v hu hv
    simp only [map_add, hu, hv]

end PolycyclicRecognition.ComplexCartan

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexRotationTorus
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.realTorusOperator_complexify
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compact group containing the Cartan rotations

Diagonal unit scalars are invertible on the generalized weight decomposition.
The equations for preserving the bracket and fixing the Cartan algebra cut out
an actual closed subgroup of a finite torus, giving a compact action.
-/

noncomputable section
namespace PolycyclicRecognition.ComplexCartan

open LieAlgebra LieModule Module Set

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra]

/-- The genuine Cartan rotations belong to this subgroup. -/
def phaseVector (h : H) : rotationTorus H := by
  let z : Weight ℂ H L → Circle := fun χ => Circle.exp (χ h).im
  have he : torusOperator H z = rotationLinear H h := by
    apply LinearMap.ext
    intro x
    rfl
  refine ⟨z, ?_, ?_⟩
  · intro x y
    rw [he]
    exact rotationLinear_map_lie H h x y
  · intro k
    rw [he, rotationLinear_apply_genWeight H h 0]
    · simp [phase]
    · change (k : L) ∈ rootSpace H 0
      rw [rootSpace_zero_eq]
      exact k.property

end PolycyclicRecognition.ComplexCartan

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RealTorusAction
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compact rotational group acts on the real Lie algebra -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

theorem realTorusOperator_lie (z : realRotationTorus L H) (x y : L) :
    realTorusOperator L H z ⁅x, y⁆ = ⁅realTorusOperator L H z x, realTorusOperator L H z y⁆ := by
  apply complexificationLieHom_injective L
  rw [LieHom.map_lie]
  change (1 : ℂ) ⊗ₜ[ℝ] _ = ⁅(1 : ℂ) ⊗ₜ[ℝ] _, (1 : ℂ) ⊗ₜ[ℝ] _⁆
  rw [realTorusOperator_complexify, realTorusOperator_complexify, realTorusOperator_complexify]
  simpa only [LieAlgebra.ExtendScalars.bracket_tmul, one_mul] using
    z.val.property.1 ((1 : ℂ) ⊗ₜ[ℝ] x) ((1 : ℂ) ⊗ₜ[ℝ] y)

/-- Actual real Lie automorphisms, indexed by the compact torus. -/
def realTorusAutomorphism (z : realRotationTorus L H) : L ≃ₗ⁅ℝ⁆ L where
  toFun := realTorusOperator L H z
  map_add' := (realTorusOperator L H z).map_add
  map_smul' := (realTorusOperator L H z).map_smul
  invFun := realTorusOperator L H z⁻¹
  left_inv x := by rw [← realTorusOperator_mul, inv_mul_cancel, realTorusOperator_one]
  right_inv x := by rw [← realTorusOperator_mul, mul_inv_cancel, realTorusOperator_one]
  map_lie' := fun {x y} => realTorusOperator_lie L H z x y

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_TemplateSupportDirections
attribute [-instance] _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponents of a finite family of actual support positions -/

namespace PolycyclicRecognition.CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

/-- Each generator uses its own prescribed supporting Cartan position. -/
def templateSupportExponent (v : Fin M.letterCount → H) (i : Fin M.letterCount) : ℝ :=
  M.weight i (v i)

end PolycyclicRecognition.CartanWordModel

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSupportLegs
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Support legs in the actual Cartan subgroup

The canonical height section gives a one-parameter subgroup realizing any
height displacement. Its continuity follows from the published faithful
exponential representation, and its height traces the exact affine segment.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra
open scoped Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)

set_option maxHeartbeats 1000000 in
omit [IsIsometricSMul G G] in
include T hExp in
/-- Continuity of every actual exponential one-parameter subgroup. -/
theorem continuous_exp_line_of_published_realization
    [SimplyConnectedSpace G]
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (x : GroupLieAlgebra (𝓘(ℝ, EG)) G) : Continuous (fun t : ℝ => Exp (t • x)) := by
  obtain ⟨m, hm, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ Exp hExp
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  apply hind.continuous_iff.mpr
  change Continuous (fun t : ℝ => (ρ (Exp (t • x)) : Matrix (Fin m) (Fin m) ℝ))
  simp_rw [hmatch, map_smul]
  exact Units.continuous_val.comp
    (algebraExpUnit_continuous.comp (continuous_id.smul continuous_const))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanDirectionalVisits
attribute [-instance] _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Visits along the prescribed horizontal directions

The direction of each leg is retained, so its profile is evaluated along
the original horizontal flow. Polynomial pivot coordinates give logarithmic
switch diameter at the chosen supporting endpoint.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra
open scoped Manifold BigOperators

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))

set_option maxHeartbeats 1000000 in
/-- The outward-switch-return path using an explicitly prescribed Cartan direction. -/
def directionalVisitPath (v : H) (i : Fin M.letterCount)
    (n : G) (h₀ : H) (r b : ℝ) :
    Path (n * Exp h₀) (n * Exp (b • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * Exp h₀) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  exact supportVisitPath (fun t => Exp (t • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (continuous_exp_line_of_published_realization T Exp hExp realize v)
    (by simp [hExp.map_zero])
    (fun t => Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (continuous_exp_line_of_published_realization T Exp hExp realize (M.letter i))
    (by simp [hExp.map_zero]) n (Exp h₀) r b

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPolarProbeTemplates
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual polar-template widths for the three probe boxes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Set

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- Pull a cone of height functionals back to the actual Cartan weights. -/
def heightConePreimage (K : ProperCone ℝ (StrongDual ℝ W)) : Set (H →ₗ[ℝ] ℝ) :=
  {χ | ((χ.comp (cartanHeightSection T H)).comp eW.symm.toLinearMap).toContinuousLinearMap ∈ K}

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanPolarConeKernel
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the polar cone vertex without changing the mixed ideal

The polar template uses a closed cone containing zero. The cone quotient
must kill the zero generalized weight space to descend the overlapping
Cartan factors. Salience and the nonzero generator weights supply this
bridge for the same mixed ideal.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace CartanWordModel

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
/-- Pullback cone with its zero height functional removed. -/
def positiveHeightConePreimage (K : ProperCone ℝ (StrongDual ℝ W)) : Set (H →ₗ[ℝ] ℝ) :=
  {χ | let f := ((χ.comp (cartanHeightSection T H)).comp
      eW.symm.toLinearMap).toContinuousLinearMap
    f ∈ K ∧ f ≠ 0}

end CartanWordModel
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSampledVisits
attribute [-instance] _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Support visits for the actual exponentially scaled root samples -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra
open scoped Manifold BigOperators

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))

set_option maxHeartbeats 1000000 in
/-- The root curve uses the normalized interval amplitude. -/
def sampledDirectionalVisitPath (v : H) (i : Fin M.letterCount)
    (n : G) (h₀ : H) (r s b : ℝ) :
    Path (n * Exp h₀)
      (n * Exp ((b * Real.exp (r * s)) •
        (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * Exp h₀) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let d := fun t : ℝ => Exp (t • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  let f := fun t : ℝ => Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  have hd := continuous_exp_line_of_published_realization T Exp hExp realize v
  have hf := continuous_exp_line_of_published_realization T Exp hExp realize (M.letter i)
  exact supportVisitPath d hd (by simp [d, hExp.map_zero])
    (fun t => f (t * Real.exp (r * s))) (hf.comp (continuous_id.mul_const _))
    (by simp [f, hExp.map_zero]) n (Exp h₀) r b

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSegmentVisits
attribute [-instance] _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cartan segment visits for an arbitrary controlled homomorphism

The support direction is chosen in the actual Cartan algebra, before any
factorization of the homomorphism through canonical height is known.
The resulting path stays exactly over the segment of its two values.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold BigOperators

section Directions

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

set_option maxHeartbeats 1000000 in
def segmentSupportDirection (v : H) (i : Fin M.letterCount) : H :=
  if 0 ≤ M.weight i v then v else 0

set_option maxHeartbeats 1000000 in
def segmentSupportExponent (v : H) (i : Fin M.letterCount) : ℝ :=
  max 0 (M.weight i v)

end Directions

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
  {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)

set_option maxHeartbeats 1000000 in
/-- The specified segment visit, retained for measurable path sampling. -/
def segmentVisitPath (v : H) (i : Fin M.letterCount) (n : G) (r b : ℝ) :
    Path (n * 1) (n * Exp (b • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * 1) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let δ := (M.segmentSupportDirection v i : GroupLieAlgebra (𝓘(ℝ, EG)) G)
  exact supportVisitPath (fun t => Exp (t • δ))
    (continuous_exp_line_of_published_realization T Exp hExp realize δ)
    (by simp [hExp.map_zero])
    (fun t => Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (continuous_exp_line_of_published_realization T Exp hExp realize _)
    (by simp [hExp.map_zero]) n 1 r b

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanSegmentWordPath
attribute [-instance] _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Specified segment paths for continuously varying words

The exponentially rescaled amplitudes are evaluated along the previously
constructed segment visits. This retains both measurable samples and the
uniform metric bounds needed for endpoint integration.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))

set_option maxHeartbeats 1000000 in
def segmentScaledWord (v : H) (r : ℝ) (u : List (Fin M.letterCount × ℝ)) :
    List (Fin M.letterCount × ℝ) :=
  u.map (fun z => (z.1, z.2 * Real.exp (r * M.segmentSupportExponent v z.1)))

set_option maxHeartbeats 1000000 in
def segmentWordPath (v : H) (r : ℝ) (u : List (Fin M.letterCount × ℝ)) :
    Path (1 : G) ((M.segmentScaledWord v r u).map
      (fun z => Exp (z.2 • (M.letter z.1 : GroupLieAlgebra (𝓘(ℝ, EG)) G)))).prod := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let d (i : Fin M.letterCount) (t : ℝ) :=
    Exp (t • (M.segmentSupportDirection v i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  let f (i : Fin M.letterCount) (t : ℝ) :=
    Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  have hd i : Continuous (d i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hf i : Continuous (f i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hd₀ i : d i 0 = 1 := by simp [d, hExp.map_zero]
  have hf₀ i : f i 0 = 1 := by simp [f, hExp.map_zero]
  exact (supportWordPath d f hd hf hd₀ hf₀ 1 r (M.segmentScaledWord v r u) 1).cast
    (by simp) (by simp [indexedWordProduct, f])

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanTemplateVisits
attribute [-instance] _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cartan support visits for finitely many prescribed template directions

The directions are actual Cartan vectors. A convex target containing their
images contains every support path, including the short root switches.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold BigOperators

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
  {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)

set_option maxHeartbeats 1000000 in
/-- The specified support visit, retained for measurable path sampling. -/
def templateVisitPath (v : Fin M.letterCount → H) (i : Fin M.letterCount) (n : G) (r b : ℝ) :
    Path (n * 1) (n * Exp (b • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * 1) := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let δ := (v i : GroupLieAlgebra (𝓘(ℝ, EG)) G)
  exact supportVisitPath (fun t => Exp (t • δ))
    (continuous_exp_line_of_published_realization T Exp hExp realize δ)
    (by simp [hExp.map_zero])
    (fun t => Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (continuous_exp_line_of_published_realization T Exp hExp realize _)
    (by simp [hExp.map_zero]) n 1 r b

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanTemplateWordPath
attribute [-instance] _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Specified template paths for continuously varying words

The exponentially rescaled amplitudes are evaluated along the previously
constructed template visits. This retains both measurable samples and the
uniform metric bounds needed for endpoint integration.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))

set_option maxHeartbeats 1000000 in
def templateScaledWord (v : Fin M.letterCount → H) (r : ℝ) (u : List (Fin M.letterCount × ℝ)) :
    List (Fin M.letterCount × ℝ) :=
  u.map (fun z => (z.1, z.2 * Real.exp (r * M.weight z.1 (v z.1))))

set_option maxHeartbeats 1000000 in
def templateWordPath (v : Fin M.letterCount → H) (r : ℝ) (u : List (Fin M.letterCount × ℝ)) :
    Path (1 : G) ((M.templateScaledWord v r u).map
      (fun z => Exp (z.2 • (M.letter z.1 : GroupLieAlgebra (𝓘(ℝ, EG)) G)))).prod := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let d (i : Fin M.letterCount) (t : ℝ) :=
    Exp (t • (v i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  let f (i : Fin M.letterCount) (t : ℝ) :=
    Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  have hd i : Continuous (d i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hf i : Continuous (f i) := continuous_exp_line_of_published_realization T Exp hExp realize _
  have hd₀ i : d i 0 = 1 := by simp [d, hExp.map_zero]
  have hf₀ i : f i 0 = 1 := by simp [f, hExp.map_zero]
  exact (supportWordPath d f hd hf hd₀ hf₀ 1 r (M.templateScaledWord v r u) 1).cast
    (by simp) (by simp [indexedWordProduct, f])

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexAdjointKernel
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.ComplexTriangularAdjoint.complexWeightMap_one_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nilpotent kernel of the complex adjoint weights

Complex weights retain rotational directions. Their common real kernel is
nilpotent by triangular matrices, faithful scalar extension, and Engel's theorem.
-/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}

namespace ComplexTriangularAdjoint
variable (T : ComplexTriangularAdjoint L n)

theorem matrix_nilpotent (x : L) (hx : x ∈ T.kernelIdeal) :
    IsNilpotent (complexifiedAdjointMatrix L T.basis x) := by
  let A := complexifiedAdjointMatrix L T.basis x
  have hz (i : Fin n) : A i i = 0 := congrFun hx i
  have hp : A.charpoly = Polynomial.X ^ n := by
    rw [Matrix.charpoly_of_isUpperTriangular A (T.upper _)]
    simp [hz]
  refine ⟨n, ?_⟩
  have h := Matrix.aeval_self_charpoly A
  simpa only [hp, map_pow, Polynomial.aeval_X] using h

/-- Vanishing complex weights force the original real adjoint operator to be nilpotent. -/
theorem ad_nilpotent (x : L) (hx : x ∈ T.kernelIdeal) :
    IsNilpotent (LieAlgebra.ad ℝ L x) := by
  obtain ⟨k, hk⟩ := T.matrix_nilpotent x hx
  let C := ℂ ⊗[ℝ] L
  let j := complexificationLieHom L
  let D := LieAlgebra.ad ℂ C (j x)
  have hD : D ^ k = 0 := by
    apply (LinearMap.toMatrixAlgEquiv T.basis).injective
    rw [map_pow, map_zero]
    exact hk
  have intertwine (m : ℕ) (y : L) :
      j (((LieAlgebra.ad ℝ L x) ^ m) y) = (D ^ m) (j y) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
      exact (j.map_lie x _).trans (congrArg D ih)
  refine ⟨k, ?_⟩
  ext y
  apply complexificationLieHom_injective L
  rw [intertwine, hD]
  simp [j]

/-- The common kernel is a nilpotent Lie ideal, even when weights are nonreal. -/
theorem kernelIdeal_nilpotent [FiniteDimensional ℝ L] :
    LieRing.IsNilpotent T.kernelIdeal := by
  have : LieModule.IsNilpotent T.kernelIdeal L :=
    (LieModule.isNilpotent_iff_forall' (R := ℝ)).mpr fun x =>
      T.ad_nilpotent x x.property
  exact T.kernelIdeal.incl_injective.lieModuleIsNilpotent
    (f := LieHom.id) (g := T.kernelIdeal.incl.toLinearMap) (fun _ _ => rfl)

end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ComplexNilradical
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.ComplexTriangularAdjoint.complexWeightMap_one_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The intrinsic meaning of the complex weight kernel

The common kernel consists exactly of the elements with nilpotent adjoint.
In particular it is preserved by every Lie automorphism. This identifies the
nilpotent factor without making a choice of triangular basis part of its data.
-/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}

namespace ComplexTriangularAdjoint
variable (T : ComplexTriangularAdjoint L n)

/-- Nilpotence of the real adjoint remains nilpotence after scalar extension. -/
theorem complex_ad_nilpotent (x : L) (hx : IsNilpotent (LieAlgebra.ad ℝ L x)) :
    IsNilpotent (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] L) (complexificationLieHom L x)) := by
  obtain ⟨k, hk⟩ := hx
  let j := complexificationLieHom L
  let D := LieAlgebra.ad ℂ (ℂ ⊗[ℝ] L) (j x)
  have intertwine (m : ℕ) (y : L) :
      (D ^ m) (j y) = j (((LieAlgebra.ad ℝ L x) ^ m) y) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ih]
      exact (j.map_lie x _).symm
  refine ⟨k, ?_⟩
  apply LinearMap.ext
  intro v
  induction v using OAI.tensorInductionOn with
  | tmul z y =>
    change (D ^ k) (z ⊗ₜ[ℝ] y) = 0
    have he : z ⊗ₜ[ℝ] y = z • j y := by
      change z ⊗ₜ[ℝ] y = z • ((1 : ℂ) ⊗ₜ[ℝ] y)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [he, map_smul, intertwine, hk]
    simp [j]
  | add v w hv hw => simp only [map_add, hv, hw]

/-- The nilpotent kernel is independent of the chosen complex triangular basis. -/
theorem mem_kernelIdeal_iff_ad_nilpotent (x : L) :
    x ∈ T.kernelIdeal ↔ IsNilpotent (LieAlgebra.ad ℝ L x) := by
  refine ⟨T.ad_nilpotent x, ?_⟩
  intro hx
  obtain ⟨k, hk⟩ := complex_ad_nilpotent x hx
  have hA : complexifiedAdjointMatrix L T.basis x ^ k = 0 := by
    change ((LinearMap.toMatrixAlgEquiv T.basis)
      (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] L) ((1 : ℂ) ⊗ₜ[ℝ] x))) ^ k = 0
    change (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] L) ((1 : ℂ) ⊗ₜ[ℝ] x)) ^ k = 0 at hk
    rw [← map_pow, hk, map_zero]
  ext i
  have hi := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i i) hA
  have hu : (complexifiedAdjointMatrix L T.basis x).IsUpperTriangular := T.upper _
  rw [diagonal_pow _ hu k i] at hi
  change complexifiedAdjointMatrix L T.basis x i i = 0
  exact eq_zero_of_pow_eq_zero (by simpa only [Matrix.zero_apply] using hi)

/-- Every Lie automorphism preserves this concrete nilpotent ideal. -/
theorem map_mem_kernelIdeal (f : L ≃ₗ⁅ℝ⁆ L) {x : L} (hx : x ∈ T.kernelIdeal) :
    f x ∈ T.kernelIdeal := by
  rw [T.mem_kernelIdeal_iff_ad_nilpotent] at hx ⊢
  obtain ⟨k, hk⟩ := hx
  have intertwine (m : ℕ) (y : L) :
      ((LieAlgebra.ad ℝ L (f x)) ^ m) (f y) =
        f (((LieAlgebra.ad ℝ L x) ^ m) y) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ih]
      exact (f.map_lie x _).symm
  refine ⟨k, ?_⟩
  ext y
  obtain ⟨z, rfl⟩ := f.surjective y
  change ((LieAlgebra.ad ℝ L (f x)) ^ k) (f z) = 0
  rw [intertwine, hk]
  simp

end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_DerivationFlowRepresentation
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Representing a nilpotent derivation flow by conjugation

Only the given intertwining identity is used. The target operator need not
be nilpotent outside the image of the intertwiner.
-/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

local instance derivationFlowRepresentationRat : Module ℚ L :=
  Module.compHom L (algebraMap ℚ ℝ)

local instance q145LieRatGeometryDerivationFlowRepresentation_re7aceb_1 : LieAlgebra ℚ L where
  lie_smul t x y := lie_smul (algebraMap ℚ ℝ t) x y
theorem nilpotentDerivationFlow_eq_analytic (t : ℝ) (x : L) :
    nilpotentDerivationFlow D hD t x =
      NormedSpace.exp (t • D.toLinearMap.toContinuousLinearMap) x := by
  let d := D.toLinearMap.toContinuousLinearMap
  have hd : IsNilpotent d := by
    obtain ⟨k, hk⟩ := hD
    refine ⟨k, ?_⟩
    ext y
    have he : (d ^ k).toLinearMap = D.toLinearMap ^ k :=
      map_pow ContinuousLinearMap.toLinearMapRingHom d k
    have hy := congrArg (fun f : L →ₗ[ℝ] L => f y) he
    rw [hk] at hy
    exact hy
  let : NormedAlgebra ℚ (L →L[ℝ] L) := NormedAlgebra.restrictScalars ℚ ℝ _
  rw [analytic_exp_eq_nilpotent_exp (hd.smul t)]
  have he := (hd.smul t).map_exp ContinuousLinearMap.toLinearMapRingHom
  exact (congrArg (fun f : L →ₗ[ℝ] L => f x) he).symm

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialAutomorphismTopology
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Topology of the integrated nilpotent automorphisms -/

noncomputable section
namespace PolycyclicRecognition

open LieModule
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hbij : Function.Bijective Exp)
  (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)

omit [T2Space G] in
include hchart in
theorem continuous_exponentialConjugate (F : L ≃ₗ⁅ℝ⁆ L) :
    Continuous (exponentialConjugate e Exp hbij F) := by
  let D := (e.symm.toLinearEquiv.trans F.toLinearEquiv).trans e.toLinearEquiv
  have heq : (exponentialConjugate e Exp hbij F : G → G) =
      chart ∘ D ∘ chart.symm := by
    funext g
    obtain ⟨x, rfl⟩ := (hbij.comp e.bijective).surjective g
    change exponentialConjugate e Exp hbij F (Exp (e x)) = _
    rw [exponentialConjugate_apply_exp]
    simp only [Function.comp_apply, ← hchart, chart.symm_apply_apply, D,
      LinearEquiv.trans_apply, LieEquiv.coe_toLinearEquiv]
    change chart (e (F x)) = chart (e (F (e.symm (e x))))
    rw [e.symm_apply_apply]
  rw [heq]
  exact chart.continuous.comp (D.toContinuousLinearEquiv.continuous.comp chart.symm.continuous)

/-- Both directions of exponential conjugation are continuous, and the
published finite Dynkin formula proves its multiplicativity. -/
def integrateNilpotentLieEquivContinuous
    (dynkin : NilpotentDynkinExpansionInput E G) (hExp : IsGroupExponential Exp)
    {c : ℕ} (hc : lowerCentralSeries ℝ L L c = ⊥) (F : L ≃ₗ⁅ℝ⁆ L) : G ≃ₜ* G := by
  let f := integrateNilpotentLieEquiv e Exp hbij dynkin hExp hc F
  refine { f with
    continuous_toFun := continuous_exponentialConjugate e Exp hbij chart hchart F
    continuous_invFun := ?_ }
  have heq : (f.symm : G → G) = exponentialConjugate e Exp hbij F.symm := by
    funext g
    apply f.injective
    rw [f.apply_symm_apply]
    obtain ⟨x, rfl⟩ := (hbij.comp e.bijective).surjective g
    change Exp (e x) = exponentialConjugate e Exp hbij F
      (exponentialConjugate e Exp hbij F.symm (Exp (e x)))
    rw [exponentialConjugate_apply_exp, exponentialConjugate_apply_exp, F.apply_symm_apply]
  change Continuous (f.symm : G → G)
  rw [heq]
  exact continuous_exponentialConjugate e Exp hbij chart hchart F.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_IntrinsicDerivationFlow
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotent derivation flow in any Lie group -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

theorem derivationFlow_intrinsic_adjoint
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (f : L →ₗ[ℝ] GroupLieAlgebra (𝓘(ℝ, E)) G) (u : GroupLieAlgebra (𝓘(ℝ, E)) G)
    (hf : ∀ x, f (D x) = ⁅u, f x⁆) (t : ℝ) (x : L) :
    f (nilpotentDerivationFlow D hD t x) =
      conjugationDifferentialHom (E := E) (Exp (t • u)) (f x) := by
  let fE : L →ₗ[ℝ] E := f
  rw [nilpotentDerivationFlow_eq_analytic]
  have he := exp_intertwine_apply fE.toContinuousLinearMap
    (t • D.toLinearMap.toContinuousLinearMap) (t • groupAdjointOperator (E := E) u)
    (by
      intro y
      change f (t • D y) = t • ⁅u, f y⁆
      rw [map_smul, hf]) x
  rw [← adjointLinearMap_exponential hExp u t] at he
  exact he

theorem derivationFlow_intrinsic_conjugation [T2Space G]
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (f : L →ₗ[ℝ] GroupLieAlgebra (𝓘(ℝ, E)) G) (u : GroupLieAlgebra (𝓘(ℝ, E)) G)
    (hf : ∀ x, f (D x) = ⁅u, f x⁆) (t : ℝ) (x : L) :
    Exp (f (nilpotentDerivationFlow D hD t x)) =
      Exp (t • u) * Exp (f x) * (Exp (t • u))⁻¹ := by
  rw [derivationFlow_intrinsic_adjoint D hD Exp hExp f u hf]
  exact (conjugation_exponential hExp (Exp (t • u)) (f x)).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemidirectIntegration
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.integrateNilpotentLieEquiv_apply_exp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating a codimension-one semidirect product

An equivariant homomorphism on the ideal and the complementary exponential
curve give the required homomorphism, with its actual manifold derivative.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
  (k : L →* G) (u : GroupLieAlgebra (𝓘(ℝ, E)) G)
  (hact : ∀ t x, k (nilpotentDerivationFlow D hD t x) =
    Exp (t • u) * k x * (Exp (t • u))⁻¹)

def derivationSemidirectHom :
    letI := derivationSemidirectGroup D hD
    letI : MulOneClass (L × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
    letI : One (L × ℝ) := (derivationSemidirectGroup D hD).toOne
    (L × ℝ) →* G := by
  letI := derivationSemidirectGroup D hD
  letI : MulOneClass (L × ℝ) := (derivationSemidirectGroup D hD).toMulOneClass
  letI : Mul (L × ℝ) := (derivationSemidirectGroup D hD).toMul
  letI : One (L × ℝ) := (derivationSemidirectGroup D hD).toOne
  refine { toFun := fun p => k p.1 * Exp (p.2 • u), map_one' := ?_, map_mul' := ?_ }
  · change k ((derivationSemidirectGroup D hD).one).1 *
      Exp (((derivationSemidirectGroup D hD).one).2 • u) = 1
    rw [derivationSemidirect_one]
    simp only [zero_smul, hExp.map_zero, mul_one]
    rw [← P.one_eq_zero, map_one]
  · intro x y
    change k ((derivationSemidirectGroup D hD).mul x y).1 *
      Exp (((derivationSemidirectGroup D hD).mul x y).2 • u) = _
    rw [derivationSemidirect_mul, map_mul, hact, hExp.map_add_smul]
    group

omit [LieGroup (𝓘(ℝ, E)) ⊤ G] in
@[simp] theorem derivationSemidirectHom_apply (p : L × ℝ) :
    derivationSemidirectHom D hD Exp hExp k u hact p = k p.1 * Exp (p.2 • u) := rfl

theorem contMDiff_derivationSemidirectHom
    (hk : ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, E)) ∞ k) :
    ContMDiff (𝓘(ℝ, L × ℝ)) (𝓘(ℝ, E)) ∞
      (derivationSemidirectHom D hD Exp hExp k u hact) :=
  (hk.comp contDiff_fst.contMDiff).mul
    ((hExp.contMDiff_curve u).comp contDiff_snd.contMDiff)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilradicalRotationAction
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compact rotation action on the actual nilpotent kernel -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

namespace ComplexTriangularAdjoint

/-- Restrict the real rotations to the intrinsic nilpotent adjoint kernel. -/
def nilradicalRotation (z : realRotationTorus L H) : T.kernelIdeal ≃ₗ⁅ℝ⁆ T.kernelIdeal where
  toFun x := ⟨realTorusOperator L H z x,
    T.map_mem_kernelIdeal (realTorusAutomorphism L H z) x.property⟩
  invFun x := ⟨realTorusOperator L H z⁻¹ x,
    T.map_mem_kernelIdeal (realTorusAutomorphism L H z⁻¹) x.property⟩
  left_inv x := by
    apply Subtype.ext
    exact (realTorusAutomorphism L H z).left_inv x
  right_inv x := by
    apply Subtype.ext
    exact (realTorusAutomorphism L H z).right_inv x
  map_add' x y := by apply Subtype.ext; exact (realTorusOperator L H z).map_add x y
  map_smul' r x := by apply Subtype.ext; exact (realTorusOperator L H z).map_smul r x
  map_lie' := by
    intro x y
    apply Subtype.ext
    exact realTorusOperator_lie L H z x y

end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_IntegratedNilradicalRotations
attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.ComplexTriangularAdjoint.complexWeightMap_one_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compact rotations on the closed nilpotent factor -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  (N : NilpotentLieModel T.kernelIdeal)

/-- The compact rotation on the chosen nilpotent model's tangent algebra. -/
def modelNilradicalRotation (z : realRotationTorus L H) :
    GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier ≃ₗ⁅ℝ⁆
      GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier :=
  N.equiv.symm.trans ((T.nilradicalRotation H z).trans N.equiv)

@[simp] theorem modelNilradicalRotation_apply (z : realRotationTorus L H)
    (x : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier) :
    modelNilradicalRotation T H N z x =
      N.equiv (T.nilradicalRotation H z (N.equiv.symm x)) := rfl

@[simp] theorem modelNilradicalRotation_one
    (x : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier) :
    modelNilradicalRotation T H N 1 x = x := by
  have h : T.nilradicalRotation H 1 (N.equiv.symm x) = N.equiv.symm x := by
    apply Subtype.ext
    exact realTorusOperator_one L H (N.equiv.symm x)
  rw [modelNilradicalRotation_apply, h, N.equiv.apply_symm_apply]

@[simp] theorem modelNilradicalRotation_mul (z w : realRotationTorus L H)
    (x : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier) :
    modelNilradicalRotation T H N (z * w) x =
      modelNilradicalRotation T H N z (modelNilradicalRotation T H N w x) := by
  have h : T.nilradicalRotation H (z * w) (N.equiv.symm x) =
      T.nilradicalRotation H z (T.nilradicalRotation H w (N.equiv.symm x)) := by
    apply Subtype.ext
    exact realTorusOperator_mul L H z w (N.equiv.symm x)
  simp only [modelNilradicalRotation_apply, N.equiv.symm_apply_apply, h]

/-- The transported linear representation. -/
def modelNilradicalLinearAction : realRotationTorus L H →*
    (GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier ≃ₗ[ℝ]
      GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier) where
  toFun z := (modelNilradicalRotation T H N z).toLinearEquiv
  map_one' := by ext x; exact modelNilradicalRotation_one T H N x
  map_mul' z w := by ext x; exact modelNilradicalRotation_mul T H N z w x

@[simp] theorem modelNilradicalLinearAction_apply (z : realRotationTorus L H)
    (x : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier) :
    modelNilradicalLinearAction T H N z x = modelNilradicalRotation T H N z x := rfl

end PolycyclicRecognition

end

end OAI
end


