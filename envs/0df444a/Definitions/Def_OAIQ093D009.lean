-- Prove2me | Definitions.Def_OAIQ093D009
-- name    : OAIQ093D009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T16:09:00.180183+00:00
-- url     : https://prove2.me/theorems/c39b8429-0b3a-4d69-96c5-78283d273816
-- title:
--   Definitions bundle OAIQ093D009 of the split of OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 291 declarations of OpenAI's Lean: 100 definitions, 1 inductive type or structure, 6 instances and 184 theorems. The definitions and types are `OAI.PolycyclicRecognition.CornulierTesseraModelInput`, `OAI.PolycyclicRecognition.HasSubmersiveTwoImageSubsequence`, `OAI.PolycyclicRecognition.HasSubmersiveWordSubsequence`, `OAI.PolycyclicRecognition.IntegralProjectiveTower.cohomologyEquiv`, `OAI.PolycyclicRecognition.IntegralProjectiveTower.completeCohomologyEquiv`, `OAI.PolycyclicRecognition.IntegralProjectiveTower.normalization`, `OAI.PolycyclicRecognition.LieRiemannianMetricInput`, `OAI.PolycyclicRecognition.MatrixLieDifferentialInput`, `OAI.PolycyclicRecognition.MeasuredProbeRegions`, `OAI.PolycyclicRecognition.MeasuredProbeRegions.ControlsTwoPaths`, `OAI.PolycyclicRecognition.OnshuusPostRealizationInput`, `OAI.PolycyclicRecognition.PolynomialBoundedChainPacking`, `OAI.PolycyclicRecognition.PolynomialMatrixGroup.coordinates`, `OAI.PolycyclicRecognition.ProperMinimizingMetric.toProperChainMetric`, `OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.freeChosenLift`, `OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.freeDiagram`, `OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.freeLimitGenerator`, `OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.freeModuleCocone`, `OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.freeModuleGenerator`, `OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.freeModuleInverse`, `OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.freeModuleLift`, `OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.iteratedNormalizedSyzygy`, `OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.normalizedFree`, `OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.normalizedFreeModuleBasis`, `OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.normalizedSyzygy`, `OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.transportIso`, `OAI.PolycyclicRecognition.ShiftedCompletedCohomology`, `OAI.PolycyclicRecognition.SimplyConnectedSolvableLieModel.toLCModel`, `OAI.PolycyclicRecognition.SupportDatum.supportForm`, `OAI.PolycyclicRecognition.SupportDatum.supportForms`, `OAI.PolycyclicRecognition.WordMetric.chains`, `OAI.PolycyclicRecognition.abelianDynkinCoefficients`, `OAI.PolycyclicRecognition.abelianLieModel`, `OAI.PolycyclicRecognition.adjointExponentialLinear`, `OAI.PolycyclicRecognition.adjointExponentialNormedAddCommGroup`, `OAI.PolycyclicRecognition.adjointExponentialNormedSpace`, `OAI.PolycyclicRecognition.adjointMatrixHom`, `OAI.PolycyclicRecognition.algebraGroupTangentLie`, `OAI.PolycyclicRecognition.algebraGroupTangentSpan`, `OAI.PolycyclicRecognition.alternatingCoordinateProduct` and 61 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `PolycyclicRecognition_Algebra_AbelianDynkinInput`, `PolycyclicRecognition_Algebra_AlgebraGroupTangent`, `PolycyclicRecognition_Algebra_AlternatingProductSubmersion`, `PolycyclicRecognition_Algebra_AmplitudeWordCoordinates`, `PolycyclicRecognition_Algebra_AscendingQuotientColimit`, `PolycyclicRecognition_Algebra_BooleanPartitionMaps`, `PolycyclicRecognition_Algebra_BooleanStepRing`, `PolycyclicRecognition_Algebra_CanonicalNilpotentLogarithm`, `PolycyclicRecognition_Algebra_ChartedVectorFieldBracket`, `PolycyclicRecognition_Algebra_CommonDynkinFormula`, `PolycyclicRecognition_Algebra_CommutingUnipotentLogarithm`, `PolycyclicRecognition_Algebra_CoupledBundleStates`, `PolycyclicRecognition_Algebra_DifferenceAmplitudeWord`, `PolycyclicRecognition_Algebra_FiniteLogCoefficientBound`, `PolycyclicRecognition_Algebra_GroupLikeNilpotentLogarithm`, `PolycyclicRecognition_Algebra_HomogeneousUniversalLogarithm`, `PolycyclicRecognition_Algebra_HomogeneousWordCoefficients`, `PolycyclicRecognition_Algebra_HomogeneousWordProjection`, `PolycyclicRecognition_Algebra_LocallyBoundedDerivedSeries`, `PolycyclicRecognition_Algebra_MonoidTensorCoordinates`, `PolycyclicRecognition_Algebra_NilpotentPowerSeriesEvaluation`, `PolycyclicRecognition_Algebra_NilpotentPowerSeriesSubstitution`, `PolycyclicRecognition_Algebra_NilpotentUniversalLogarithm`, `PolycyclicRecognition_Algebra_NilpotentWordEvaluation`, `PolycyclicRecognition_Algebra_NormalizedFreeColimit`, `PolycyclicRecognition_Algebra_NormalizedFreeRepresentation`, `PolycyclicRecognition_Algebra_NormalizedGroupLaws`, `PolycyclicRecognition_Algebra_NormalizedIdentityClass`, `PolycyclicRecognition_Algebra_PolynomialBilinearWords`, `PolycyclicRecognition_Algebra_PolynomialMatrixGroup`, `PolycyclicRecognition_Algebra_PolynomialOneParameterNilpotent`, `PolycyclicRecognition_Algebra_PresentationKernelMap`, `PolycyclicRecognition_Algebra_PrimitiveWordProjection`, `PolycyclicRecognition_Algebra_RationalPowerSeriesHom`, `PolycyclicRecognition_Algebra_RationalUniversalLogarithm`, `PolycyclicRecognition_Algebra_RealTorusContinuity`, `PolycyclicRecognition_Algebra_RegularDualPairing`, `PolycyclicRecognition_Algebra_RegularFreeEvaluation`, `PolycyclicRecognition_Algebra_RegularPairingNaturality`, `PolycyclicRecognition_Algebra_RescaledSubmersiveScheme`, `PolycyclicRecognition_Algebra_TruncatedPrimitiveCoefficients`, `PolycyclicRecognition_Algebra_TwoImageLimits`, `PolycyclicRecognition_Algebra_UniversalCoefficientStability`, `PolycyclicRecognition_Algebra_UniversalDynkinTruncation`, `PolycyclicRecognition_Algebra_UniversalLogarithmWordCoefficients`, `PolycyclicRecognition_Algebra_WordPowerCoefficientBound`, `PolycyclicRecognition_Algebra_WordTensorConvolution`, `PolycyclicRecognition_Analysis_AmenableCorrection`, `PolycyclicRecognition_Analysis_BoundedPathGrowth`, `PolycyclicRecognition_Analysis_CompactExtensionModels`, `PolycyclicRecognition_Analysis_CompactProbeLift`, `PolycyclicRecognition_Analysis_ExtensionInvariantMean`, `PolycyclicRecognition_Analysis_FiniteIntegralRepresentations`, `PolycyclicRecognition_Analysis_FiniteWordMetric`, `PolycyclicRecognition_Analysis_IntegralFinsuppFunctor`, `PolycyclicRecognition_Analysis_MeanSubgroup`, `PolycyclicRecognition_Analysis_MeasuredProbeRegions`, `PolycyclicRecognition_Analysis_MinimizingMetricChains`, `PolycyclicRecognition_Analysis_OneParameterIntegralCurve`, `PolycyclicRecognition_Analysis_SupportNorm`, `PolycyclicRecognition_Analysis_SupportPolytope`, `PolycyclicRecognition_Analysis_WordChartScaleTransition`, `PolycyclicRecognition_Finiteness_BilateralCochainShift`, `PolycyclicRecognition_Finiteness_BooleanStepProjective`, `PolycyclicRecognition_Finiteness_CompletedCohomology`, `PolycyclicRecognition_Finiteness_CompletedIdentity`, `PolycyclicRecognition_Finiteness_FiniteProjectivePresentations`, `PolycyclicRecognition_Finiteness_InductionExhaustionVanishing`, `PolycyclicRecognition_Finiteness_IntegralProjectiveTower`, `PolycyclicRecognition_Finiteness_NormalizedProjectiveResolution`, `PolycyclicRecognition_Finiteness_NormalizedProjectiveTower`, `PolycyclicRecognition_Finiteness_NormalizedResolutionSyzygies`, `PolycyclicRecognition_Finiteness_NormalizedStableSyzygyMap`, `PolycyclicRecognition_Finiteness_NormalizedSyzygyColimit`, `PolycyclicRecognition_Finiteness_NormalizedSyzygyFunctor`, `PolycyclicRecognition_Finiteness_ProjectiveKernelStableMap`, `PolycyclicRecognition_Finiteness_ProjectiveTowerCohomology`, `PolycyclicRecognition_Finiteness_ProjectiveTowerComparison`, `PolycyclicRecognition_Finiteness_ShiftedCompletedCohomology`, `PolycyclicRecognition_Geometry_AbelianLieModel`, `PolycyclicRecognition_Geometry_AdjointExponentialRepresentation`, `PolycyclicRecognition_Geometry_AdjointMatrixHeight`, `PolycyclicRecognition_Geometry_AlgebraExponentialNaturality`, `PolycyclicRecognition_Geometry_AlgebraHomLieDifferential`, `PolycyclicRecognition_Geometry_AlgebraTangentLie`, `PolycyclicRecognition_Geometry_AnalyticDerivationFlow`, `PolycyclicRecognition_Geometry_BoundedAssociativeBCH`, `PolycyclicRecognition_Geometry_CompactLieLaws`, `PolycyclicRecognition_Geometry_ExponentialProductChart`, `PolycyclicRecognition_Geometry_ExponentialSmoothHom`, `PolycyclicRecognition_Geometry_FaithfulDifferential`, `PolycyclicRecognition_Geometry_FiniteExponentialLogarithm`, `PolycyclicRecognition_Geometry_IntrinsicAdjointHeight`, `PolycyclicRecognition_Geometry_LieIntegrationNaturality`, `PolycyclicRecognition_Geometry_ManifoldRelatedBracket`, `PolycyclicRecognition_Geometry_MinimizingLieMetric`, `PolycyclicRecognition_Geometry_MovingBaseFlow`, `PolycyclicRecognition_Geometry_NilpotentDerivationFlowDerivative`, `PolycyclicRecognition_Geometry_NormalizedExponentialLaws`, `PolycyclicRecognition_Geometry_PrimitiveNilpotentExponential`, `PolycyclicRecognition_Geometry_ProductLieAlgebra`, `PolycyclicRecognition_Geometry_RiemannianExponentialInputs`, `PolycyclicRecognition_Geometry_ScalarNilpotentExponential`, `PolycyclicRecognition_Geometry_SemidirectProductTopology`, `PolycyclicRecognition_Geometry_SmoothHomLieDifferential`, `PolycyclicRecognition_Geometry_TriangulableLieModel`, `PolycyclicRecognition_Geometry_TriangularLieDifferential`, `PolycyclicRecognition_Geometry_TriangularMatrixExponential`, `PolycyclicRecognition_Geometry_TriangularRealizationInput`, `PolycyclicRecognition_Geometry_TruncatedWordExponential`, `PolycyclicRecognition_Geometry_UniversalBCHCoefficientBound`, `PolycyclicRecognition_Geometry_WeightedWordComponents`, `PolycyclicRecognition_Geometry_WeightedWordLogarithm`.
--
--   **Imports.** It imports the published bundle `Def_PolycyclicRecognition`; the bundles `OAIQ093D000`, `OAIQ093D001`, `OAIQ093D002`, `OAIQ093D003` and `OAIQ093D004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ093D012`, `OAIQ093D014` and `OAIQ093D015`; the statements `OAI_PolycyclicRecognition_CartanWordModel_exists_coupled_profile_comparison_region`, `OAI.PolycyclicRecognition.CartanWordModel.exists_source_target_comparison_schemes`, `OAI.PolycyclicRecognition.CartanWordModel.source_target_product_exponent_le`, `OAI.PolycyclicRecognition.CartanWordModel.templateSupport_le_of_recurrent_segment_cells_sequence`, `OAI.PolycyclicRecognition.cornulierTesseraModelInput` and `OAI.PolycyclicRecognition.polynomialBoundedChainPacking_intrinsic`.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D000
import Definitions.Def_OAIQ093D001
import Definitions.Def_OAIQ093D002
import Definitions.Def_OAIQ093D003
import Definitions.Def_OAIQ093D004

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_OneParameterIntegralCurve
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering a one-parameter subgroup from its tangent vector -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

theorem oneParameter_eq_groupExponential [T2Space G]
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {γ : ℝ → G} (hzero : γ 0 = 1) (hmul : ∀ s t, γ (s + t) = γ s * γ t)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G)
    (hd : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ 0
      ((ContinuousLinearMap.id ℝ ℝ).smulRight v)) :
    ∀ t, γ t = Exp (t • v) := by
  have hh := invariant_integralCurve_unique (oneParameter_isMIntegralCurve hzero hmul v hd)
    (hExp.isMIntegralCurve v) (by simpa only [zero_smul, hExp.map_zero] using hzero)
  exact congrFun hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AbelianDynkinInput
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite BCH for commutative Lie groups -/

noncomputable section
namespace PolycyclicRecognition

open LieModule
open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [CommGroup G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

theorem IsGroupExponential.map_add_of_comm
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (x y : GroupLieAlgebra (𝓘(ℝ, E)) G) : Exp (x + y) = Exp x * Exp y := by
  let γ : ℝ → G := fun t => Exp (t • x) * Exp (t • y)
  have hzero : γ 0 = 1 := by simp [γ, hExp.map_zero]
  have hmul : ∀ s t, γ (s + t) = γ s * γ t := by
    intro s t
    dsimp [γ]
    rw [hExp.map_add_smul, hExp.map_add_smul]
    ac_rfl
  have hd : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ 0
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (x + y)) := by
    have hh := HasMFDerivAt.mul_at_one (hExp.hasMFDerivAt_zero x) (hExp.hasMFDerivAt_zero y)
      (by simp [hExp.map_zero]) (by simp [hExp.map_zero])
    apply hh.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro r
    let t : ℝ := r
    change t • x + t • y = t • (x + y)
    exact (smul_add t x y).symm
  have hh := oneParameter_eq_groupExponential hExp hzero hmul (x + y) hd 1
  simpa only [γ, one_smul] using hh.symm

theorem IsGroupExponential.prod_eq_exp_sum_of_comm
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {n : ℕ} (X : Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G) :
    (List.ofFn (fun i => Exp (X i))).prod = Exp (∑ i, X i) := by
  induction n with
  | zero => simp [hExp.map_zero]
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, ih, Fin.sum_univ_succ, hExp.map_add_of_comm]

/-- Only the degree-one coefficients are nonzero. -/
def abelianDynkinCoefficients (c n : ℕ) : DynkinCoefficients c n :=
  fun d _ => if d.val = 0 then 1 else 0

theorem abelianDynkinCoefficients_bound (c n : ℕ) (d : Fin c)
    (w : Fin (d.val + 1) → Fin n) : |abelianDynkinCoefficients c n d w| ≤ (2 : ℝ) ^ c := by
  dsimp [abelianDynkinCoefficients]
  split_ifs
  · simpa only [abs_one] using (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : 1 ≤ (2 : ℝ) ^ c)
  · simp only [abs_zero] <;> positivity

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AlgebraGroupTangent
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Infinitesimal commutators of matrix groups

The finite-dimensional span of derivatives of curves in a subgroup records
its infinitesimal action. Differentiating group commutators twice puts the
algebra commutator into the tangent span of the derived subgroup.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Topology commutatorElement
open Filter

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [FiniteDimensional ℝ A] [CompleteSpace A]

/-- The finite-dimensional linear span of the actual curve derivatives. -/
def algebraGroupTangentSpan (D : Subgroup Aˣ) : Submodule ℝ A :=
  Submodule.span ℝ {X | AlgebraGroupTangentVector D X}

omit [FiniteDimensional ℝ A] [CompleteSpace A] in
theorem algebraGroupTangentSpan_mono {D F : Subgroup Aˣ} (hDF : D ≤ F) :
    algebraGroupTangentSpan D ≤ algebraGroupTangentSpan F := by
  apply Submodule.span_mono
  rintro X ⟨c, hc, h0, hd⟩
  exact ⟨c, fun t => hDF (hc t), h0, hd⟩

omit [FiniteDimensional ℝ A] in
/-- Conjugation by one group element gives a tangent of the group commutator
subgroup after subtracting the original tangent. -/
theorem conjugation_difference_tangent {D : Subgroup Aˣ} {u : Aˣ} (hu : u ∈ D)
    {Y : A} (hY : AlgebraGroupTangentVector D Y) :
    AlgebraGroupTangentVector ⁅D, D⁆ ((u : A) * Y * (u⁻¹ : Aˣ) - Y) := by
  obtain ⟨c, hc, h0, hd⟩ := hY
  refine ⟨fun t => ⁅u, c t⁆, fun t => Subgroup.commutator_mem_commutator hu (hc t), ?_, ?_⟩
  · simp only [h0, commutatorElement_def, mul_one, mul_inv_cancel]
  · have hi := hasDerivAt_units_inverse_at_one h0 hd
    have h := (((hasDerivAt_const 0 (u : A)).mul hd).mul
      (hasDerivAt_const (0 : ℝ) ((u⁻¹ : Aˣ) : A))).mul hi
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    simp [h0, sub_eq_add_neg]

/-- Two actual tangents have an algebra commutator tangent to the derived
subgroup. The second differentiation uses closedness of the finite span. -/
theorem commutator_mem_derived_tangentSpan {D : Subgroup Aˣ} {X Y : A}
    (hX : AlgebraGroupTangentVector D X) (hY : AlgebraGroupTangentVector D Y) :
    X * Y - Y * X ∈ algebraGroupTangentSpan ⁅D, D⁆ := by
  obtain ⟨c, hc, h0, hd⟩ := hX
  have hi := hasDerivAt_units_inverse_at_one h0 hd
  have hdiff : HasDerivAt (fun t => (c t : A) * Y * ((c t)⁻¹ : Aˣ) - Y)
      (X * Y - Y * X) 0 := by
    have h := ((hd.mul_const Y).mul hi).sub_const Y
    simpa [h0, sub_eq_add_neg] using h
  apply submodule_mem_of_hasDerivAt (algebraGroupTangentSpan ⁅D, D⁆) hdiff
  intro t
  exact Submodule.subset_span (conjugation_difference_tangent (hc t) hY)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CompactLieLaws
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact families of normalized Lie laws

Bounded brackets and generators satisfying fixed word-basis identities form
a compact parameter set. Limits retain the Lie identities and the exact word
normalizations, so bracket generation cannot disappear in a limit.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric

variable {V I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable [FiniteDimensional ℝ V] [Fintype I]

/-- Parameter data for a fixed normalization by bracket words. -/
def normalizedLieParameters (w : J → FreeMagma I) (b : J → V) (C : ℝ) :
    Set ((V →L[ℝ] V →L[ℝ] V) × (I → V)) :=
  {p | ‖p.1‖ ≤ C ∧ ‖p.2‖ ≤ C ∧ IsLieBracket p.1 ∧
    ∀ j, evalBilinearWord p.1 p.2 (w j) = b j}

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportNorm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The norm obtained from weighted nilpotent boxes

For a bracket-word basis, each generator occurs with a positive integral
multiplicity. Unimodularity says that the corresponding weighted sum of
characters is zero. The support exponent of a segment is the maximum, over
these bases, of the weighted positive parts of the characters. This finite
data yields the support norm identities.
-/

namespace PolycyclicRecognition

open scoped BigOperators

variable {W I B : Type*} [AddCommGroup W] [Module ℝ W]
  [Fintype I] [Fintype B] [Nonempty B]

namespace SupportDatum

variable (D : SupportDatum W I B)

omit [Nonempty B] in
theorem basisSupport_add_le (b : B) (v w : W) :
    D.basisSupport b (v + w) ≤ D.basisSupport b v + D.basisSupport b w := by
  simp only [basisSupport, map_add, ← Finset.sum_add_distrib, ← mul_add]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply max_le
  · exact add_nonneg (le_max_left _ _) (le_max_left _ _)
  · exact add_le_add (le_max_right _ _) (le_max_right _ _)

theorem segmentSupport_add_le (v w : W) :
    D.segmentSupport (v + w) ≤ D.segmentSupport v + D.segmentSupport w := by
  apply D.segmentSupport_le
  intro b
  exact (D.basisSupport_add_le b v w).trans
    (add_le_add (D.basisSupport_le b v) (D.basisSupport_le b w))

omit [Nonempty B] in
theorem basisSupport_smul_of_nonneg (b : B) (w : W) {r : ℝ} (hr : 0 ≤ r) :
    D.basisSupport b (r • w) = r * D.basisSupport b w := by
  simp only [basisSupport, map_smul, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hmax := mul_max_of_nonneg 0 (D.weight i w) hr
  rw [mul_zero] at hmax
  rw [← hmax]
  ring

theorem segmentSupport_smul_of_nonneg (w : W) {r : ℝ} (hr : 0 ≤ r) :
    D.segmentSupport (r • w) = r * D.segmentSupport w := by
  apply le_antisymm
  · apply D.segmentSupport_le
    intro b
    rw [D.basisSupport_smul_of_nonneg b w hr]
    exact mul_le_mul_of_nonneg_left (D.basisSupport_le b w) hr
  · obtain ⟨b, hb, heq⟩ := Finset.exists_mem_eq_sup'
      Finset.univ_nonempty (fun b => D.basisSupport b w)
    change r * Finset.univ.sup' _ _ ≤ _
    rw [heq, ← D.basisSupport_smul_of_nonneg b w hr]
    exact D.basisSupport_le b (r • w)

theorem segmentSupport_smul (w : W) (r : ℝ) :
    D.segmentSupport (r • w) = |r| * D.segmentSupport w := by
  rcases le_total 0 r with hr | hr
  · rw [abs_of_nonneg hr, D.segmentSupport_smul_of_nonneg w hr]
  · rw [abs_of_nonpos hr, ← D.segmentSupport_neg (r • w), ← neg_smul]
    exact D.segmentSupport_smul_of_nonneg w (neg_nonneg.mpr hr)

/-- The segment support is an actual real vector-space norm. This construction
does not install a new topology on a space carrying an existing norm. -/
theorem normCore : letI : Norm W := ⟨D.segmentSupport⟩; NormedSpace.Core ℝ W := by
  let : Norm W := ⟨D.segmentSupport⟩
  exact
    { norm_nonneg := D.segmentSupport_nonneg
      norm_smul := fun r w => by simpa only [Real.norm_eq_abs] using D.segmentSupport_smul w r
      norm_triangle := D.segmentSupport_add_le
      norm_eq_zero_iff := D.segmentSupport_eq_zero_iff }

end SupportDatum
end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalizedGroupLaws
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instBorelSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instGroup _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace _root_.OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact polynomial group laws for the actual rescalings

One fixed binary Dynkin formula suffices for all coordinate bases of the
original group. Its group and one-parameter identities are proved in each
basis, and closedness preserves them in the compact normalized family.
-/

noncomputable section

namespace PolycyclicRecognition

open Module Set

variable {V I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype I]

/-- Normalized Lie data whose fixed Dynkin product satisfies the group laws. -/
def normalizedGroupParameters {c : ℕ} (a : DynkinCoefficients c 2)
    (w : J → FreeMagma I) (b : J → V) (C : ℝ) :
    Set ((V →L[ℝ] V →L[ℝ] V) × (I → V)) :=
  normalizedLieParameters w b C ∩ {p | PolynomialGroupLaws (dynkinProduct a p.1)}

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialProductChart
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local product charts from the finite Dynkin identity

Products of exponentials in a basis have a locally surjective logarithm map.
The proof gets smoothness from the finite Dynkin polynomial and its derivative
from the exact one-coordinate restrictions. No smooth-logarithm or local
product assertion is a separate input.
-/

noncomputable section

namespace PolycyclicRecognition

open Module Set Filter
open scoped Topology ContDiff

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

attribute [local instance] OAI.PolycyclicRecognition.exponentialProductNormedAddCommGroup
attribute [local instance] OAI.PolycyclicRecognition.exponentialProductNormedSpace
variable {G : Type*} [Group G] {n : ℕ} (Exp : L → G) (b : Basis (Fin n) ℝ L)

variable (hExp : Function.Bijective Exp) (hzero : Exp 0 = 1)

include hzero in
@[simp] theorem basisProductLog_single (i : Fin n) (s : ℝ) :
    basisProductLog Exp b hExp (Pi.single i s) = s • b i := by
  apply hExp.injective
  rw [show Exp (basisProductLog Exp b hExp (Pi.single i s)) =
    basisExponentialProduct Exp b (Pi.single i s) from
      (Equiv.ofBijective Exp hExp).apply_symm_apply _]
  unfold basisExponentialProduct
  rw [list_prod_ofFn_eq_single _ i (by
    intro j hj
    simp [Pi.single_eq_of_ne hj, hzero])]
  simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NormalizedExponentialLaws
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact normalized exponential-coordinate groups

The defining equations retain both the exact group law and its adjoint
conjugation formula. All of these equations hold in the actual rescalings
and survive passage to a limit.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Module

variable {V I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype I]

def normalizedExponentialParameters {c : ℕ} (a : DynkinCoefficients c 2)
    (w : J → FreeMagma I) (b : J → V) (C : ℝ) :
    Set ((V →L[ℝ] V →L[ℝ] V) × (I → V)) :=
  normalizedGroupParameters a w b C ∩
    {p | ExponentialConjugationLaw (dynkinProduct a p.1) p.1}

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AmplitudeWordCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independently varying every amplitude in a fixed generator word -/

noncomputable section

namespace PolycyclicRecognition

def amplitudeWordEndpoint {I : Type*} {n m c : ℕ} (a : DynkinCoefficients c 2)
    (letters : Fin m → I)
    (p : ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ))
    (t : Fin m → ℝ) : Fin n → ℝ :=
  polynomialListProduct (dynkinProduct a p.1) (List.ofFn (fun j => t j • p.2 (letters j)))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AlternatingProductSubmersion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Submersion of an alternating product from two linear images

If generators in the union of two images bracket-generate the limiting
algebra, one fixed alternating product has a surjective differential.
Identity factors pad the unused side of each generator slot. The rank is
proved for the full product map, before restricting any parameters.
-/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def alternatingCoordinateProduct {c h : ℕ} (a : DynkinCoefficients c 2)
    (B : V →L[ℝ] V →L[ℝ] V) (L₁ L₂ : U →L[ℝ] V)
    (z : Fin h → U × U) : V :=
  polynomialListProduct (dynkinProduct a B)
    (List.ofFn (fun j => dynkinProduct a B (L₁ (z j).1) (L₂ (z j).2)))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalizedFreeRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized free cover of an integral representation

The basis omits zero, and a coefficient morphism sends a basis element to zero
whenever its image is zero. Thus the free-cover functor preserves zero maps.
The augmentation is a natural epimorphism with projective source.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

def normalizedFreeFunctor : Rep.{0} ℤ G ⥤ Rep.{0} ℤ G where
  obj := normalizedFreeRepresentation
  map := normalizedFreeMap
  map_id := normalizedFreeMap_id
  map_comp := normalizedFreeMap_comp

instance normalizedFreeRepresentation_projective (A : Rep.{0} ℤ G) :
    Projective (normalizedFreeRepresentation A) := by
  change Projective (Rep.free ℤ G {a : A // a ≠ 0})
  infer_instance

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NormalizedSyzygyFunctor
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Functorial syzygies from the normalized free cover -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

@[simp]
theorem normalizedSyzygyMap_zero (A B : Rep.{0} ℤ G) :
    normalizedSyzygyMap (0 : A ⟶ B) = 0 := by
  apply (cancel_mono (kernel.ι (normalizedFreeAugmentation B))).mp
  simp

def normalizedSyzygySequenceMap {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    normalizedSyzygySequence A ⟶ normalizedSyzygySequence B where
  τ₁ := normalizedSyzygyMap f
  τ₂ := normalizedFreeMap f
  τ₃ := f
  comm₁₂ := normalizedSyzygyMap_ι f
  comm₂₃ := normalizedFreeAugmentation_natural f

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FiniteIntegralRepresentations
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite generation in the concrete integral resolutions -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra

variable (G : Type) [Group G]

theorem integralRepresentationFinite_free (α : Type) [Finite α] :
    IntegralRepresentationFinite G (Rep.free ℤ G α) := by
  classical
  let := Fintype.ofFinite α
  exact Module.Finite.of_basis (Representation.freeAsModuleBasis ℤ G α)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_AscendingQuotientColimit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.telescopeAugmentation_epi _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete colimit of an ascending sequence of invariant relations

Every element is represented in the initial quotient. A class vanishes in the
quotient by the union precisely when it vanishes at a finite stage.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Submodule.Quotient.module
variable {G : Type} [Group G] (A : Rep.{0} ℤ G)

def invariantQuotientMap {N M : Submodule ℤ A}
    (hN : RepresentationInvariant A N) (hM : RepresentationInvariant A M) (h : N ≤ M) :
    Rep.quotient A N hN ⟶ Rep.quotient A M hM :=
  Rep.ofHom ⟨N.mapQ M LinearMap.id h, fun g => by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl⟩

def ascendingQuotientDiagram (N : ℕ → Submodule ℤ A)
    (hN : ∀ n, RepresentationInvariant A (N n)) (hmono : Monotone N) :
    SequentialRepresentationDiagram G where
  obj n := Rep.quotient A (N n) (hN n)
  map _ _ h := invariantQuotientMap A _ _ (hmono h)
  map_id n := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl
  map_comp i j k hij hjk := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl

def ascendingQuotientColimit (N : ℕ → Submodule ℤ A)
    (hN : ∀ n, RepresentationInvariant A (N n)) (hmono : Monotone N)
    (M : Submodule ℤ A) (hM : RepresentationInvariant A M)
    (hNM : ∀ n, N n ≤ M) (hcover : ∀ x ∈ M, ∃ n, x ∈ N n) :
    (ascendingQuotientDiagram A N hN hmono).ColimitCocone (Rep.quotient A M hM) where
  ι n := invariantQuotientMap A (hN n) hM (hNM n)
  comm i j hij := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl
  surj x := by
    obtain ⟨y, rfl⟩ := M.mkQ_surjective x
    exact ⟨0, (N 0).mkQ y, rfl⟩
  zero_exact i x hx := by
    obtain ⟨y, rfl⟩ := (N i).mkQ_surjective x
    have hy : y ∈ M := (Submodule.Quotient.mk_eq_zero _).mp hx
    obtain ⟨n, hn⟩ := hcover y hy
    refine ⟨max i n, Nat.le_max_left _ _, ?_⟩
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hmono (Nat.le_max_right i n) hn)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BooleanStepRing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ring of integer-valued functions on finite Boolean partitions

Only finitely many of the chosen Boolean coordinates may be used by any one
function. These functions form an actual subring, and each function has finite
range. This provides the small coefficient algebra needed for a countable group.
-/
noncomputable section
namespace PolycyclicRecognition
variable {X I : Type}

theorem booleanStepRing_coordinate (a : I → X → Bool) (i : I) :
    (fun x => if a i x then (1 : ℤ) else 0) ∈ booleanStepRing a := by
  classical
  exact ⟨{i}, fun x y hxy => by
    dsimp only
    rw [hxy i (Finset.mem_singleton_self i)]⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BooleanPartitionMaps
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
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

/-- Forget some of the Boolean coordinates of a realized partition cell. -/
def booleanPartitionRefine {s t : Finset I} (h : s ⊆ t) :
    booleanPartitionCell a t → booleanPartitionCell a s := fun c =>
  ⟨fun i => c.val ⟨i.val, h i.property⟩, by
    obtain ⟨x, hx⟩ := c.property
    refine ⟨x, ?_⟩
    funext i
    exact congrFun hx ⟨i.val, h i.property⟩⟩

@[simp]
theorem booleanPartitionRefine_point {s t : Finset I} (h : s ⊆ t) (x : X) :
    booleanPartitionRefine a h (booleanPartitionPoint a t x) = booleanPartitionPoint a s x := rfl

theorem booleanPartitionRefine_surjective {s t : Finset I} (h : s ⊆ t) :
    Function.Surjective (booleanPartitionRefine a h) := by
  intro c
  exact ⟨booleanPartitionPoint a t (booleanPartitionRepresentative a s c),
    booleanPartitionPoint_representative a s c⟩

abbrev booleanPartitionStage (s : Finset I) : Rep ℤ PUnit.{1} :=
  Rep.trivial ℤ PUnit.{1} (booleanPartitionCell a s → ℤ)

instance booleanPartitionStage_projective (s : Finset I) :
    Projective (booleanPartitionStage a s) := by
  let := Fintype.ofFinite (booleanPartitionCell a s)
  apply projective_rep_of_integer_projective

/-- Pull a step function back to a finer partition. -/
def booleanPartitionMap {s t : Finset I} (h : s ⊆ t) :
    booleanPartitionStage a s ⟶ booleanPartitionStage a t :=
  subsingletonGroupRepHom {
    toFun v c := v (booleanPartitionRefine a h c)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

/-- Choose one refined cell above each old cell to obtain a retraction. -/
def booleanPartitionRetraction {s t : Finset I} (h : s ⊆ t) :
    booleanPartitionStage a t ⟶ booleanPartitionStage a s :=
  subsingletonGroupRepHom {
    toFun v c := v (Function.surjInv (booleanPartitionRefine_surjective a h) c)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

theorem booleanPartitionMap_retraction {s t : Finset I} (h : s ⊆ t) :
    booleanPartitionMap a h ≫ booleanPartitionRetraction a h = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  funext c
  exact congrArg v (Function.surjInv_eq (booleanPartitionRefine_surjective a h) c)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentPowerSeriesEvaluation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite evaluation of rational power series at a nilpotent element

Evaluation takes place in the given associative algebra, which need not be
commutative. Nilpotence makes truncation invisible to polynomial evaluation.
-/

noncomputable section
namespace PolycyclicRecognition

theorem powerSeries_trunc_monomial (n k : ℕ) (q : ℚ) :
    PowerSeries.trunc n (Polynomial.monomial k q : PowerSeries ℚ) =
      if k < n then Polynomial.monomial k q else 0 := by
  by_cases hk : k < n
  · rw [ite_eq_left hk]
    ext d
    rw [PowerSeries.coeff_trunc, Polynomial.coeff_coe]
    by_cases hd : k = d
    · subst d; simp [hk]
    · simp [Polynomial.coeff_monomial, hd]
  · rw [ite_eq_right hk]
    ext d
    rw [PowerSeries.coeff_trunc, Polynomial.coeff_coe]
    by_cases hd : k = d
    · subst d; simp [hk]
    · simp [Polynomial.coeff_monomial, hd]

variable {A : Type*} [Ring A] [Algebra ℚ A] (a : A) {n : ℕ}

theorem aeval_powerSeries_trunc_coe (ha : a ^ n = 0) (p : Polynomial ℚ) :
    Polynomial.aeval a (PowerSeries.trunc n (p : PowerSeries ℚ)) =
      Polynomial.aeval a p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [Polynomial.coe_add, map_add] using congrArg₂ (· + ·) hp hq
  | monomial k q =>
    rw [powerSeries_trunc_monomial]
    split_ifs with hk
    · rfl
    · rw [map_zero, Polynomial.aeval_monomial,
        pow_eq_zero_of_le (Nat.le_of_not_gt hk) ha, mul_zero]

def nilpotentPowerSeriesEval (n : ℕ) (ha : a ^ (n + 1) = 0) : PowerSeries ℚ →+* A where
  toFun f := Polynomial.aeval a (PowerSeries.trunc (n + 1) f)
  map_zero' := by simp
  map_one' := by rw [PowerSeries.trunc_one, map_one]
  map_add' f g := by rw [map_add, map_add]
  map_mul' f g := by
    rw [← PowerSeries.trunc_trunc_mul_trunc]
    rw [← Polynomial.coe_mul, aeval_powerSeries_trunc_coe a ha, map_mul]

theorem nilpotentPowerSeriesEval_coe (n : ℕ) (ha : a ^ (n + 1) = 0) (p : Polynomial ℚ) :
    nilpotentPowerSeriesEval a n ha (p : PowerSeries ℚ) = Polynomial.aeval a p :=
  aeval_powerSeries_trunc_coe a ha p

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalPowerSeriesHom
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational power-series homomorphisms killed by a power of the variable -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A] (F : PowerSeries ℚ →+* A)

omit [Algebra ℚ A] in
theorem rationalPowerSeriesHom_eq_trunc {n : ℕ}
    (hF : F PowerSeries.X ^ n = 0) (f : PowerSeries ℚ) :
    F f = F (PowerSeries.trunc n f : PowerSeries ℚ) := by
  have hd : (PowerSeries.X : PowerSeries ℚ) ^ n ∣
      f - (PowerSeries.trunc n f : PowerSeries ℚ) := by
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro k hk
    rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, ite_eq_left hk, sub_self]
  obtain ⟨q, hq⟩ := hd
  have hzero : F (f - (PowerSeries.trunc n f : PowerSeries ℚ)) = 0 := by
    rw [hq, map_mul, map_pow, hF, zero_mul]
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

theorem rationalPowerSeriesHom_eq_aeval_trunc {n : ℕ}
    (hF : F PowerSeries.X ^ n = 0) (f : PowerSeries ℚ) :
    F f = Polynomial.aeval (F PowerSeries.X) (PowerSeries.trunc n f) := by
  rw [rationalPowerSeriesHom_eq_trunc F hF, rationalPowerSeriesHom_polynomial]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentPowerSeriesSubstitution
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Substitution under finite power-series evaluation -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A] (a : A) (n : ℕ) (ha : a ^ (n + 1) = 0)

theorem nilpotentPowerSeriesEval_X :
    nilpotentPowerSeriesEval a n ha PowerSeries.X = a := by
  rw [← Polynomial.coe_X, nilpotentPowerSeriesEval_coe, Polynomial.aeval_X]

theorem nilpotentPowerSeriesEval_nilpotent (g : PowerSeries ℚ)
    (hg : g.constantCoeff = 0) :
    nilpotentPowerSeriesEval a n ha g ^ (n + 1) = 0 := by
  obtain ⟨q, hq⟩ := PowerSeries.X_dvd_iff.mpr hg
  rw [← map_pow, hq, mul_pow, map_mul, map_pow, nilpotentPowerSeriesEval_X, ha, zero_mul]

theorem nilpotentPowerSeriesEval_subst (f g : PowerSeries ℚ)
    (hg : g.constantCoeff = 0) :
    nilpotentPowerSeriesEval a n ha (PowerSeries.subst g f) =
      Polynomial.aeval (nilpotentPowerSeriesEval a n ha g) (PowerSeries.trunc (n + 1) f) := by
  let S : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ :=
    PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' hg)
  let F := (nilpotentPowerSeriesEval a n ha).comp S.toRingHom
  have hX : F PowerSeries.X = nilpotentPowerSeriesEval a n ha g := by
    change nilpotentPowerSeriesEval a n ha (S PowerSeries.X) = _
    congr 1
    exact PowerSeries.substAlgHom_X (R := ℚ) (PowerSeries.HasSubst.of_constantCoeff_zero' hg)
  have hnil : F PowerSeries.X ^ (n + 1) = 0 := by
    rw [hX]
    exact nilpotentPowerSeriesEval_nilpotent a n ha g hg
  have h := rationalPowerSeriesHom_eq_aeval_trunc F hnil f
  rw [hX] at h
  change nilpotentPowerSeriesEval a n ha (S f) = _ at h
  simpa only [S, PowerSeries.coe_substAlgHom] using h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FiniteExponentialLogarithm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Compatibility with OpenAI's Mathlib (d13f23b): `log` and `exp` as inverse power series
(`Mathlib/RingTheory/PowerSeries/Log.lean` and `Substitution.lean` there). -/

namespace OAI

/-! # Finite exponential and logarithm identities

Formal power-series identities evaluate in an associative rational algebra
at a nilpotent element. All expressions are finite polynomials.
-/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A]

theorem nilpotentPowerSeriesEval_exp (a : A) (n : ℕ) (ha : a ^ (n + 1) = 0) :
    nilpotentPowerSeriesEval a n ha (PowerSeries.exp ℚ) = IsNilpotent.exp a := by
  change Polynomial.aeval a (PowerSeries.trunc (n + 1) (PowerSeries.exp ℚ)) = _
  rw [Polynomial.aeval_def, PowerSeries.eval₂_trunc_eq_sum_range, IsNilpotent.exp_eq_sum ha]
  apply Finset.sum_congr rfl
  intro k _
  rw [PowerSeries.coeff_exp]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, one_div, Algebra.smul_def]

theorem finiteNilpotentLog_pow (a : A) (n : ℕ) (ha : a ^ (n + 1) = 0) :
    finiteNilpotentLog (n + 1) a ^ (n + 1) = 0 :=
  nilpotentPowerSeriesEval_nilpotent a n ha (PowerSeries.log ℚ) PowerSeries.constantCoeff_log

theorem finiteNilpotentLog_exp (a : A) (n : ℕ) (ha : a ^ (n + 1) = 0) :
    finiteNilpotentLog (n + 1) (IsNilpotent.exp a - 1) = a := by
  have hg : (PowerSeries.exp ℚ - 1).constantCoeff = 0 := by simp
  have h := nilpotentPowerSeriesEval_subst a n ha
    (PowerSeries.log ℚ) (PowerSeries.exp ℚ - 1) hg
  rw [PowerSeries.subst_log_exp_sub_one, nilpotentPowerSeriesEval_X, map_sub,
    nilpotentPowerSeriesEval_exp, map_one] at h
  exact h.symm

theorem exp_finiteNilpotentLog (a : A) (n : ℕ) (ha : a ^ (n + 1) = 0) :
    IsNilpotent.exp (finiteNilpotentLog (n + 1) a) = 1 + a := by
  have h := nilpotentPowerSeriesEval_subst a n ha
    (PowerSeries.exp ℚ) (PowerSeries.log ℚ) PowerSeries.constantCoeff_log
  rw [PowerSeries.subst_exp_log, map_add, map_one, nilpotentPowerSeriesEval_X] at h
  have hb := finiteNilpotentLog_pow a n ha
  have he := nilpotentPowerSeriesEval_exp (finiteNilpotentLog (n + 1) a) n hb
  change Polynomial.aeval (finiteNilpotentLog (n + 1) a)
    (PowerSeries.trunc (n + 1) (PowerSeries.exp ℚ)) = _ at he
  change 1 + a = Polynomial.aeval (finiteNilpotentLog (n + 1) a)
    (PowerSeries.trunc (n + 1) (PowerSeries.exp ℚ)) at h
  exact (h.trans he).symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CanonicalNilpotentLogarithm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A truncation-independent logarithm for unipotent elements -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A]

theorem nilpotentLog_eq_of_pow (a : A) (ha : IsNilpotent a) (n : ℕ)
    (hn : a ^ (n + 1) = 0) : nilpotentLog a = finiteNilpotentLog (n + 1) a := by
  have hk : a ^ (nilpotencyClass a + 1) = 0 := by
    rw [pow_succ, pow_nilpotencyClass ha, zero_mul]
  let F := nilpotentPowerSeriesEval a (nilpotencyClass a) hk
  have hF : F PowerSeries.X ^ (n + 1) = 0 := by
    rw [nilpotentPowerSeriesEval_X]
    exact hn
  have h := rationalPowerSeriesHom_eq_aeval_trunc F hF (PowerSeries.log ℚ)
  rw [nilpotentPowerSeriesEval_X] at h
  exact h

theorem nilpotentLog_nilpotent (a : A) (ha : IsNilpotent a) :
    IsNilpotent (nilpotentLog a) := by
  have hk : a ^ (nilpotencyClass a + 1) = 0 := by
    rw [pow_succ, pow_nilpotencyClass ha, zero_mul]
  exact ⟨_, finiteNilpotentLog_pow a (nilpotencyClass a) hk⟩

theorem exp_nilpotentLog (a : A) (ha : IsNilpotent a) :
    IsNilpotent.exp (nilpotentLog a) = 1 + a := by
  apply exp_finiteNilpotentLog
  rw [pow_succ, pow_nilpotencyClass ha, zero_mul]

theorem nilpotentLog_exp (a : A) (ha : IsNilpotent a) :
    nilpotentLog (IsNilpotent.exp a - 1) = a := by
  have hk : a ^ (nilpotencyClass a + 1) = 0 := by
    rw [pow_succ, pow_nilpotencyClass ha, zero_mul]
  have he : (IsNilpotent.exp a - 1) ^ (nilpotencyClass a + 1) = 0 := by
    have h := nilpotentPowerSeriesEval_nilpotent a (nilpotencyClass a) hk
      (PowerSeries.exp ℚ - 1) (by simp)
    simpa only [map_sub, nilpotentPowerSeriesEval_exp, map_one] using h
  rw [nilpotentLog_eq_of_pow _ (IsNilpotent.isNilpotent_exp_sub_one ha) _ he]
  exact finiteNilpotentLog_exp a (nilpotencyClass a) hk

theorem nilpotentLog_map {B : Type*} [Ring B] [Algebra ℚ B]
    (f : A →+* B) (a : A) (ha : IsNilpotent a) :
    nilpotentLog (f a) = f (nilpotentLog a) := by
  have hk : a ^ (nilpotencyClass a + 1) = 0 := by
    rw [pow_succ, pow_nilpotencyClass ha, zero_mul]
  have hf : (f a) ^ (nilpotencyClass a + 1) = 0 := by rw [← map_pow, hk, map_zero]
  let F := f.comp (nilpotentPowerSeriesEval a (nilpotencyClass a) hk)
  have hF : F PowerSeries.X ^ (nilpotencyClass a + 1) = 0 := by
    change f (nilpotentPowerSeriesEval a (nilpotencyClass a) hk PowerSeries.X) ^ _ = 0
    rwa [nilpotentPowerSeriesEval_X]
  have h := rationalPowerSeriesHom_eq_aeval_trunc F hF (PowerSeries.log ℚ)
  have hx : F PowerSeries.X = f a := by
    simp only [F, RingHom.comp_apply, nilpotentPowerSeriesEval_X]
  rw [hx] at h
  change f (nilpotentLog a) = finiteNilpotentLog (nilpotencyClass a + 1) (f a) at h
  rw [nilpotentLog_eq_of_pow _ ⟨_, hf⟩ _ hf]
  exact h.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_ChartedVectorFieldBracket
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lie brackets in vector-space charts

The source chart is used only locally. This bridges the differential of an
algebra-valued map with the intrinsic bracket of vector fields.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Function Bundle VectorField
open scoped Manifold ContDiff Topology

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

theorem chartVectorField_related
    {f : M → F} (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ f)
    {V : (x : M) → TangentSpace (𝓘(ℝ, E)) x} {V' : F → F}
    (hrel : ∀ x, mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x (V x) = V' (f x))
    (x₀ : M) {y : E} (hy : y ∈ (extChartAt (𝓘(ℝ, E)) x₀).target) :
    fderiv ℝ (f ∘ (extChartAt (𝓘(ℝ, E)) x₀).symm) y (chartVectorField x₀ V y) =
      V' (f ((extChartAt (𝓘(ℝ, E)) x₀).symm y)) := by
  let φ := extChartAt (𝓘(ℝ, E)) x₀
  let D : E →L[ℝ] E := mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm y
  let B : E →L[ℝ] F := mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f (φ.symm y)
  let v : E := V (φ.symm y)
  have hD : D.IsInvertible := by
    have hrange : range (𝓘(ℝ, E)) = (univ : Set E) := by ext x; simp
    have hh := isInvertible_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ, E)) hy
    rw [hrange, mfderivWithin_univ] at hh
    exact hh
  rw [fderiv_chart_comp hf x₀ hy]
  change B (D (D.inverse v)) = V' (f (φ.symm y))
  exact (congrArg B (hD.self_apply_inverse v)).trans (hrel (φ.symm y))

theorem fderiv_chart_comp_base
    {f : M → F} (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ f) (x₀ : M) :
    fderiv ℝ (f ∘ (extChartAt (𝓘(ℝ, E)) x₀).symm)
      (extChartAt (𝓘(ℝ, E)) x₀ x₀) =
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x₀ := by
  have hh := fderiv_chart_comp hf x₀ (mem_extChartAt_target x₀)
  rw [mfderiv_chart_symm_base] at hh
  have hB : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f
      ((extChartAt (𝓘(ℝ, E)) x₀).symm (extChartAt (𝓘(ℝ, E)) x₀ x₀)) : E →L[ℝ] F) =
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x₀ := by
    congr 1
    exact extChartAt_to_inv x₀
  exact hh.trans ((congrArg (fun B : E →L[ℝ] F => B.comp (ContinuousLinearMap.id ℝ E)) hB).trans
    (ContinuousLinearMap.comp_id _))

theorem mfderiv_mlieBracket_of_related [CompleteSpace E]
    {f : M → F} (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ f)
    {V W : (x : M) → TangentSpace (𝓘(ℝ, E)) x} {V' W' : F → F}
    (hV : ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (𝓘(ℝ, E)) M)))
    (hW : ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞
      (fun x => (⟨x, W x⟩ : TangentBundle (𝓘(ℝ, E)) M)))
    (hV' : Differentiable ℝ V') (hW' : Differentiable ℝ W')
    (hrelV : ∀ x, mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x (V x) = V' (f x))
    (hrelW : ∀ x, mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x (W x) = W' (f x))
    (x₀ : M) :
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x₀ (mlieBracket (𝓘(ℝ, E)) V W x₀) =
      lieBracket ℝ V' W' (f x₀) := by
  let φ := extChartAt (𝓘(ℝ, E)) x₀
  let fbar : E → F := f ∘ φ.symm
  have hinv : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ φ.symm (φ x₀) := by
    simpa only [φ, mfld_simps, contMDiffWithinAt_univ] using
      (contMDiffWithinAt_extChartAt_symm_range_self (I := 𝓘(ℝ, E)) (n := ∞) x₀)
  have hbar : ContDiffAt ℝ 2 fbar (φ x₀) :=
    (((hf x₀).comp_of_eq hinv (extChartAt_to_inv x₀)).contDiffAt).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have htarget : φ.target ∈ 𝓝 (φ x₀) := by
    simpa only [φ, mfld_simps, nhdsWithin_univ] using
      extChartAt_target_mem_nhdsWithin (I := 𝓘(ℝ, E)) x₀
  have hrv : ∀ᶠ y in 𝓝 (φ x₀),
      fderiv ℝ fbar y (chartVectorField x₀ V y) = V' (fbar y) :=
    eventually_of_mem htarget fun y hy => chartVectorField_related hf hrelV x₀ hy
  have hrw : ∀ᶠ y in 𝓝 (φ x₀),
      fderiv ℝ fbar y (chartVectorField x₀ W y) = W' (fbar y) :=
    eventually_of_mem htarget fun y hy => chartVectorField_related hf hrelW x₀ hy
  have hb := fderiv_lieBracket_of_related hbar
    (differentiableAt_chartVectorField ((hV x₀).mdifferentiableAt (by simp)))
    (differentiableAt_chartVectorField ((hW x₀).mdifferentiableAt (by simp)))
    (hV' _) (hW' _) hrv hrw
  let B : E →L[ℝ] F := mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x₀
  have hbr := mlieBracket_eq_chartBracket V W x₀
  have hbase := fderiv_chart_comp_base hf x₀
  have hvalue : fbar (φ x₀) = f x₀ := congrArg f (extChartAt_to_inv x₀)
  exact (congrArg B hbr).trans
    ((congrArg (fun L : E →L[ℝ] F =>
      L (lieBracket ℝ (chartVectorField x₀ V) (chartVectorField x₀ W) (φ x₀)))
        hbase.symm).trans (hb.trans (congrArg (lieBracket ℝ V' W') hvalue)))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ManifoldRelatedBracket
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Brackets of related vector fields on manifolds

Both source and target charts are local. This extends the vector-space
calculation only as far as needed to differentiate Lie-group homomorphisms.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Function Bundle VectorField
open scoped Manifold ContDiff Topology

variable {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold (𝓘(ℝ, F)) ∞ N]

theorem mfderiv_mlieBracket_of_manifold_related [CompleteSpace E] [CompleteSpace F]
    {f : M → N} (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ f)
    {V W : (x : M) → TangentSpace (𝓘(ℝ, E)) x}
    {V' W' : (y : N) → TangentSpace (𝓘(ℝ, F)) y}
    (hV : ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (𝓘(ℝ, E)) M)))
    (hW : ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞
      (fun x => (⟨x, W x⟩ : TangentBundle (𝓘(ℝ, E)) M)))
    (hV' : ContMDiff (𝓘(ℝ, F)) ((𝓘(ℝ, F)).prod (𝓘(ℝ, F))) ∞
      (fun y => (⟨y, V' y⟩ : TangentBundle (𝓘(ℝ, F)) N)))
    (hW' : ContMDiff (𝓘(ℝ, F)) ((𝓘(ℝ, F)).prod (𝓘(ℝ, F))) ∞
      (fun y => (⟨y, W' y⟩ : TangentBundle (𝓘(ℝ, F)) N)))
    (hrelV : ∀ x, mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x (V x) = V' (f x))
    (hrelW : ∀ x, mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x (W x) = W' (f x))
    (x₀ : M) :
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x₀ (mlieBracket (𝓘(ℝ, E)) V W x₀) =
      mlieBracket (𝓘(ℝ, F)) V' W' (f x₀) := by
  let φ := extChartAt (𝓘(ℝ, E)) x₀
  let ψ := extChartAt (𝓘(ℝ, F)) (f x₀)
  let fbar : E → F := ψ ∘ f ∘ φ.symm
  have hinv : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ φ.symm (φ x₀) := by
    simpa only [φ, mfld_simps, contMDiffWithinAt_univ] using
      (contMDiffWithinAt_extChartAt_symm_range_self (I := 𝓘(ℝ, E)) (n := ∞) x₀)
  have heq : (f ∘ φ.symm) (φ x₀) = f x₀ := congrArg f (extChartAt_to_inv x₀)
  have hbar : ContDiffAt ℝ 2 fbar (φ x₀) := by
    apply ContDiffAt.of_le (n := ∞) _ (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    exact ((contMDiffAt_extChartAt (I := 𝓘(ℝ, F))).comp_of_eq
      ((hf x₀).comp_of_eq hinv (extChartAt_to_inv x₀)) heq).contDiffAt
  have htarget : φ.target ∈ 𝓝 (φ x₀) := by
    simpa only [φ, mfld_simps, nhdsWithin_univ] using
      extChartAt_target_mem_nhdsWithin (I := 𝓘(ℝ, E)) x₀
  have hsource : ψ.source ∈ 𝓝 (f x₀) := extChartAt_source_mem_nhds (f x₀)
  have himage : ∀ᶠ y in 𝓝 (φ x₀), f (φ.symm y) ∈ ψ.source := by
    apply (hf.continuous.continuousAt.comp hinv.continuousAt).preimage_mem_nhds
    rw [heq]
    exact hsource
  have hrelated (A : (x : M) → TangentSpace (𝓘(ℝ, E)) x)
      (B : (y : N) → TangentSpace (𝓘(ℝ, F)) y)
      (hrel : ∀ x, mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x (A x) = B (f x)) :
      ∀ᶠ y in 𝓝 (φ x₀), fderiv ℝ fbar y (chartVectorField x₀ A y) =
        chartVectorField (f x₀) B (fbar y) := by
    filter_upwards [htarget, himage] with y hy hfy
    have hD : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm y).IsInvertible := by
      simpa only [φ, mfld_simps, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ, E)) hy
    rw [show fbar = ψ ∘ f ∘ φ.symm from rfl, fderiv_double_chart hf x₀ hy hfy]
    change (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (f (φ.symm y)))
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f (φ.symm y))
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm y)
          ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm y).inverse (A (φ.symm y))))) = _
    rw [hD.self_apply_inverse, hrel]
    exact (chartVectorField_apply_chart (f x₀) B hfy).symm
  have hvalue : fbar (φ x₀) = ψ (f x₀) := congrArg ψ heq
  have hb := fderiv_lieBracket_of_related hbar
    (differentiableAt_chartVectorField ((hV x₀).mdifferentiableAt (by simp)))
    (differentiableAt_chartVectorField ((hW x₀).mdifferentiableAt (by simp)))
    (by rw [hvalue]; exact
      differentiableAt_chartVectorField ((hV' (f x₀)).mdifferentiableAt (by simp)))
    (by rw [hvalue]; exact
      differentiableAt_chartVectorField ((hW' (f x₀)).mdifferentiableAt (by simp)))
    (hrelated V V' hrelV) (hrelated W W' hrelW)
  have hbase : fderiv ℝ fbar (φ x₀) = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x₀ := by
    have hh := fderiv_double_chart hf x₀ (mem_extChartAt_target x₀)
      (by simpa only [extChartAt_to_inv] using mem_extChartAt_source (I := 𝓘(ℝ, F)) (f x₀))
    have hpoint : φ.symm (φ x₀) = x₀ := extChartAt_to_inv x₀
    have hB : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f (φ.symm (φ x₀)) : E →L[ℝ] F) =
        mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x₀ := by congr 1
    have hT : (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (f (φ.symm (φ x₀))) : F →L[ℝ] F) =
        ContinuousLinearMap.id ℝ F := by
      have hp : (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (f (φ.symm (φ x₀))) : F →L[ℝ] F) =
          mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (f x₀) := by congr 1
      exact hp.trans (mfderiv_extChartAt_self (I := 𝓘(ℝ, F)))
    change fderiv ℝ fbar (φ x₀) =
      (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (f (φ.symm (φ x₀)))).comp
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f (φ.symm (φ x₀))).comp
          (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm (φ x₀))) at hh
    rw [hT, hB, mfderiv_chart_symm_base] at hh
    change fderiv ℝ fbar (φ x₀) = (ContinuousLinearMap.id ℝ F).comp
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x₀ : E →L[ℝ] F).comp
        (ContinuousLinearMap.id ℝ E)) at hh
    exact hh.trans (ContinuousLinearMap.ext fun _ => rfl)
  rw [hbase] at hb
  rw [mlieBracket_eq_chartBracket V W x₀, mlieBracket_eq_chartBracket V' W' (f x₀)]
  exact hb.trans (congrArg (lieBracket ℝ (chartVectorField (f x₀) V')
    (chartVectorField (f x₀) W')) (congrArg ψ heq))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SmoothHomLieDifferential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Differentiating smooth Lie-group homomorphisms

The differential preserves brackets because the associated invariant
vector fields are related by the homomorphism.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {E G F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace H] [ChartedSpace F H] [Group H] [LieGroup (𝓘(ℝ, F)) ⊤ H]

theorem mfderiv_hom_map_bracket (φ : G →* H)
    (hφ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ φ)
    (v w : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    homDifferentialLinear (E := E) (F := F) φ ⁅v, w⁆ = ⁅homDifferentialLinear (E := E) (F := F) φ v, homDifferentialLinear (E := E) (F := F) φ w⁆ := by
  have hd := hφ.mdifferentiable (by simp)
  have hh := mfderiv_mlieBracket_of_manifold_related hφ
    (contMDiff_invariantVectorField_infty v) (contMDiff_invariantVectorField_infty w)
    (contMDiff_invariantVectorField_infty (homDifferentialLinear (E := E) (F := F) φ v))
    (contMDiff_invariantVectorField_infty (homDifferentialLinear (E := E) (F := F) φ w))
    (mfderiv_hom_invariant φ hd v) (mfderiv_hom_invariant φ hd w) 1
  let B : H → F := fun y => VectorField.mlieBracket (𝓘(ℝ, F))
    (mulInvariantVectorField (homDifferentialLinear (E := E) (F := F) φ v))
    (mulInvariantVectorField (homDifferentialLinear (E := E) (F := F) φ w)) y
  exact hh.trans (congrArg B φ.map_one)

def homLieDifferential (φ : G →* H)
    (hφ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ φ) :
    GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, F)) H where
  toLinearMap := homDifferentialLinear (E := E) (F := F) φ
  map_lie' := fun {v w} => mfderiv_hom_map_bracket φ hφ v w

@[simp] theorem homLieDifferential_apply (φ : G →* H)
    (hφ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ φ)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    homLieDifferential φ hφ v = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1 v := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ProductLieAlgebra
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tangent projections of a product Lie group

The jointly injective projections detect nilpotence and transport a single
finite BCH identity to both factors.
-/

noncomputable section
namespace PolycyclicRecognition

open LieModule
open scoped Manifold ContDiff

variable {E G F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace H] [ChartedSpace F H] [Group H] [LieGroup (𝓘(ℝ, F)) ⊤ H]

attribute [local instance] productSelfChartedSpace

def productFstLieHom : GroupLieAlgebra (𝓘(ℝ, E × F)) (G × H) →ₗ⁅ℝ⁆
    GroupLieAlgebra (𝓘(ℝ, E)) G :=
  homLieDifferential (MonoidHom.fst G H) contMDiff_product_fst

def productSndLieHom : GroupLieAlgebra (𝓘(ℝ, E × F)) (G × H) →ₗ⁅ℝ⁆
    GroupLieAlgebra (𝓘(ℝ, F)) H :=
  homLieDifferential (MonoidHom.snd G H) contMDiff_product_snd

@[simp] theorem productFstLieHom_apply (v : GroupLieAlgebra (𝓘(ℝ, E × F)) (G × H)) :
    productFstLieHom (E := E) (F := F) (G := G) (H := H) v = v.1 := by
  have hd : (mfderiv ((𝓘(ℝ, E)).prod (𝓘(ℝ, F))) (𝓘(ℝ, E))
      (Prod.fst : G × H → G) 1 : (E × F) →L[ℝ] E) = ContinuousLinearMap.fst ℝ E F :=
    mfderiv_fst
  rw [← modelWithCornersSelf_prod] at hd
  exact congrArg (fun D : (E × F) →L[ℝ] E => D v) hd

@[simp] theorem productSndLieHom_apply (v : GroupLieAlgebra (𝓘(ℝ, E × F)) (G × H)) :
    productSndLieHom (E := E) (F := F) (G := G) (H := H) v = v.2 := by
  have hd : (mfderiv ((𝓘(ℝ, E)).prod (𝓘(ℝ, F))) (𝓘(ℝ, F))
      (Prod.snd : G × H → H) 1 : (E × F) →L[ℝ] F) = ContinuousLinearMap.snd ℝ E F :=
    mfderiv_snd
  rw [← modelWithCornersSelf_prod] at hd
  exact congrArg (fun D : (E × F) →L[ℝ] F => D v) hd

theorem product_tangent_nilpotent
    (hG : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (hH : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, F)) H)) :
    LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E × F)) (G × H)) := by
  obtain ⟨c, hc⟩ := (isNilpotent_iff ℝ _ _).mp hG
  obtain ⟨d, hd⟩ := (isNilpotent_iff ℝ _ _).mp hH
  apply (isNilpotent_iff ℝ _ _).mpr
  refine ⟨max c d, le_antisymm ?_ bot_le⟩
  intro x hx
  have hfst : productFstLieHom (E := E) (F := F) (G := G) (H := H) x = 0 := by
    have hm := LieIdeal.map_lowerCentralSeries_le (R := ℝ)
      (f := productFstLieHom (E := E) (F := F) (G := G) (H := H)) (max c d)
    have hle := (antitone_lowerCentralSeries ℝ
      (GroupLieAlgebra (𝓘(ℝ, E)) G) (GroupLieAlgebra (𝓘(ℝ, E)) G)) (Nat.le_max_left c d)
    rw [hc] at hle
    exact (hm.trans hle) (LieIdeal.mem_map hx)
  have hsnd : productSndLieHom (E := E) (F := F) (G := G) (H := H) x = 0 := by
    have hm := LieIdeal.map_lowerCentralSeries_le (R := ℝ)
      (f := productSndLieHom (E := E) (F := F) (G := G) (H := H)) (max c d)
    have hle := (antitone_lowerCentralSeries ℝ
      (GroupLieAlgebra (𝓘(ℝ, F)) H) (GroupLieAlgebra (𝓘(ℝ, F)) H)) (Nat.le_max_right c d)
    rw [hd] at hle
    exact (hm.trans hle) (LieIdeal.mem_map hx)
  change x = 0
  rw [productFstLieHom_apply] at hfst
  rw [productSndLieHom_apply] at hsnd
  exact Prod.ext hfst hsnd

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CommonDynkinFormula
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common BCH formula for two nilpotent Lie groups

Apply the published finite Dynkin identity once to the product group, then
project to each factor. The projections preserve the actual tangent bracket.
-/

noncomputable section
namespace PolycyclicRecognition

open LieModule
open scoped Manifold

attribute [local instance] productSelfChartedSpace

variable {E G F H : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [ChartedSpace F H] [Group H] [LieGroup (𝓘(ℝ, F)) ⊤ H] [T2Space H]

/-- The product is packaged solely to instantiate the existing published
input. Its measurable structure is the Borel structure of the product. -/
def exponentialProductLieModel
    (cG : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
    (cH : GroupLieAlgebra (𝓘(ℝ, F)) H ≃ₜ H) :
    NilpotentLieModel (GroupLieAlgebra (𝓘(ℝ, E × F)) (G × H)) := by
  letI : MeasurableSpace (G × H) := borel (G × H)
  letI : BorelSpace (G × H) := ⟨rfl⟩
  exact {
    modelSpace := E × F
    carrier := G × H
    simplyConnectedSpace := (cG.prodCongr cH).symm.toHomotopyEquiv.simplyConnectedSpace
    equiv := LieEquiv.refl }

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CommutingUnipotentLogarithm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithm of commuting unipotent products -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A]

theorem nilpotentLog_unipotent_mul {a b : A} (h : Commute a b)
    (ha : IsNilpotent a) (hb : IsNilpotent b) :
    nilpotentLog ((1 + a) * (1 + b) - 1) = nilpotentLog a + nilpotentLog b := by
  have hc := commute_nilpotentLog h
  have hn := hc.isNilpotent_add (nilpotentLog_nilpotent a ha) (nilpotentLog_nilpotent b hb)
  have he : IsNilpotent.exp (nilpotentLog a + nilpotentLog b) = (1 + a) * (1 + b) := by
    rw [IsNilpotent.exp_add_of_commute hc (nilpotentLog_nilpotent a ha)
      (nilpotentLog_nilpotent b hb), exp_nilpotentLog a ha, exp_nilpotentLog b hb]
  rw [← he, nilpotentLog_exp _ hn]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DifferenceAmplitudeWord
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Two independent interval samples per generator switch -/

noncomputable section

namespace PolycyclicRecognition

open Module

def differenceAmplitudeWordEndpoint {I : Type*} {n m c : ℕ} (a : DynkinCoefficients c 2)
    (letters : Fin m → I)
    (p : ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ))
    (t : Fin (m + m) → ℝ) : Fin n → ℝ :=
  amplitudeWordEndpoint a letters p (differenceParameters m t)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoupledBundleStates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual bundle conjugations preserve joint Haar volume -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set

variable {N : Type*} [Group N] [TopologicalSpace N] [IsTopologicalGroup N]

variable [MeasurableSpace N] [BorelSpace N]

omit [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N] in
@[simp] theorem bundleConjugator_apply {h m : ℕ} (k : Fin h → N)
    (i : Fin h) (j : Fin m) :
    bundleConjugator m k (finProdFinEquiv (i, j)).val = k i := by
  rw [bundleConjugator, dite_eq_left (finProdFinEquiv (i, j)).isLt]
  change k (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1 = k i
  rw [Equiv.symm_apply_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_WordPowerCoefficientBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.rationalWordAntipode_one _root_.OAI.PolycyclicRecognition.rationalWordDegree_one _root_.OAI.PolycyclicRecognition.wordAntipodeConvolution_tmul _root_.OAI.PolycyclicRecognition.wordDegreeConvolution_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binomial bounds for powers of a word series with zero constant term -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {n : ℕ}

theorem word_power_coefficient_bound (p : RationalWords n) (hp : p.coeff 1 = 0)
    (hbound : ∀ w, |p.coeff w| ≤ 1) (k : ℕ) (w : FreeMonoid (Fin n)) (hw : 0 < w.length) :
    |(p ^ (k + 1)).coeff w| ≤ ((w.length - 1).choose k : ℚ) := by
  induction k generalizing w with
  | zero => simpa only [zero_add, pow_one, Nat.choose_zero_right, Nat.cast_one] using hbound w
  | succ k ih =>
    rw [pow_succ p (k + 1), word_coeff_mul]
    have hterm (i : Fin (w.length + 1)) :
        |(p ^ (k + 1)).coeff (wordSplit w i).1 * p.coeff (wordSplit w i).2| ≤
          if 0 < i.val ∧ i.val < w.length then ((i.val - 1).choose k : ℚ) else 0 := by
      have hlen : (wordSplit w i).1.length + (wordSplit w i).2.length = w.length := by
        rw [← FreeMonoid.length_mul, wordSplit_mul]
      rw [wordSplit_left_length] at hlen
      by_cases hi0 : i.val = 0
      · have hz : (p ^ (k + 1)).coeff (wordSplit w i).1 = 0 :=
          wordMinimumDegree_pow hp (k + 1) _ (by rw [wordSplit_left_length, hi0]; omega)
        simp [hi0, hz]
      · by_cases hiw : i.val = w.length
        · have hz : (wordSplit w i).2 = 1 :=
            FreeMonoid.length_eq_zero.mp (by omega)
          simp [hiw, hz, hp]
        · have hi : 0 < i.val ∧ i.val < w.length := by omega
          rw [ite_eq_left hi, abs_mul]
          have hb := ih (wordSplit w i).1 (by rw [wordSplit_left_length]; exact hi.1)
          rw [wordSplit_left_length] at hb
          exact (mul_le_mul hb (hbound _) (abs_nonneg _) (Nat.cast_nonneg _)).trans_eq (mul_one _)
    calc
      _ ≤ ∑ i : Fin (w.length + 1),
          |(p ^ (k + 1)).coeff (wordSplit w i).1 * p.coeff (wordSplit w i).2| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin (w.length + 1),
          if 0 < i.val ∧ i.val < w.length then ((i.val - 1).choose k : ℚ) else 0 :=
        Finset.sum_le_sum (fun i _ => hterm i)
      _ = ((w.length - 1).choose (k + 1) : ℚ) := by
        exact_mod_cast sum_internal_word_cuts w.length k hw

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_FiniteLogCoefficientBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficient bounds for the finite logarithm of a word polynomial -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

theorem finiteLog_coefficient_bound {n : ℕ} (p : RationalWords n) (c : ℕ)
    (hp : p.coeff 1 = 0) (hbound : ∀ w, |p.coeff w| ≤ 1)
    (w : FreeMonoid (Fin n)) (hw : 0 < w.length) (hc : w.length ≤ c + 1) :
    |(finiteNilpotentLog (c + 1) p).coeff w| ≤ (2 : ℚ) ^ c := by
  rw [finiteNilpotentLog_sum]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
  calc
    _ ≤ ∑ k : Fin c, |((-1 : ℚ) ^ (k.val + 2) / (k.val + 1)) *
        (p ^ (k.val + 1)).coeff w| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin c, ((w.length - 1).choose k.val : ℚ) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      have hs : |(-1 : ℚ) ^ (k.val + 2) / (k.val + 1)| ≤ 1 := by
        simp only [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_nonneg (by positivity : (0 : ℚ) ≤ k.val + 1), one_div]
        exact inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg _))
      exact (mul_le_mul hs (word_power_coefficient_bound p hp hbound k.val w hw)
        (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ ≤ (2 : ℚ) ^ c := by
      have h := sum_choose_initial_le (w.length - 1) c (by omega)
      rw [← Fin.sum_univ_eq_sum_range] at h
      exact_mod_cast h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GroupLikeNilpotentLogarithm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithm of a unipotent group-like element is primitive -/

noncomputable section
namespace PolycyclicRecognition

open TensorProduct
open scoped TensorProduct

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [Algebra ℚ A]

theorem nilpotentLog_groupLike
    (Δ : A →ₐ[R] A ⊗[R] A) (a : A) (ha : IsNilpotent a)
    (hΔ : Δ (1 + a) = (1 + a) ⊗ₜ[R] (1 + a)) :
    Δ (nilpotentLog a) =
      nilpotentLog a ⊗ₜ[R] (1 : A) + (1 : A) ⊗ₜ[R] nilpotentLog a := by
  let l : A →+* A ⊗[R] A := Algebra.TensorProduct.includeLeftRingHom
  let r : A →+* A ⊗[R] A := Algebra.TensorProduct.includeRight.toRingHom
  have hl (x : A) : l x = x ⊗ₜ[R] (1 : A) := rfl
  have hr (x : A) : r x = (1 : A) ⊗ₜ[R] x := rfl
  have hc : Commute (l a) (r a) := by
    change Commute (a ⊗ₜ[R] (1 : A)) ((1 : A) ⊗ₜ[R] a)
    change (a ⊗ₜ[R] (1 : A)) * ((1 : A) ⊗ₜ[R] a) =
      ((1 : A) ⊗ₜ[R] a) * (a ⊗ₜ[R] (1 : A))
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hf : (1 + a) ⊗ₜ[R] (1 + a) = (1 + l a) * (1 + r a) := by
    simp only [hl, hr, add_tmul, tmul_add, add_mul, mul_add, one_mul, mul_one,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.one_def]
  have hd : Δ a = (1 + l a) * (1 + r a) - 1 := by
    rw [← hf, ← hΔ, map_add, map_one, add_sub_cancel_left]
  change Δ.toRingHom (nilpotentLog a) = _
  rw [← nilpotentLog_map Δ.toRingHom a ha]
  change nilpotentLog (Δ a) = _
  rw [hd, nilpotentLog_unipotent_mul hc (ha.map l) (ha.map r),
    nilpotentLog_map l a ha, nilpotentLog_map r a ha, hl, hr]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_WordTensorConvolution
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The antipode and degree convolutions for rational words -/

noncomputable section
namespace PolycyclicRecognition

open TensorProduct
open scoped TensorProduct

variable {n : ℕ}

theorem wordAntipodeConvolution_letter_mul (i : Fin n)
    (u : RationalWords n ⊗[ℚ] RationalWords n) :
    wordAntipodeConvolution
        ((rationalWordLetter i ⊗ₜ[ℚ] 1 + 1 ⊗ₜ[ℚ] rationalWordLetter i) * u) =
      rationalWordLetter i * wordAntipodeConvolution u -
        wordAntipodeConvolution u * rationalWordLetter i := by
  induction u using OAI.tensorInductionOn with
  | tmul p q =>
    simp only [add_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_add,
      wordAntipodeConvolution_tmul, rationalWordAntipode_letter_mul]
    noncomm_ring
  | add u v hu hv =>
    rw [mul_add, map_add, hu, hv]
    simp only [map_add, mul_add, add_mul]
    abel

theorem wordDegreeConvolution_letter_mul (i : Fin n)
    (u : RationalWords n ⊗[ℚ] RationalWords n) :
    wordDegreeConvolution
        ((rationalWordLetter i ⊗ₜ[ℚ] 1 + 1 ⊗ₜ[ℚ] rationalWordLetter i) * u) =
      rationalWordLetter i * wordAntipodeConvolution u +
        rationalWordLetter i * wordDegreeConvolution u -
        wordDegreeConvolution u * rationalWordLetter i := by
  induction u using OAI.tensorInductionOn with
  | tmul p q =>
    simp only [add_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_add,
      wordAntipodeConvolution_tmul, wordDegreeConvolution_tmul,
      rationalWordDegree_letter_mul, rationalWordAntipode_letter_mul]
    noncomm_ring
  | add u v hu hv =>
    rw [mul_add, map_add, hu, hv]
    simp only [map_add, mul_add, add_mul]
    abel

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PrimitiveWordProjection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Dynkin projection identity for primitive rational words -/

noncomputable section
namespace PolycyclicRecognition

open TensorProduct
open scoped TensorProduct

variable {n : ℕ}

theorem wordAntipodeConvolution_coproduct (p : RationalWords n) :
    wordAntipodeConvolution (rationalWordCoproduct p) =
      rationalWordAugmentation p • (1 : RationalWords n) := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change wordAntipodeConvolution (rationalWordCoproduct (MonoidAlgebra.single w 1)) =
      rationalWordAugmentation (MonoidAlgebra.single w 1) • (1 : RationalWords n)
    induction w using FreeMonoid.recOn with
    | one =>
      simp only [← MonoidAlgebra.one_def, map_one, one_smul]
      change wordAntipodeConvolution (1 ⊗ₜ[ℚ] 1) = 1
      simp
    | of_mul i w ih =>
      have h : MonoidAlgebra.single (FreeMonoid.of i * w) (1 : ℚ) =
          rationalWordLetter i * MonoidAlgebra.single w 1 := by
        simp [rationalWordLetter]
      rw [h, map_mul, rationalWordCoproduct_letter,
        wordAntipodeConvolution_letter_mul, ih]
      simp [rationalWordAugmentation, rationalWordLetter, rationalWordEvaluation_single,
        Algebra.mul_smul_comm]
  | add p q hp hq =>
    simp only [map_add, hp, hq, add_smul]
  | smul r p hp =>
    simp only [map_smul, hp, smul_smul, smul_eq_mul]

theorem wordDegreeConvolution_coproduct (p : RationalWords n) :
    wordDegreeConvolution (rationalWordCoproduct p) =
      wordLieProjection rationalWordLetter p := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change wordDegreeConvolution (rationalWordCoproduct (MonoidAlgebra.single w 1)) =
      wordLieProjection rationalWordLetter (MonoidAlgebra.single w 1)
    induction w using FreeMonoid.recOn with
    | one =>
      rw [← MonoidAlgebra.one_def, map_one]
      change wordDegreeConvolution (1 ⊗ₜ[ℚ] 1) = _
      rw [wordDegreeConvolution_tmul, rationalWordDegree_one, zero_mul,
        MonoidAlgebra.one_def, wordLieProjection_single]
      simp [wordRightLie]
    | of_mul i w ih =>
      have h : MonoidAlgebra.single (FreeMonoid.of i * w) (1 : ℚ) =
          rationalWordLetter i * MonoidAlgebra.single w 1 := by
        simp [rationalWordLetter]
      rw [h, map_mul, rationalWordCoproduct_letter,
        wordDegreeConvolution_letter_mul, wordAntipodeConvolution_coproduct, ih,
        wordLieProjection_letter_mul, rationalWordAugmentation_eq_coeff]
      simp only [Algebra.mul_smul_comm, mul_one]
      abel
  | add p q hp hq => simp only [map_add, hp, hq]
  | smul r p hp => simp only [map_smul, hp]

/-- Primitive words are sent to their degree derivative by the Dynkin projection. -/
theorem IsPrimitiveRationalWord.projection_eq_degree {p : RationalWords n}
    (hp : IsPrimitiveRationalWord p) :
    wordLieProjection rationalWordLetter p = rationalWordDegree p := by
  rw [← wordDegreeConvolution_coproduct, hp]
  simp

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_HomogeneousWordProjection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Homogeneous primitive words and their right-nested Lie expressions -/

noncomputable section
namespace PolycyclicRecognition

variable {n : ℕ}

variable {A : Type*} [Ring A] [Algebra ℚ A] (X : Fin n → A)

/-- The degree identity holds after substitution in any rational associative algebra. -/
theorem primitive_homogeneous_word_projection {p : RationalWords n} {d : ℕ}
    (hp : IsPrimitiveRationalWord p) (hd : IsHomogeneousRationalWord p d) :
    wordLieProjection X p = (d : ℚ) • rationalWordEvaluation X p := by
  rw [← rationalWordEvaluation_projection, hp.projection_eq_degree, hd.degree_eq, map_smul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_HomogeneousWordCoefficients
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.wordBasisOfDet_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite right-nested coefficients of homogeneous primitive words -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {n d : ℕ}

theorem wordOfFn_injective : Function.Injective (wordOfFn : (Fin d → Fin n) → _) := by
  intro f g h
  apply List.ofFn_injective
  exact congrArg FreeMonoid.toList h

attribute [local instance 100] LieRing.ofAssociativeRing

theorem wordRightLie_ofFn {A : Type*} [Ring A] [Algebra ℚ A]
    (X : Fin n → A) (d : ℕ) (w : Fin (d + 1) → Fin n) :
    wordRightLie X (List.ofFn w) = evalBracketWord X (rightNestedWord d w) := by
  induction d with
  | zero => simp [List.ofFn_succ, wordRightLie, rightNestedWord]
  | succ d ih =>
    rw [List.ofFn_succ]
    have htail : List.ofFn (fun i => w i.succ) ≠ [] := by
      intro h
      have := congrArg List.length h
      simp at this
    cases h : List.ofFn (fun i => w i.succ) with
    | nil => exact (htail h).elim
    | cons i l =>
      change X (w 0) * wordRightLie X (i :: l) -
        wordRightLie X (i :: l) * X (w 0) = _
      rw [← h, ih]
      rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_MonoidTensorCoordinates
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplicative coordinates for tensors of monoid algebras -/

noncomputable section
namespace PolycyclicRecognition

open TensorProduct
open scoped TensorProduct

variable (R M N : Type*) [CommRing R] [Monoid M] [Monoid N]

theorem monoidTensorCoordinates_eq_tensorEquiv
    (x : MonoidAlgebra R M ⊗[R] MonoidAlgebra R N) :
    monoidTensorCoordinates R M N x = MonoidAlgebra.tensorEquiv R x := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul p q =>
    induction p using MonoidAlgebra.induction_linear with
    | zero => simp
    | add p p' hp hp' => simp only [add_tmul, map_add, hp, hp']
    | single m a =>
      induction q using MonoidAlgebra.induction_linear with
      | zero => simp
      | add q q' hq hq' => simp only [tmul_add, map_add, hq, hq']
      | single n b =>
        rw [monoidTensorCoordinates_single, MonoidAlgebra.tensorEquiv_single_tmul_single]

theorem monoidTensorCoordinates_injective : Function.Injective (monoidTensorCoordinates R M N) := by
  intro x y h
  apply (MonoidAlgebra.tensorEquiv R).injective
  simpa only [monoidTensorCoordinates_eq_tensorEquiv] using h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PrimitiveNilpotentExponential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products of exponentials in the primitive tensor coproduct -/

noncomputable section
namespace PolycyclicRecognition

open TensorProduct
open scoped TensorProduct

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [Algebra ℚ A]

theorem log_product_nilpotentExp_primitive (Δ : A →ₐ[R] A ⊗[R] A) (L : List A)
    (hL : ∀ a ∈ L, IsNilpotent a ∧ Δ a = a ⊗ₜ[R] (1 : A) + (1 : A) ⊗ₜ[R] a)
    (hu : IsNilpotent ((L.map IsNilpotent.exp).prod - 1)) :
    Δ (nilpotentLog ((L.map IsNilpotent.exp).prod - 1)) =
      nilpotentLog ((L.map IsNilpotent.exp).prod - 1) ⊗ₜ[R] (1 : A) +
      (1 : A) ⊗ₜ[R] nilpotentLog ((L.map IsNilpotent.exp).prod - 1) := by
  apply nilpotentLog_groupLike Δ _ hu
  simpa only [add_sub_cancel] using product_nilpotentExp_primitive Δ L hL

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ScalarNilpotentExponential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential products with a common nilpotent scalar -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A]

theorem nilpotent_exp_sub_one_factor (a : A) (ha : IsNilpotent a) :
    ∃ b : A, IsNilpotent.exp a - 1 = a * b := by
  have hn : a ^ (nilpotencyClass a + 1) = 0 := by
    rw [pow_succ, pow_nilpotencyClass ha, zero_mul]
  let F := nilpotentPowerSeriesEval a (nilpotencyClass a) hn
  have hc : (PowerSeries.exp ℚ - 1).constantCoeff = 0 := by simp
  obtain ⟨q, hq⟩ := PowerSeries.X_dvd_iff.mpr hc
  refine ⟨F q, ?_⟩
  calc
    IsNilpotent.exp a - 1 = F (PowerSeries.exp ℚ - 1) := by
      rw [map_sub, nilpotentPowerSeriesEval_exp, map_one]
    _ = a * F q := by rw [hq, map_mul, nilpotentPowerSeriesEval_X]

variable {R : Type*} [CommRing R] [Algebra R A]

theorem scalar_nilpotent_exp_product_factor (t : R) (ht : IsNilpotent t) (L : List A) :
    ∃ b : A, (L.map (fun a => IsNilpotent.exp (t • a))).prod - 1 = t • b := by
  have hn (a : A) : IsNilpotent (t • a) := by
    obtain ⟨k, hk⟩ := ht
    exact ⟨k, by rw [smul_pow, hk, zero_smul]⟩
  induction L with
  | nil => exact ⟨0, by simp⟩
  | cons a L ih =>
    obtain ⟨b, hb⟩ := nilpotent_exp_sub_one_factor (t • a) (hn a)
    obtain ⟨c, hc⟩ := ih
    refine ⟨(a * b) * (L.map (fun a => IsNilpotent.exp (t • a))).prod + c, ?_⟩
    rw [List.map_cons, List.prod_cons, smul_add, ← smul_mul_assoc,
      ← smul_mul_assoc, ← hb, ← hc]
    noncomm_ring

theorem scalar_nilpotent_exp_product_pow (t : R) (N : ℕ) (ht : t ^ N = 0) (L : List A) :
    ((L.map (fun a => IsNilpotent.exp (t • a))).prod - 1) ^ N = 0 := by
  obtain ⟨b, hb⟩ := scalar_nilpotent_exp_product_factor t ⟨N, ht⟩ L
  rw [hb, smul_pow, ht, zero_smul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TruncatedWordExponential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The universal exponential product over truncated rational scalars -/

noncomputable section
namespace PolycyclicRecognition

open TensorProduct
open scoped TensorProduct

variable (c n : ℕ)

theorem truncatedWordExponentialProduct_pow :
    (truncatedWordExponentialProduct c n - 1) ^ (c + 1) = 0 := by
  simpa only [List.map_ofFn, Function.comp_def, truncatedWordExponentialProduct]
    using scalar_nilpotent_exp_product_pow
    (truncatedScalarParameter c) (c + 1) (truncatedScalarParameter_pow c)
    (List.ofFn (truncatedWordLetter c n))

theorem truncatedWordLogarithm_primitive :
    truncatedWordCoproduct c n (truncatedWordLogarithm c n) =
      truncatedWordLogarithm c n ⊗ₜ[TruncatedRationalScalars c] (1 : TruncatedWords c n) +
        (1 : TruncatedWords c n) ⊗ₜ[TruncatedRationalScalars c] truncatedWordLogarithm c n := by
  let L := List.ofFn (fun i : Fin n =>
    truncatedScalarParameter c • truncatedWordLetter c n i)
  have hL (a : TruncatedWords c n) (ha : a ∈ L) :
      IsNilpotent a ∧ truncatedWordCoproduct c n a =
        a ⊗ₜ[TruncatedRationalScalars c] (1 : TruncatedWords c n) +
          (1 : TruncatedWords c n) ⊗ₜ[TruncatedRationalScalars c] a := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact ⟨⟨c + 1, by rw [smul_pow, truncatedScalarParameter_pow, zero_smul]⟩,
      truncatedWordCoproduct_parameter_letter c n i⟩
  have hu := truncatedWordExponentialProduct_pow c n
  have h := log_product_nilpotentExp_primitive (truncatedWordCoproduct c n) L hL
    (show IsNilpotent ((L.map IsNilpotent.exp).prod - 1) from
      ⟨c + 1, by simpa only [L, List.map_ofFn, Function.comp_def,
        truncatedWordExponentialProduct] using hu⟩)
  have he : (L.map IsNilpotent.exp).prod = truncatedWordExponentialProduct c n := by
    simp only [L, List.map_ofFn, Function.comp_def, truncatedWordExponentialProduct]
  rw [he, nilpotentLog_eq_of_pow _ ⟨_, hu⟩ _ hu] at h
  exact h

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TruncatedPrimitiveCoefficients
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Primitive rational coefficients of the truncated universal logarithm -/

noncomputable section
namespace PolycyclicRecognition

open TensorProduct
open scoped TensorProduct

variable (c n : ℕ)

theorem primitive_truncated_coefficient (f : TruncatedRationalScalars c →ₗ[ℚ] ℚ)
    (p : TruncatedWords c n)
    (hp : truncatedWordCoproduct c n p =
      p ⊗ₜ[TruncatedRationalScalars c] (1 : TruncatedWords c n) +
        (1 : TruncatedWords c n) ⊗ₜ[TruncatedRationalScalars c] p) :
    IsPrimitiveRationalWord (monoidCoefficientLinear f p) := by
  have h := congrArg (monoidTensorCoordinates (TruncatedRationalScalars c) _ _) hp
  rw [← pairedWordCoproduct_eq_truncated, map_add, monoidTensorCoordinates_tmul_one,
    monoidTensorCoordinates_one_tmul] at h
  have h' := congrArg (monoidCoefficientLinear f) h
  rw [coefficientLinear_pairedWordCoproduct, map_add, monoidCoefficientLinear_mapDomain,
    monoidCoefficientLinear_mapDomain] at h'
  unfold IsPrimitiveRationalWord
  apply monoidTensorCoordinates_injective ℚ (FreeMonoid (Fin n)) (FreeMonoid (Fin n))
  rw [← pairedWordCoproduct_eq_rational, map_add, monoidTensorCoordinates_tmul_one,
    monoidTensorCoordinates_one_tmul]
  exact h'

theorem universalLogarithmCoefficient_primitive (d : ℕ) :
    IsPrimitiveRationalWord (universalLogarithmCoefficient c n d) :=
  primitive_truncated_coefficient c n _ _ (truncatedWordLogarithm_primitive c n)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightedWordLogarithm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The universal logarithm preserves the scalar/word grading -/

noncomputable section
namespace PolycyclicRecognition

variable (c n : ℕ)

theorem weightedWordSubalgebra_exp_parameter_letter (i : Fin n) :
    IsNilpotent.exp (truncatedScalarParameter c • truncatedWordLetter c n i) ∈
      weightedWordSubalgebra c n := by
  have hn : (truncatedScalarParameter c • truncatedWordLetter c n i) ^ (c + 1) = 0 := by
    rw [smul_pow, truncatedScalarParameter_pow, zero_smul]
  rw [← nilpotentPowerSeriesEval_exp _ c hn]
  exact weightedWordSubalgebra_aeval c n (weightedWordSubalgebra_parameter_letter c n i) _

theorem weightedWordSubalgebra_exponentialProduct :
    truncatedWordExponentialProduct c n ∈ weightedWordSubalgebra c n := by
  apply (weightedWordSubalgebra c n).toSubmonoid.list_prod_mem
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  exact weightedWordSubalgebra_exp_parameter_letter c n i

theorem weightedWordLogarithm_mem :
    truncatedWordLogarithm c n ∈ weightedWordSpan c n := by
  exact weightedWordSubalgebra_aeval c n
    ((weightedWordSubalgebra c n).sub_mem (weightedWordSubalgebra_exponentialProduct c n)
      (weightedWordSubalgebra c n).one_mem) _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_HomogeneousUniversalLogarithm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Homogeneous Lie expansions of the universal logarithm coefficients -/

noncomputable section
namespace PolycyclicRecognition

variable {n d : ℕ}

theorem universalLogarithmCoefficient_homogeneous (c n d : ℕ) :
    IsHomogeneousRationalWord (universalLogarithmCoefficient c n d) d :=
  weightedWordSpan_coefficient_homogeneous c n d _ (weightedWordLogarithm_mem c n)

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LocallyBoundedDerivedSeries
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform derived-series bound passes from finitely generated subgroups -/
noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement
variable {G : Type} [Group G]

theorem ambientDerivedSeries_mono {H K : Subgroup G} (hHK : H ≤ K) (n : ℕ) :
    ambientDerivedSeries H n ≤ ambientDerivedSeries K n := by
  intro x hx
  obtain ⟨h, hh, rfl⟩ := hx
  refine ⟨Subgroup.inclusion hHK h, ?_, rfl⟩
  exact map_derivedSeries_le_derivedSeries (Subgroup.inclusion hHK) n ⟨h, hh, rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentWordEvaluation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential and logarithm identities under nilpotent substitution -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A] {c n : ℕ} (X : Fin n → A)
  (hX : ∀ w : FreeMonoid (Fin n), c < w.length → FreeMonoid.lift X w = 0)

include hX

theorem weightedWordSubstitution_exp_letter (i : Fin n) :
    weightedWordSubstitution X
      (IsNilpotent.exp (truncatedScalarParameter c • truncatedWordLetter c n i)) =
        IsNilpotent.exp (X i) := by
  have hn : (truncatedScalarParameter c • truncatedWordLetter c n i) ^ (c + 1) = 0 := by
    rw [smul_pow, truncatedScalarParameter_pow, zero_smul]
  rw [← nilpotentPowerSeriesEval_exp _ c hn]
  change weightedWordSubstitution X (Polynomial.aeval _ _) = _
  rw [weightedWordSubstitution_aeval X hX (weightedWordSubalgebra_parameter_letter c n i),
    weightedWordSubstitution_parameter_letter X hX]
  exact nilpotentPowerSeriesEval_exp _ c (nilpotent_word_letter_pow X hX i)

theorem weightedWordSubstitution_exponentialProduct :
    weightedWordSubstitution X (truncatedWordExponentialProduct c n) =
      (List.ofFn (fun i => IsNilpotent.exp (X i))).prod := by
  rw [truncatedWordExponentialProduct, weightedWordSubstitution_list_prod X hX]
  · simp only [List.map_ofFn, Function.comp_def, weightedWordSubstitution_exp_letter X hX]
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact weightedWordSubalgebra_exp_parameter_letter c n i

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RationalUniversalLogarithm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The rational polynomial underlying the universal truncated logarithm -/

noncomputable section
namespace PolycyclicRecognition

variable (c n : ℕ)

theorem rationalWordWeight_exponential (i : Fin n) :
    rationalWordWeight c n (rationalWordExponential c n i) =
      IsNilpotent.exp (truncatedScalarParameter c • truncatedWordLetter c n i) := by
  rw [rationalWordExponential, ← Polynomial.aeval_algHom_apply, rationalWordWeight_letter]
  exact nilpotentPowerSeriesEval_exp _ c (by rw [smul_pow, truncatedScalarParameter_pow, zero_smul])

theorem rationalWordWeight_exponentialProduct :
    rationalWordWeight c n (rationalExponentialProduct c n) = truncatedWordExponentialProduct c n := by
  simp only [rationalExponentialProduct, map_list_prod, List.map_ofFn, Function.comp_def,
    rationalWordWeight_exponential, truncatedWordExponentialProduct]

theorem rationalWordWeight_universalLogarithm :
    rationalWordWeight c n (rationalUniversalLogarithm c n) = truncatedWordLogarithm c n := by
  rw [rationalUniversalLogarithm, finiteNilpotentLog, ← Polynomial.aeval_algHom_apply,
    map_sub, rationalWordWeight_exponentialProduct, map_one]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_WeightedWordComponents
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit degree components of weighted words -/

noncomputable section
namespace PolycyclicRecognition

variable {c n d : ℕ}

theorem universalLogarithmCoefficient_zero (c n : ℕ) : universalLogarithmCoefficient c n 0 = 0 :=
  primitive_homogeneous_degree_zero (universalLogarithmCoefficient_primitive c n 0)
    (universalLogarithmCoefficient_homogeneous c n 0)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UniversalLogarithmWordCoefficients
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational coefficients of the universal logarithm -/

noncomputable section
namespace PolycyclicRecognition

variable {c n d : ℕ}

theorem universalLogarithmCoefficient_coeff (hd : d ≤ c) (w : FreeMonoid (Fin n)) :
    (universalLogarithmCoefficient c n d).coeff w =
      if w.length = d then (rationalUniversalLogarithm c n).coeff w else 0 := by
  rw [universalLogarithmCoefficient, ← rationalWordWeight_universalLogarithm]
  exact rationalWordWeight_coefficient _ hd w

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NilpotentUniversalLogarithm
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The universal logarithm evaluates to the actual finite logarithm -/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A] {c n : ℕ} (X : Fin n → A)
  (hX : ∀ w : FreeMonoid (Fin n), c < w.length → FreeMonoid.lift X w = 0)

include hX

theorem nilpotent_word_exp_product_pow :
    ((List.ofFn (fun i => IsNilpotent.exp (X i))).prod - 1) ^ (c + 1) = 0 := by
  have ha := (weightedWordSubalgebra c n).sub_mem
    (weightedWordSubalgebra_exponentialProduct c n) (weightedWordSubalgebra c n).one_mem
  have h : weightedWordSubstitution X (truncatedWordExponentialProduct c n - 1) ^ (c + 1) = 0 := by
    rw [← weightedWordSubstitution_pow X hX ha, truncatedWordExponentialProduct_pow, map_zero]
  rw [map_sub, weightedWordSubstitution_exponentialProduct X hX,
    weightedWordSubstitution_one X hX] at h
  exact h

theorem rationalUniversalLogarithm_eval :
    rationalWordEvaluation X (rationalUniversalLogarithm c n) =
      finiteNilpotentLog (c + 1) ((List.ofFn (fun i => IsNilpotent.exp (X i))).prod - 1) := by
  rw [← weightedWordSubstitution_weight X hX, rationalWordWeight_universalLogarithm]
  change weightedWordSubstitution X (Polynomial.aeval _ _) = _
  rw [weightedWordSubstitution_aeval X hX
    ((weightedWordSubalgebra c n).sub_mem (weightedWordSubalgebra_exponentialProduct c n)
      (weightedWordSubalgebra c n).one_mem),
    map_sub, weightedWordSubstitution_exponentialProduct X hX, weightedWordSubstitution_one X hX]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalizedFreeColimit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.IntegralProjectiveTower.instDirectedSystemNatCohomologyStageCoeLinearMapIntIdForward _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.telescopeAugmentation_epi _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.telescopeShift_inclusion _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.telescopeShift_succ _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.telescopeShift_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized free generators in a sequential coefficient colimit -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]
namespace SequentialRepresentationDiagram.ColimitCocone
variable {D : SequentialRepresentationDiagram G} {A : Rep.{0} ℤ G}
  (c : D.ColimitCocone A)

abbrev freeDiagram (_c : D.ColimitCocone A) : SequentialRepresentationDiagram G := D.mapFunctor normalizedFreeFunctor

def freeLimitGenerator (i : ℕ) (x : D.obj i) : c.freeDiagram.ModuleLimit :=
  Module.DirectLimit.of ℤ[G] ℕ _ c.freeDiagram.moduleMap i
    ((normalizedFreeRepresentation (D.obj i)).ρ.asModuleEquiv.symm
      (normalizedFreeGenerator (D.obj i) x))

theorem freeLimitGenerator_transport (i j : ℕ) (hij : i ≤ j) (x : D.obj i) :
    c.freeLimitGenerator i x = c.freeLimitGenerator j ((D.map i j hij).hom x) := by
  unfold freeLimitGenerator
  have he := Module.DirectLimit.of_f (R := ℤ[G]) (ι := ℕ)
    (G := fun k => (c.freeDiagram.obj k).ρ.asModule) (f := c.freeDiagram.moduleMap)
    (hij := hij) (x := (normalizedFreeRepresentation (D.obj i)).ρ.asModuleEquiv.symm
      (normalizedFreeGenerator (D.obj i) x))
  have hg : c.freeDiagram.moduleMap i j hij
      ((normalizedFreeRepresentation (D.obj i)).ρ.asModuleEquiv.symm
        (normalizedFreeGenerator (D.obj i) x)) =
      (normalizedFreeRepresentation (D.obj j)).ρ.asModuleEquiv.symm
        (normalizedFreeGenerator (D.obj j) ((D.map i j hij).hom x)) := by
    apply (normalizedFreeRepresentation (D.obj j)).ρ.asModuleEquiv.injective
    exact normalizedFreeMap_generator (D.map i j hij) x
  rw [hg] at he
  exact he.symm

@[simp]
theorem freeLimitGenerator_zero (i : ℕ) : c.freeLimitGenerator i 0 = 0 := by
  simp [freeLimitGenerator]
  exact (Module.DirectLimit.of ℤ[G] ℕ _ c.freeDiagram.moduleMap i).map_zero

theorem freeLimitGenerator_eq (i j : ℕ) (x : D.obj i) (y : D.obj j)
    (hxy : (c.ι i).hom x = (c.ι j).hom y) :
    c.freeLimitGenerator i x = c.freeLimitGenerator j y := by
  let k := max i j
  let xk := (D.map i k (le_max_left i j)).hom x
  let yk := (D.map j k (le_max_right i j)).hom y
  have he : (c.ι k).hom (xk - yk) = 0 := by
    rw [map_sub]
    have hx := ConcreteCategory.congr_hom (c.comm i k (le_max_left i j)) x
    have hy := ConcreteCategory.congr_hom (c.comm j k (le_max_right i j)) y
    change (c.ι k).hom xk = (c.ι i).hom x at hx
    change (c.ι k).hom yk = (c.ι j).hom y at hy
    rw [hx, hy, hxy, sub_self]
  obtain ⟨l, hkl, hl⟩ := c.zero_exact k (xk - yk) he
  have hl' : (D.map k l hkl).hom xk = (D.map k l hkl).hom yk := by
    exact sub_eq_zero.mp (by simpa only [map_sub] using hl)
  rw [c.freeLimitGenerator_transport i k (le_max_left i j),
    c.freeLimitGenerator_transport j k (le_max_right i j)]
  change c.freeLimitGenerator k xk = c.freeLimitGenerator k yk
  rw [c.freeLimitGenerator_transport k l hkl, c.freeLimitGenerator_transport k l hkl, hl']

theorem freeLimitGenerator_eq_zero (i : ℕ) (x : D.obj i) (hx : (c.ι i).hom x = 0) :
    c.freeLimitGenerator i x = 0 := by
  have he := c.freeLimitGenerator_eq i i x 0 (by simpa using hx)
  simpa using he

def normalizedFreeModuleBasis (B : Rep.{0} ℤ G) :
    Module.Basis {b : B // b ≠ 0} ℤ[G] (normalizedFreeRepresentation B).ρ.asModule :=
  Representation.freeAsModuleBasis ℤ G {b : B // b ≠ 0}

def freeModuleGenerator (B : Rep.{0} ℤ G) (x : B) : (normalizedFreeRepresentation B).ρ.asModule :=
  (normalizedFreeRepresentation B).ρ.asModuleEquiv.symm (normalizedFreeGenerator B x)

@[simp]
theorem freeModuleGenerator_zero (B : Rep.{0} ℤ G) : freeModuleGenerator B 0 = 0 := by
  simp [freeModuleGenerator]

theorem freeModuleGenerator_basis (B : Rep.{0} ℤ G) (x : B) (hx : x ≠ 0) :
    freeModuleGenerator B x = normalizedFreeModuleBasis B ⟨x, hx⟩ := by
  unfold freeModuleGenerator
  rw [normalizedFreeGenerator_of_ne_zero B x hx]
  rfl

def freeModuleCocone (i : ℕ) : (c.freeDiagram.obj i).ρ.asModule →ₗ[ℤ[G]]
    (normalizedFreeRepresentation A).ρ.asModule :=
  representationModuleHomEquiv ℤ G _ _ (normalizedFreeMap (c.ι i))

def freeModuleLift : c.freeDiagram.ModuleLimit →ₗ[ℤ[G]]
    (normalizedFreeRepresentation A).ρ.asModule :=
  Module.DirectLimit.lift ℤ[G] ℕ _ _ c.freeModuleCocone (by
    intro i j h x
    change representationModuleHomEquiv ℤ G _ _
      (normalizedFreeMap (D.map i j h) ≫ normalizedFreeMap (c.ι j)) x =
        representationModuleHomEquiv ℤ G _ _ (normalizedFreeMap (c.ι i)) x
    rw [← normalizedFreeMap_comp, c.comm])

theorem freeModuleLift_generator (i : ℕ) (x : D.obj i) :
    c.freeModuleLift (c.freeLimitGenerator i x) = freeModuleGenerator A ((c.ι i).hom x) := by
  unfold freeModuleLift freeLimitGenerator
  refine (Module.DirectLimit.lift_of c.freeModuleCocone _ _).trans ?_
  apply (normalizedFreeRepresentation A).ρ.asModuleEquiv.injective
  exact normalizedFreeMap_generator (c.ι i) x

def freeChosenLift (a : {a : A // a ≠ 0}) : c.freeDiagram.ModuleLimit :=
  c.freeLimitGenerator (Classical.choose (c.surj a.1))
    (Classical.choose (Classical.choose_spec (c.surj a.1)))

def freeModuleInverse : (normalizedFreeRepresentation A).ρ.asModule →ₗ[ℤ[G]]
    c.freeDiagram.ModuleLimit :=
  (normalizedFreeModuleBasis A).constr ℤ c.freeChosenLift

@[simp]
theorem freeModuleInverse_basis (a : {a : A // a ≠ 0}) :
    c.freeModuleInverse (normalizedFreeModuleBasis A a) = c.freeChosenLift a :=
  (normalizedFreeModuleBasis A).constr_basis ℤ c.freeChosenLift a

@[simp]
theorem freeLimitGenerator_basis (i : ℕ) (a : {a : D.obj i // a ≠ 0}) :
    Module.DirectLimit.of ℤ[G] ℕ _ c.freeDiagram.moduleMap i
      (normalizedFreeModuleBasis (D.obj i) a) = c.freeLimitGenerator i a.1 := by
  change Module.DirectLimit.of ℤ[G] ℕ _ c.freeDiagram.moduleMap i
      (normalizedFreeModuleBasis (D.obj i) a) =
    Module.DirectLimit.of ℤ[G] ℕ _ c.freeDiagram.moduleMap i (freeModuleGenerator (D.obj i) a.1)
  rw [freeModuleGenerator_basis (D.obj i) a.1 a.2]

theorem freeModuleLift_chosen (a : {a : A // a ≠ 0}) :
    c.freeModuleLift (c.freeChosenLift a) = freeModuleGenerator A a.1 := by
  unfold freeChosenLift
  rw [c.freeModuleLift_generator, Classical.choose_spec (Classical.choose_spec (c.surj a.1))]

theorem freeModuleInverse_generator (i : ℕ) (x : D.obj i) :
    c.freeModuleInverse (freeModuleGenerator A ((c.ι i).hom x)) = c.freeLimitGenerator i x := by
  classical
  by_cases hx : (c.ι i).hom x = 0
  · rw [hx, freeModuleGenerator_zero, map_zero, c.freeLimitGenerator_eq_zero i x hx]
  · rw [freeModuleGenerator_basis A _ hx]
    rw [c.freeModuleInverse_basis]
    unfold freeChosenLift
    apply c.freeLimitGenerator_eq
    exact Classical.choose_spec (Classical.choose_spec (c.surj ((c.ι i).hom x)))

theorem freeModuleLift_bijective : Function.Bijective c.freeModuleLift := by
  have hleft : c.freeModuleInverse.comp c.freeModuleLift = LinearMap.id := by
    apply Module.DirectLimit.hom_ext
    intro i
    apply (normalizedFreeModuleBasis (D.obj i)).ext
    intro a
    have hb := c.freeLimitGenerator_basis i a
    have hq := c.freeModuleLift_generator i a.1
    have hi := c.freeModuleInverse_generator i a.1
    exact (congrArg (fun z => c.freeModuleInverse (c.freeModuleLift z)) hb).trans
      ((congrArg c.freeModuleInverse hq).trans (hi.trans hb.symm))
  have hright : c.freeModuleLift.comp c.freeModuleInverse = LinearMap.id := by
    apply (normalizedFreeModuleBasis A).ext
    intro a
    simp only [LinearMap.comp_apply, LinearMap.id_apply, c.freeModuleInverse_basis,
      c.freeModuleLift_chosen]
    exact freeModuleGenerator_basis A a.1 a.2
  have hl : Function.LeftInverse c.freeModuleInverse c.freeModuleLift := fun x =>
    LinearMap.congr_fun hleft x
  have hr : Function.RightInverse c.freeModuleInverse c.freeModuleLift := fun x =>
    LinearMap.congr_fun hright x
  exact ⟨hl.injective, hr.surjective⟩

@[simp]
theorem freeModuleLift_of (i : ℕ) (x : (c.freeDiagram.obj i).ρ.asModule) :
    c.freeModuleLift (Module.DirectLimit.of ℤ[G] ℕ _ c.freeDiagram.moduleMap i x) =
      c.freeModuleCocone i x := Module.DirectLimit.lift_of _ _ _

def normalizedFree : (D.mapFunctor normalizedFreeFunctor).ColimitCocone
    (normalizedFreeRepresentation A) where
  ι i := normalizedFreeMap (c.ι i)
  comm i j h := by
    change normalizedFreeMap (D.map i j h) ≫ normalizedFreeMap (c.ι j) =
      normalizedFreeMap (c.ι i)
    rw [← normalizedFreeMap_comp, c.comm]
  surj x := by
    obtain ⟨z, hz⟩ := c.freeModuleLift_bijective.2
      ((normalizedFreeRepresentation A).ρ.asModuleEquiv.symm x)
    obtain ⟨i, y, rfl⟩ := Module.DirectLimit.exists_of z
    refine ⟨i, (normalizedFreeRepresentation (D.obj i)).ρ.asModuleEquiv y, ?_⟩
    rw [c.freeModuleLift_of] at hz
    have he := congrArg (normalizedFreeRepresentation A).ρ.asModuleEquiv hz
    exact he
  zero_exact i x hx := by
    let y := (normalizedFreeRepresentation (D.obj i)).ρ.asModuleEquiv.symm x
    have hz : Module.DirectLimit.of ℤ[G] ℕ _ c.freeDiagram.moduleMap i y = 0 := by
      apply c.freeModuleLift_bijective.1
      calc
        _ = c.freeModuleCocone i y := c.freeModuleLift_of i y
        _ = 0 := by
          apply (normalizedFreeRepresentation A).ρ.asModuleEquiv.injective
          exact hx
        _ = c.freeModuleLift 0 := (map_zero c.freeModuleLift).symm
    obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact hz
    refine ⟨j, hij, ?_⟩
    have he := congrArg (normalizedFreeRepresentation (D.obj j)).ρ.asModuleEquiv hj
    exact he

end SequentialRepresentationDiagram.ColimitCocone
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CompletedCohomology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Degree-zero complete cohomology from normalized syzygies

The transition maps are the actual connecting homomorphisms of the natural
short exact free-cover sequences. No vanishing theorem is assumed here.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem normalizedSyzygyConnecting_natural {A B : Rep.{0} ℤ G} (f : A ⟶ B) (n : ℕ) :
    normalizedSyzygyConnecting A n ≫
        groupCohomology.map (MonoidHom.id G) ((iteratedNormalizedSyzygy (n + 1)).map f) (n + 1) =
      groupCohomology.map (MonoidHom.id G) ((iteratedNormalizedSyzygy n).map f) n ≫
        normalizedSyzygyConnecting B n :=
  groupCohomology.δ_naturality
    (normalizedSyzygySequence_shortExact ((iteratedNormalizedSyzygy n).obj A))
    (normalizedSyzygySequence_shortExact ((iteratedNormalizedSyzygy n).obj B))
    (normalizedSyzygySequenceMap ((iteratedNormalizedSyzygy n).map f)) n (n + 1) rfl

theorem normalizedCohomologyForward_natural {A B : Rep.{0} ℤ G} (f : A ⟶ B)
    (i j : ℕ) (h : i ≤ j) (x : normalizedCohomologyStage A i) :
    normalizedCohomologyStageMap f j (normalizedCohomologyForward A i j h x) =
      normalizedCohomologyForward B i j h (normalizedCohomologyStageMap f i x) := by
  induction h with
  | refl =>
    simp only [normalizedCohomologyForward, Nat.leRecOn_self]
    rfl
  | @step j h ih =>
    change normalizedCohomologyStageMap f (j + 1)
      (Nat.leRecOn (C := normalizedCohomologyStage A) _
        (fun {k} => (normalizedSyzygyConnecting A k).hom) x) =
      Nat.leRecOn (C := normalizedCohomologyStage B) _
        (fun {k} => (normalizedSyzygyConnecting B k).hom) _
    rw [Nat.leRecOn_succ h, Nat.leRecOn_succ h]
    have hn := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (normalizedSyzygyConnecting_natural f j)) (normalizedCohomologyForward A i j h x)
    change normalizedCohomologyStageMap f (j + 1)
      ((normalizedSyzygyConnecting A j).hom _) =
        (normalizedSyzygyConnecting B j).hom
          (normalizedCohomologyForward B i j h (normalizedCohomologyStageMap f i x))
    rw [← ih]
    exact hn

def completedCohomologyMap {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    CompletedCohomology A →ₗ[ℤ] CompletedCohomology B :=
  Module.DirectLimit.map (f := normalizedCohomologyForward A)
    (f' := normalizedCohomologyForward B) (normalizedCohomologyStageMap f)
    (fun i j h => by
      apply LinearMap.ext
      exact normalizedCohomologyForward_natural f i j h)

@[simp]
theorem completedCohomologyMap_of {A B : Rep.{0} ℤ G} (f : A ⟶ B) (i : ℕ)
    (x : normalizedCohomologyStage A i) :
    completedCohomologyMap f
      (Module.DirectLimit.of ℤ ℕ _ (normalizedCohomologyForward A) i x) =
    Module.DirectLimit.of ℤ ℕ _ (normalizedCohomologyForward B) i
      (normalizedCohomologyStageMap f i x) := by
  exact Module.DirectLimit.map_apply_of (normalizedCohomologyStageMap f)
    (fun i j h => by
      apply LinearMap.ext
      exact normalizedCohomologyForward_natural f i j h) x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NormalizedProjectiveResolution
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.repCofiber_projective _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.freeLimitGenerator_basis _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.freeModuleGenerator_zero _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.freeModuleInverse_basis _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.freeModuleLift_of _root_.OAI.PolycyclicRecognition.induction_mk_left_inv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The projective resolution determined by normalized free covers

Its quotient syzygy in degree n is the actual n-fold normalized kernel used
in the complete-cohomology construction.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

def normalizedFreeStep (A : Rep.{0} ℤ G) :
    normalizedFreeRepresentation (normalizedSyzygy A) ⟶ normalizedFreeRepresentation A :=
  normalizedFreeAugmentation (normalizedSyzygy A) ≫ kernel.ι (normalizedFreeAugmentation A)

theorem normalizedFreeStep_comp (A : Rep.{0} ℤ G) :
    normalizedFreeStep A ≫ normalizedFreeAugmentation A = 0 := by
  simp [normalizedFreeStep]

theorem normalizedFreeStep_exact (A : Rep.{0} ℤ G) :
    (ShortComplex.mk (normalizedFreeStep A) (normalizedFreeAugmentation A)
      (normalizedFreeStep_comp A)).Exact := by
  apply (rep_shortComplex_exact_iff _).mpr
  intro x hx
  obtain ⟨k, hk⟩ := (rep_shortComplex_exact_iff _).mp
    (normalizedSyzygySequence_shortExact A).exact x hx
  obtain ⟨p, hp⟩ := (Rep.epi_iff_surjective
    (normalizedFreeAugmentation (normalizedSyzygy A))).mp inferInstance k
  refine ⟨p, ?_⟩
  change (kernel.ι (normalizedFreeAugmentation A)).hom
    ((normalizedFreeAugmentation (normalizedSyzygy A)).hom p) = x
  rw [hp]
  exact hk

def normalizedResolutionTerm (A : Rep.{0} ℤ G) (n : ℕ) : Rep.{0} ℤ G :=
  normalizedFreeRepresentation ((iteratedNormalizedSyzygy n).obj A)

def normalizedResolutionDifferential (A : Rep.{0} ℤ G) (n : ℕ) :
    normalizedResolutionTerm A (n + 1) ⟶ normalizedResolutionTerm A n :=
  normalizedFreeStep ((iteratedNormalizedSyzygy n).obj A)

def normalizedResolutionComplex (A : Rep.{0} ℤ G) : ChainComplex (Rep.{0} ℤ G) ℕ :=
  ChainComplex.of (normalizedResolutionTerm A) (normalizedResolutionDifferential A) (by
    intro n
    let B := (iteratedNormalizedSyzygy n).obj A
    change normalizedFreeStep (normalizedSyzygy B) ≫
      (normalizedFreeAugmentation (normalizedSyzygy B) ≫
        kernel.ι (normalizedFreeAugmentation B)) = 0
    rw [← Category.assoc, normalizedFreeStep_comp, zero_comp])

@[simp]
theorem normalizedResolutionComplex_d (A : Rep.{0} ℤ G) (n : ℕ) :
    (normalizedResolutionComplex A).d (n + 1) n =
      normalizedFreeStep ((iteratedNormalizedSyzygy n).obj A) := by
  exact ChainComplex.of_d (normalizedResolutionTerm A) (normalizedResolutionDifferential A) n

instance normalizedResolutionComplex_projective (A : Rep.{0} ℤ G) (n : ℕ) :
    Projective ((normalizedResolutionComplex A).X n) :=
  inferInstanceAs (Projective (normalizedFreeRepresentation ((iteratedNormalizedSyzygy n).obj A)))

theorem normalizedResolutionComplex_exact (A : Rep.{0} ℤ G) (n : ℕ) :
    (normalizedResolutionComplex A).ExactAt (n + 1) := by
  rw [exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  apply (rep_shortComplex_exact_iff _).mpr
  intro x hx
  change ((normalizedResolutionComplex A).d (n + 1) n).hom x = 0 at hx
  rw [normalizedResolutionComplex_d] at hx
  have hx' : (normalizedFreeAugmentation ((iteratedNormalizedSyzygy (n + 1)).obj A)).hom x = 0 := by
    apply (Rep.mono_iff_injective
      (kernel.ι (normalizedFreeAugmentation ((iteratedNormalizedSyzygy n).obj A)))).mp
      inferInstance
    change (kernel.ι (normalizedFreeAugmentation ((iteratedNormalizedSyzygy n).obj A))).hom
      ((normalizedFreeAugmentation ((iteratedNormalizedSyzygy (n + 1)).obj A)).hom x) = 0 at hx
    exact hx.trans (map_zero (kernel.ι (normalizedFreeAugmentation
      ((iteratedNormalizedSyzygy n).obj A))).hom).symm
  change ∃ y, ((normalizedResolutionComplex A).d (n + 2) (n + 1)).hom y = x
  rw [show n + 2 = (n + 1) + 1 by omega, normalizedResolutionComplex_d]
  exact (rep_shortComplex_exact_iff _).mp
    (normalizedFreeStep_exact ((iteratedNormalizedSyzygy (n + 1)).obj A)) x hx'

def normalizedResolutionAugmentation (A : Rep.{0} ℤ G) :
    normalizedResolutionComplex A ⟶ (ChainComplex.single₀ (Rep.{0} ℤ G)).obj A :=
  ((normalizedResolutionComplex A).toSingle₀Equiv A).symm
    ⟨normalizedFreeAugmentation A, by
      rw [normalizedResolutionComplex_d]
      exact normalizedFreeStep_comp A⟩

theorem normalizedResolutionAugmentation_quasiIso (A : Rep.{0} ℤ G) :
    QuasiIso (normalizedResolutionAugmentation A) where
  quasiIsoAt i := by
    cases i with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_of_zeros' _ (by rfl) rfl rfl]
      constructor
      · exact normalizedFreeStep_exact A
      · exact normalizedFreeAugmentation_epi A
    | succ n =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)]
      exact normalizedResolutionComplex_exact A n

def normalizedProjectiveResolution (A : Rep.{0} ℤ G) : ProjectiveResolution A where
  complex := normalizedResolutionComplex A
  projective := normalizedResolutionComplex_projective A
  π := normalizedResolutionAugmentation A
  quasiIso := normalizedResolutionAugmentation_quasiIso A

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NormalizedResolutionSyzygies
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quotient terms of the normalized projective resolution -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

def normalizedResolutionProjection (A : Rep.{0} ℤ G) (n : ℕ) :
    (normalizedResolutionComplex A).X n ⟶ (iteratedNormalizedSyzygy n).obj A :=
  normalizedFreeAugmentation ((iteratedNormalizedSyzygy n).obj A)

theorem normalizedResolution_d_projection (A : Rep.{0} ℤ G) (n : ℕ) :
    (normalizedResolutionComplex A).d (n + 1) n ≫ normalizedResolutionProjection A n = 0 := by
  rw [normalizedResolutionComplex_d]
  exact normalizedFreeStep_comp ((iteratedNormalizedSyzygy n).obj A)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_NormalizedIdentityClass
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identity cocycles in the normalized resolution

The projection onto the n-th syzygy is a cocycle. If its class vanishes in a
positive degree, the next kernel inclusion splits; this gives a projective
syzygy and hence finite integral dimension for the trivial coefficient.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def normalizedIdentityCycle (A : Rep.{0} ℤ G) (n : ℕ) :
    ((normalizedResolutionComplex A).linearYonedaObj ℤ
      ((iteratedNormalizedSyzygy n).obj A)).cycles n := by
  let C := (normalizedResolutionComplex A).linearYonedaObj ℤ
    ((iteratedNormalizedSyzygy n).obj A)
  exact C.cyclesMk (normalizedResolutionProjection A n) (n + 1) (by simp) (by
    change (normalizedResolutionComplex A).d (n + 1) n ≫
      normalizedResolutionProjection A n = 0
    exact normalizedResolution_d_projection A n)

def normalizedIdentityClass (A : Rep.{0} ℤ G) (n : ℕ) :
    ((normalizedResolutionComplex A).linearYonedaObj ℤ
      ((iteratedNormalizedSyzygy n).obj A)).homology n :=
  ((normalizedResolutionComplex A).linearYonedaObj ℤ
    ((iteratedNormalizedSyzygy n).obj A)).homologyπ n (normalizedIdentityCycle A n)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialBilinearWords
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial coordinate formulas for the finite BCH words -/

noncomputable section
namespace PolycyclicRecognition
variable {I J : Type*} {d : ℕ}

theorem coordinatePolynomial_evalBilinearWord
    (B : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (X : (I → ℝ) → J → (Fin d → ℝ))
    (hX : ∀ j, IsCoordinatePolynomial (fun x => X x j)) (w : FreeMagma J) :
    IsCoordinatePolynomial (fun x => evalBilinearWord B (X x) w) := by
  induction w using FreeMagma.rec with
  | of j => exact hX j
  | mul a b ha hb =>
    exact IsCoordinatePolynomial.bilinear B.toLinearMap₁₂ ha hb

theorem coordinatePolynomial_bilinearDynkin {c n : ℕ} (a : DynkinCoefficients c n)
    (B : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (X : (I → ℝ) → Fin n → (Fin d → ℝ))
    (hX : ∀ j, IsCoordinatePolynomial (fun x => X x j)) :
    IsCoordinatePolynomial (fun x => bilinearDynkinPolynomial a B (X x)) := by
  apply IsCoordinatePolynomial.sum Finset.univ
  intro k _
  apply IsCoordinatePolynomial.sum Finset.univ
  intro w _
  exact (coordinatePolynomial_evalBilinearWord B X hX (rightNestedWord k.val w)).smul _

theorem coordinatePolynomial_dynkinProduct {c : ℕ} (a : DynkinCoefficients c 2)
    (B : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) :
    IsCoordinatePolynomial (fun x : (Fin d ⊕ Fin d) → ℝ =>
      dynkinProduct a B (x ∘ Sum.inl) (x ∘ Sum.inr)) := by
  apply coordinatePolynomial_bilinearDynkin
  intro i
  fin_cases i
  · exact IsCoordinatePolynomial.reindex Sum.inl
  · exact IsCoordinatePolynomial.reindex Sum.inr

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialMatrixGroup
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial topology on invertible matrices

Both a matrix and its inverse are retained as affine coordinates. Inversion
then exchanges coordinates, and translations are polynomial coordinate maps.
The resulting topology is Noetherian and T1. Only separate continuity of
multiplication is asserted; the product topology need not be the affine
polynomial topology on a product.
-/

noncomputable section
namespace PolycyclicRecognition

namespace PolynomialMatrixGroup

variable {K : Type*} [Field K] {n : ℕ}

def coordinates (g : PolynomialMatrixGroup K n) : AffinePolynomialPoint (Coord n) K :=
  ⟨fun s => if s.1 then entries g⁻¹ s.2.1 s.2.2 else entries g s.2.1 s.2.2⟩

instance instTopologicalSpace : TopologicalSpace (PolynomialMatrixGroup K n) :=
  TopologicalSpace.induced coordinates inferInstance

end PolynomialMatrixGroup
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PolynomialOneParameterNilpotent
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial matrix one-parameter groups have nilpotent derivative

Successive derivatives are left multiplication by successive powers of the
initial derivative. A polynomial degree bound therefore forces one power to
vanish. This argument uses neither eigenvalues nor triangularization.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Matrix.Norms.Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem polynomial_oneParameter_derivatives
    {f : ℝ → Matrix I I ℝ} {A : Matrix I I ℝ}
    (hadd : ∀ s t, f (s + t) = f s * f t) (hzero : HasDerivAt f A 0)
    (p : I → I → Polynomial ℝ) (hp : ∀ i j t, (p i j).eval t = f t i j)
    (k : ℕ) (i j : I) (t : ℝ) :
    ((Polynomial.derivative^[k]) (p i j)).eval t = (A ^ k * f t) i j := by
  induction k generalizing t with
  | zero => simpa using hp i j t
  | succ k hk =>
    have h₁ := (((Polynomial.derivative^[k]) (p i j)).hasDerivAt t)
    have heq : (fun s => ((Polynomial.derivative^[k]) (p i j)).eval s) =
        (fun s => (A ^ k * f s) i j) := funext hk
    rw [heq] at h₁
    have h₂ := (matrixEntryLinear i j).hasFDerivAt.comp_hasDerivAt t
      ((oneParameter_hasDerivAt hadd hzero t).const_mul (A ^ k))
    change HasDerivAt (fun s => (A ^ k * f s) i j) ((A ^ k * (A * f t)) i j) t at h₂
    have h := h₁.unique h₂
    simpa only [Function.iterate_succ_apply', matrixEntryLinear_apply,
      pow_succ, mul_assoc] using h

theorem isNilpotent_of_polynomial_oneParameter
    {f : ℝ → Matrix I I ℝ} {A : Matrix I I ℝ}
    (hf0 : f 0 = 1) (hadd : ∀ s t, f (s + t) = f s * f t)
    (hzero : HasDerivAt f A 0)
    (hpoly : ∀ i j, ∃ p : Polynomial ℝ, ∀ t, p.eval t = f t i j) :
    IsNilpotent A := by
  choose p hp using hpoly
  let d := (Finset.univ : Finset (I × I)).sup (fun ij => (p ij.1 ij.2).natDegree)
  refine ⟨d + 1, ?_⟩
  ext i j
  have hi : (p i j).natDegree < d + 1 := by
    have hle : (p i j).natDegree ≤ d := Finset.le_sup (f := fun ij : I × I =>
      (p ij.1 ij.2).natDegree) (Finset.mem_univ (i, j))
    exact Nat.lt_succ_of_le hle
  have h := polynomial_oneParameter_derivatives hadd hzero p hp (d + 1) i j 0
  rw [Polynomial.iterate_derivative_eq_zero hi, Polynomial.eval_zero, hf0, mul_one] at h
  exact h.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NormalizedStableSyzygyMap
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.completedCohomologyMap_of _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.normalizedCohomologyStageMap_id _root_.OAI.PolycyclicRecognition.normalizedResolutionComplex_d _root_.OAI.PolycyclicRecognition.resolutionStableSyzygyTransition_class
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Additivity of normalized syzygy maps modulo projective factors

The normalized free cover is not additive. Its induced syzygy map is additive
in the stable quotient; changing a lift produces a map through a free module.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2300] Submodule.Quotient.module
variable {G : Type} [Group G] {A B : Rep.{0} ℤ G}

theorem normalizedSyzygy_stable_of_lift (f : A ⟶ B)
    (l : normalizedFreeRepresentation A ⟶ normalizedFreeRepresentation B)
    (hl : l ≫ normalizedFreeAugmentation B = normalizedFreeAugmentation A ≫ f)
    (s : normalizedSyzygy A ⟶ normalizedSyzygy B)
    (hs : s ≫ kernel.ι (normalizedFreeAugmentation B) =
      kernel.ι (normalizedFreeAugmentation A) ≫ l) :
    stableRepresentationClass _ _ (normalizedSyzygyMap f) = stableRepresentationClass _ _ s := by
  let d := normalizedFreeMap f - l
  have hd : d ≫ normalizedFreeAugmentation B = 0 := by
    dsimp only [d]
    rw [Preadditive.sub_comp, normalizedFreeAugmentation_natural, hl, sub_self]
  let v := kernel.lift (normalizedFreeAugmentation B) d hd
  apply (stableRepresentationClass_eq_iff_projective_factor _ _).mpr
  refine ⟨normalizedFreeRepresentation A, inferInstance,
    kernel.ι (normalizedFreeAugmentation A), v, ?_⟩
  apply (cancel_mono (kernel.ι (normalizedFreeAugmentation B))).mp
  rw [Category.assoc, kernel.lift_ι, Preadditive.sub_comp, normalizedSyzygyMap_ι, hs]
  exact Preadditive.comp_sub _ _ _

def normalizedSyzygyStableLinearMap (A B : Rep.{0} ℤ G) :
    (A ⟶ B) →ₗ[ℤ] StableRepresentationHom (normalizedSyzygy A) (normalizedSyzygy B) := by
  let a : (A ⟶ B) →+ StableRepresentationHom (normalizedSyzygy A) (normalizedSyzygy B) :=
    AddMonoidHom.mk' (fun f => stableRepresentationClass _ _ (normalizedSyzygyMap f)) (by
      intro f g
      have h := normalizedSyzygy_stable_of_lift (f + g)
        (normalizedFreeMap f + normalizedFreeMap g)
        (by simp only [Preadditive.add_comp, Preadditive.comp_add, normalizedFreeAugmentation_natural])
        (normalizedSyzygyMap f + normalizedSyzygyMap g)
        (by simp only [Preadditive.add_comp, Preadditive.comp_add, normalizedSyzygyMap_ι])
      exact h.trans (map_add _ _ _))
  exact { a with map_smul' := fun r f => map_intCast_smul a ℤ ℤ r f }

theorem normalizedSyzygyStableLinearMap_eq_zero (f : A ⟶ B)
    (hf : stableRepresentationClass A B f = 0) : normalizedSyzygyStableLinearMap A B f = 0 := by
  obtain ⟨P, hP, u, v, huv⟩ := (stableRepresentationClass_eq_zero_iff_projective_factor f).mp hf
  let := hP
  let a := Projective.factorThru v (normalizedFreeAugmentation B)
  have ha : a ≫ normalizedFreeAugmentation B = v := Projective.factorThru_comp _ _
  have h := normalizedSyzygy_stable_of_lift f (normalizedFreeAugmentation A ≫ u ≫ a)
    (by rw [Category.assoc, Category.assoc, ha, huv]) 0 (by
      rw [zero_comp, ← Category.assoc, ← Category.assoc, kernel.condition,
        zero_comp, zero_comp])
  exact h.trans ((stableRepresentationClass _ _).map_zero)

def normalizedStableSyzygyMap (A B : Rep.{0} ℤ G) :
    StableRepresentationHom A B →ₗ[ℤ]
      StableRepresentationHom (normalizedSyzygy A) (normalizedSyzygy B) :=
  (projectiveFactorSubmodule A B).liftQ (normalizedSyzygyStableLinearMap A B) (by
    intro f hf
    apply normalizedSyzygyStableLinearMap_eq_zero f
    exact (Submodule.Quotient.mk_eq_zero _).mpr hf)

@[simp]
theorem normalizedStableSyzygyMap_class (f : A ⟶ B) :
    normalizedStableSyzygyMap A B (stableRepresentationClass A B f) =
      stableRepresentationClass _ _ (normalizedSyzygyMap f) := rfl

def normalizedStableSyzygyIterate (A B : Rep.{0} ℤ G) :
    (n : ℕ) → StableRepresentationHom A B →ₗ[ℤ]
      StableRepresentationHom ((iteratedNormalizedSyzygy n).obj A)
        ((iteratedNormalizedSyzygy n).obj B)
  | 0 => LinearMap.id
  | n + 1 => (normalizedStableSyzygyMap ((iteratedNormalizedSyzygy n).obj A)
      ((iteratedNormalizedSyzygy n).obj B)).comp (normalizedStableSyzygyIterate A B n)

@[simp]
theorem normalizedStableSyzygyIterate_class (n : ℕ) (f : A ⟶ B) :
    normalizedStableSyzygyIterate A B n (stableRepresentationClass A B f) =
      stableRepresentationClass _ _ ((iteratedNormalizedSyzygy n).map f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change normalizedStableSyzygyMap _ _
      (normalizedStableSyzygyIterate A B n (stableRepresentationClass A B f)) = _
    rw [ih, normalizedStableSyzygyMap_class]
    rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_PresentationKernelMap
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The stable kernel map of a short exact sequence

A lift of the normalized free cover of the quotient gives a map from its
syzygy to the submodule. Changing the lift changes this map by a projective
factor, and the construction is natural in the stable quotient.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

def presentationKernelMapOfLift (S : ShortComplex (Rep.{0} ℤ G))
    (hS : S.ShortExact) (l : normalizedFreeRepresentation S.X₃ ⟶ S.X₂)
    (hl : l ≫ S.g = normalizedFreeAugmentation S.X₃) :
    normalizedSyzygy S.X₃ ⟶ S.X₁ := by
  let : Mono S.f := hS.mono_f
  exact hS.exact.lift (kernel.ι (normalizedFreeAugmentation S.X₃) ≫ l)
    (by rw [Category.assoc, hl, kernel.condition])

@[reassoc]
theorem presentationKernelMapOfLift_f (S : ShortComplex (Rep.{0} ℤ G))
    (hS : S.ShortExact) (l : normalizedFreeRepresentation S.X₃ ⟶ S.X₂)
    (hl : l ≫ S.g = normalizedFreeAugmentation S.X₃) :
    presentationKernelMapOfLift S hS l hl ≫ S.f =
      kernel.ι (normalizedFreeAugmentation S.X₃) ≫ l := by
  let : Mono S.f := hS.mono_f
  exact hS.exact.lift_f _ _

def presentationFreeLift (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    normalizedFreeRepresentation S.X₃ ⟶ S.X₂ := by
  let : Epi S.g := hS.epi_g
  exact Projective.factorThru (normalizedFreeAugmentation S.X₃) S.g

@[reassoc]
theorem presentationFreeLift_g (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    presentationFreeLift S hS ≫ S.g = normalizedFreeAugmentation S.X₃ := by
  let : Epi S.g := hS.epi_g
  exact Projective.factorThru_comp _ _

def presentationKernelMap (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    normalizedSyzygy S.X₃ ⟶ S.X₁ :=
  presentationKernelMapOfLift S hS (presentationFreeLift S hS) (presentationFreeLift_g S hS)

@[reassoc]
theorem presentationKernelMap_f (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) :
    presentationKernelMap S hS ≫ S.f =
      kernel.ι (normalizedFreeAugmentation S.X₃) ≫ presentationFreeLift S hS :=
  presentationKernelMapOfLift_f S hS _ _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RealTorusContinuity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuity of the real compact rotation action -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra LieModule Module
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

theorem realTorusOperator_fixes_cartan (z : realRotationTorus L H) (h : H) :
    realTorusOperator L H z h = h := by
  apply complexificationLieHom_injective L
  change (1 : ℂ) ⊗ₜ[ℝ] _ = (1 : ℂ) ⊗ₜ[ℝ] _
  rw [realTorusOperator_complexify]
  exact z.val.property.2 (realCartanInComplex L H h)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RegularDualPairing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.regularDualFreeEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Evaluation pairing with the regular dual

Inverse coefficient action makes evaluation equivariant in the regular-dual
argument and invariant under the diagonal action on the other two arguments.
It therefore descends to coinvariant tensor products.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2200] TensorProduct.instModule
variable {G : Type} [Group G]

theorem regularTensorEvaluation_invariant (P A : Rep ℤ G) (g : G) :
    regularTensorEvaluation P A ∘ₗ (A.ρ.tprod P.ρ) g = regularTensorEvaluation P A := by
  apply LinearMap.ext
  intro x
  induction x using OAI.tensorInductionOn with
  | tmul a p =>
    change regularDualEvaluation P A (A.ρ g a) (P.ρ g p) = regularDualEvaluation P A a p
    exact regularDualEvaluation_diagonal P A g a p
  | add x y hx hy => simp only [map_add, hx, hy]

def regularCoinvariantEvaluation (P A : Rep ℤ G) :
    ((Rep.coinvariantsTensor ℤ G).obj A).obj P →ₗ[ℤ] (regularDual P ⟶ A) :=
  Representation.Coinvariants.lift _ (regularTensorEvaluation P A)
    (regularTensorEvaluation_invariant P A)

@[simp] theorem regularCoinvariantEvaluation_tmul (P A : Rep ℤ G) (a : A) (p : P) :
    regularCoinvariantEvaluation P A (Rep.coinvariantsTensorMk A P a p) =
      regularDualEvaluation P A a p := rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RegularFreeEvaluation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Evaluation for finite free group-ring modules -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped MonoidAlgebra TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2200] TensorProduct.instModule
attribute [local instance 2300] Representation.Coinvariants.instModule Pi.Function.module
variable {G : Type} [Group G]

def regularFreeEvaluationAddEquiv (ι : Type) [Finite ι] [DecidableEq ι] (A : Rep ℤ G) :
    ((Rep.coinvariantsTensor ℤ G).obj A).obj (Rep.free ℤ G ι) ≃+
      (regularDual (Rep.free ℤ G ι) ⟶ A) := by
  classical
  let : Module ℤ (ι →₀ A) := Finsupp.module _ _
  exact (Rep.coinvariantsTensorFreeLEquiv A ι).toAddEquiv.trans
    ((Finsupp.linearEquivFunOnFinite ℤ A ι).toAddEquiv.trans
      ((Rep.freeLiftLEquiv ℤ G ι A).symm.toAddEquiv.trans
        (Linear.homCongr ℤ (regularDualFreeIso ι).symm (Iso.refl A)).toAddEquiv))

def regularFreeEvaluationEquiv (ι : Type) [Finite ι] [DecidableEq ι] (A : Rep ℤ G) :
    ((Rep.coinvariantsTensor ℤ G).obj A).obj (Rep.free ℤ G ι) ≃ₗ[ℤ]
      (regularDual (Rep.free ℤ G ι) ⟶ A) where
  __ := regularFreeEvaluationAddEquiv ι A
  map_smul' r x := map_intCast_smul (regularFreeEvaluationAddEquiv ι A) ℤ ℤ r x

theorem regularFreeEvaluationEquiv_precompose (ι : Type) [Finite ι] [DecidableEq ι]
    (A : Rep ℤ G)
    (x : ((Rep.coinvariantsTensor ℤ G).obj A).obj (Rep.free ℤ G ι)) :
    (regularDualFreeIso ι).inv ≫ regularFreeEvaluationEquiv ι A x =
      Rep.freeLift ℤ G A (fun j => (Rep.coinvariantsTensorFreeLEquiv A ι x) j) := by
  change (regularDualFreeIso ι).inv ≫
    Linear.homCongr ℤ (regularDualFreeIso ι).symm (Iso.refl A)
      ((Rep.freeLiftLEquiv ℤ G ι A).symm
        ((Finsupp.linearEquivFunOnFinite ℤ A ι)
          (Rep.coinvariantsTensorFreeLEquiv A ι x))) = _
  simp only [Linear.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id,
    Iso.inv_hom_id_assoc, freeLiftLEquiv_symm_apply]
  congr 1

theorem regularFreeEvaluationEquiv_eq (ι : Type) [Finite ι] [DecidableEq ι] (A : Rep ℤ G) :
    (regularFreeEvaluationEquiv ι A).toLinearMap =
      regularCoinvariantEvaluation (Rep.free ℤ G ι) A := by
  classical
  apply Representation.Coinvariants.hom_ext
  apply TensorProduct.ext
  apply DFunLike.ext
  intro a
  apply Finsupp.lhom_ext'
  intro i
  apply MonoidAlgebra.lhom_ext'
  intro g
  apply DFunLike.ext
  intro r
  apply (cancel_epi (regularDualFreeIso ι).inv).mp
  change (regularDualFreeIso ι).inv ≫ regularFreeEvaluationEquiv ι A
      (Rep.coinvariantsTensorMk A (Rep.free ℤ G ι) a
        (Finsupp.single i (MonoidAlgebra.single g r))) =
    (regularDualFreeIso ι).inv ≫ regularCoinvariantEvaluation (Rep.free ℤ G ι) A
      (Rep.coinvariantsTensorMk A (Rep.free ℤ G ι) a
        (Finsupp.single i (MonoidAlgebra.single g r)))
  rw [regularFreeEvaluationEquiv_precompose]
  apply Rep.free_ext
  intro j
  change Representation.freeLift A.ρ
      (fun k => (Rep.coinvariantsTensorFreeLEquiv A ι
        (Rep.coinvariantsTensorMk A (Rep.free ℤ G ι) a
          (Finsupp.single i (MonoidAlgebra.single g r)))) k)
        (Finsupp.single j (MonoidAlgebra.single 1 1)) = _
  rw [Representation.freeLift_single_single]
  simp only [map_one, Module.End.one_apply]
  rw [@one_smul ℤ A _ A.hV2.toMulAction]
  change (Rep.coinvariantsTensorFreeLEquiv A ι
        (Rep.coinvariantsTensorMk A (Rep.free ℤ G ι) a
          (Finsupp.single i (MonoidAlgebra.single g r)))) j =
    regularCoefficientAction A
      (((regularDualFreeIso ι).inv.hom
        (Finsupp.single j (MonoidAlgebra.single 1 1))).hom
          (Finsupp.single i (MonoidAlgebra.single g r))) a
  rw [regularDualFreeIso_inv_single]
  change (Rep.coinvariantsTensorFreeToFinsupp A ι
      (Representation.Coinvariants.mk _
        (a ⊗ₜ[ℤ] Finsupp.single i (MonoidAlgebra.single g r)))) j = _
  have ht := congrArg (fun z : ι →₀ A => z j)
    (Rep.coinvariantsTensorFreeToFinsupp_mk_tmul_single A a i g r)
  calc
    _ = (Finsupp.single i (A.hV2.smul r (A.ρ g⁻¹ a))) j := ht
    _ = _ := by
      by_cases h : i = j
      · subst j
        simp only [Finsupp.single_eq_same, regularInversion_single, inv_one,
          Representation.ofMulAction_single, smul_eq_mul, mul_one, map_smul,
          regularCoefficientAction_single, int_smul_eq_zsmul, one_smul]
        exact (map_zsmul (LinearMap.applyₗ (R := ℤ) (M := A) a) r (A.ρ g⁻¹)).symm
      · simp only [Finsupp.single_eq_of_ne h, Finsupp.single_eq_of_ne (Ne.symm h),
          map_zero, smul_zero, LinearMap.zero_apply]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RegularPairingNaturality
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.regularDualFreeEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Naturality of the regular-dual evaluation pairing -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
attribute [local instance 2200] TensorProduct.instModule
variable {G : Type} [Group G]

@[simp] theorem regularDualMap_id (P : Rep ℤ G) :
    regularDualMap (𝟙 P) = 𝟙 (regularDual P) := by
  apply Rep.hom_ext
  apply DFunLike.ext
  intro f
  exact Category.id_comp f

theorem regularDualMap_comp {P Q R : Rep ℤ G} (f : P ⟶ Q) (g : Q ⟶ R) :
    regularDualMap (f ≫ g) = regularDualMap g ≫ regularDualMap f := by
  apply Rep.hom_ext
  apply DFunLike.ext
  intro h
  exact Category.assoc f g h

theorem regularCoinvariantEvaluation_naturality {P Q : Rep ℤ G} (f : P ⟶ Q)
    (A : Rep ℤ G) (x : ((Rep.coinvariantsTensor ℤ G).obj A).obj P) :
    regularCoinvariantEvaluation Q A (((Rep.coinvariantsTensor ℤ G).obj A).map f x) =
      regularDualMap f ≫ regularCoinvariantEvaluation P A x := by
  refine Representation.Coinvariants.induction_on x ?_
  intro t
  induction t using OAI.tensorInductionOn with
  | tmul a p =>
    apply Rep.hom_ext
    apply DFunLike.ext
    intro q
    rfl
  | add t u ht hu =>
    simp only [map_add, Preadditive.comp_add, ht, hu]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_RescaledSubmersiveScheme
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed submersive scheme for an actual sequence of rescalings

The subsequence and the word are selected from the actual coordinate laws,
before any good sheets or successful parameter sets are selected.
-/

noncomputable section

namespace PolycyclicRecognition

open Module Filter Set
open scoped Topology

/-- A convergent subsequence and a fixed word with full-rank limiting
endpoint map. This packages only the explicit finite-dimensional data. -/
def HasSubmersiveWordSubsequence {I : Type*} {n c : ℕ}
    (a : DynkinCoefficients c 2)
    (S : Set (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) ×
      (I → Fin n → ℝ)))
    (p : ℕ → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) ×
      (I → Fin n → ℝ)) : Prop :=
  ∃ q ∈ S, ∃ u : ℕ → ℕ, StrictMono u ∧ Tendsto (p ∘ u) atTop (𝓝 q) ∧
    ∃ (m : ℕ) (letters : Fin m → I) (t : Fin (m + m) → ℝ),
      differenceAmplitudeWordEndpoint a letters q t = 0 ∧
      Function.Surjective (fderiv ℝ (differenceAmplitudeWordEndpoint a letters q) t)

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_TwoImageLimits
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous limits of two box embeddings

The bounded embeddings and their bounded generator preimages are retained
alongside the normalized Lie law. Thus every limiting generator belongs to
one of the limiting images, and the full alternating product is submersive.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric Module Filter
open scoped Topology

def HasSubmersiveTwoImageSubsequence {I : Type*} [Fintype I] {n c : ℕ}
    (a : DynkinCoefficients c 2) (w : Fin n → FreeMagma I) (C : ℝ)
    (q : ℕ → TwoImageData I n) : Prop :=
  ∃ q₀ : TwoImageData I n,
    q₀.1.1 ∈ normalizedExponentialParameters a w (fun i => Pi.single i 1) C ∧
    q₀.generatorsCovered ∧
    ∃ u : ℕ → ℕ, StrictMono u ∧ Tendsto (q ∘ u) atTop (𝓝 q₀) ∧
    ∃ (h : ℕ) (z₀ : Fin h → (Fin n → ℝ) × (Fin n → ℝ)),
      alternatingCoordinateProduct a q₀.1.1.1 q₀.1.2.1 q₀.1.2.2 z₀ = 0 ∧
      Function.Surjective
        (fderiv ℝ (alternatingCoordinateProduct a q₀.1.1.1 q₀.1.2.1 q₀.1.2.2) z₀)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_UniversalBCHCoefficientBound
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The uniform bound on the universal finite BCH coefficients -/

noncomputable section
namespace PolycyclicRecognition

theorem universalLogarithmCoefficient_bound (c n : ℕ) (d : Fin c)
    (w : FreeMonoid (Fin n)) :
    |(universalLogarithmCoefficient c n (d.val + 1)).coeff w| ≤ (2 : ℚ) ^ c := by
  rw [universalLogarithmCoefficient_coeff (Nat.succ_le_of_lt d.isLt)]
  by_cases hw : w.length = d.val + 1
  · rw [ite_eq_left hw, rationalUniversalLogarithm]
    exact finiteLog_coefficient_bound _ c (rationalExponentialProduct_sub_one_empty c n)
      (rationalExponentialProduct_sub_one_bound c n) w (by omega) (by omega)
  · rw [ite_eq_right hw, abs_zero]
    positivity

theorem universalBCHCoefficient_bound (c n : ℕ) (d : Fin c)
    (w : Fin (d.val + 1) → Fin n) :
    |(d.val + 1 : ℚ)⁻¹ *
      (universalLogarithmCoefficient c n (d.val + 1)).coeff (wordOfFn w)| ≤ (2 : ℚ) ^ c := by
  rw [abs_mul, abs_inv, abs_of_nonneg (by positivity : (0 : ℚ) ≤ d.val + 1)]
  exact (mul_le_mul (inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg _)))
    (universalLogarithmCoefficient_bound c n d (wordOfFn w))
    (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_BoundedAssociativeBCH
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real coefficients and the bounded associative BCH identity -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing

def universalDynkinCoefficients (c n : ℕ) : DynkinCoefficients c n :=
  fun d w => (((d.val + 1 : ℚ)⁻¹ *
    (universalLogarithmCoefficient c n (d.val + 1)).coeff (wordOfFn w) : ℚ) : ℝ)

theorem universalDynkinCoefficients_bound (c n : ℕ) (d : Fin c)
    (w : Fin (d.val + 1) → Fin n) :
    |universalDynkinCoefficients c n d w| ≤ (2 : ℝ) ^ c := by
  unfold universalDynkinCoefficients
  exact_mod_cast universalBCHCoefficient_bound c n d w

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UniversalCoefficientStability
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independence of the low-degree universal BCH coefficients

Increasing the finite exponential and logarithm truncations changes only
higher word degrees. Thus the universal coefficients can be restricted to
the actual nilpotency class.
-/

noncomputable section
namespace PolycyclicRecognition

theorem universalLogarithmCoefficient_stable {c d n e : ℕ} (h : c ≤ d) (he : e ≤ c) :
    universalLogarithmCoefficient c n e = universalLogarithmCoefficient d n e := by
  ext w
  rw [universalLogarithmCoefficient_coeff he,
    universalLogarithmCoefficient_coeff (he.trans h)]
  by_cases hw : w.length = e
  · rw [ite_eq_left hw, ite_eq_left hw]
    exact rationalUniversalLogarithm_stable h w (by omega)
  · rw [ite_eq_right hw, ite_eq_right hw]

theorem universalDynkinCoefficients_stable {c d n : ℕ} (h : c ≤ d)
    (e : Fin c) (w : Fin (e.val + 1) → Fin n) :
    universalDynkinCoefficients c n e w =
      universalDynkinCoefficients d n (e.castLE h) w := by
  unfold universalDynkinCoefficients
  simp only [Fin.val_castLE]
  rw [universalLogarithmCoefficient_stable h (Nat.succ_le_of_lt e.isLt)]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_UniversalDynkinTruncation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting the universal BCH polynomial to the nilpotency class -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

theorem rightNestedWord_depth {I : Type*} (d : ℕ) (w : Fin (d + 1) → I) :
    bracketWordDepth (rightNestedWord d w) = d := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [rightNestedWord, bracketWordDepth, ih, Nat.zero_max]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_AmenableCorrection
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Correcting bounded height defects with an invariant mean

This is the averaging step in Proposition `recognition-from-height` of the
manuscript *Quasi-isometric recognition of virtually polycyclic groups*.
The mean is on the actual space of all bounded real functions. Neither the
height function itself nor its corrected homomorphism has to be bounded.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability
open scoped ENNReal

universe u v

variable {G : Type u} [Group G]

/-- The increment of a function of uniformly bounded additive defect is bounded. -/
def boundedIncrement (s : G → ℝ) (D : ℝ)
    (hD : ∀ h k, |s (h * k) - s h - s k| ≤ D) (h : G) : BoundedReal G :=
  ⟨fun x => s (h * x) - s x, memℓp_infty ⟨D + |s h|, by
    rintro y ⟨x, rfl⟩
    change |s (h * x) - s x| ≤ D + |s h|
    calc
      |s (h * x) - s x| = |(s (h * x) - s h - s x) + s h| := by ring_nf
      _ ≤ |s (h * x) - s h - s x| + |s h| := abs_add_le _ _
      _ ≤ D + |s h| := add_le_add (hD h x) le_rfl⟩⟩

@[simp]
theorem boundedIncrement_apply (s : G → ℝ) (D : ℝ)
    (hD : ∀ h k, |s (h * k) - s h - s k| ≤ D) (h x : G) :
    boundedIncrement s D hD h x = s (h * x) - s x := rfl

/-- The cocycle identity holds for increments before applying the mean. -/
theorem boundedIncrement_mul (s : G → ℝ) (D : ℝ)
    (hD : ∀ h k, |s (h * k) - s h - s k| ≤ D) (h k : G) :
    boundedIncrement s D hD (h * k) =
      leftPull k (boundedIncrement s D hD h) + boundedIncrement s D hD k := by
  apply lp.ext
  funext x
  change s ((h * k) * x) - s x = (s (h * (k * x)) - s (k * x)) +
    (s (k * x) - s x)
  rw [mul_assoc]
  ring

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_BoundedPathGrowth
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From bounded-height word paths to polynomial growth

Word chains and a uniform metric multiplicity bound turn polynomial packing
of bounded-height chains into polynomial growth. Gromov's theorem then gives
virtual nilpotence of the subgroup.
-/

namespace PolycyclicRecognition

variable {X W : Type*} [PseudoMetricSpace X] [NormedAddCommGroup W]

/-- Polynomial packing of bounded-height chains in the Lie model. -/
def PolynomialBoundedChainPacking [DecidableEq X] (π : X → W) : Prop :=
  ∀ (x : X) (L M : ℝ), 0 ≤ L → 0 ≤ M →
    ∃ (C b : ℕ) (centers : ℕ → Finset X),
      (∀ n, (centers n).card ≤ C * (1 + n) ^ b) ∧
      ∀ n m, m ≤ n → ∀ y, BoundedHeightChain π L M m x y →
        ∃ c ∈ centers n, dist y c ≤ 1

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_SemidirectProductTopology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The product topology on the Cartan semidirect cover -/

noncomputable section
namespace PolycyclicRecognition

variable {N D : Type*} [Group N] [Group D] [TopologicalSpace N] [TopologicalSpace D]
  (φ : D →* MulAut N)

attribute [local instance] semidirectProductTopology

instance instT2SpaceSemidirectProduct_solutions [T2Space N] [T2Space D] : T2Space (N ⋊[φ] D) :=
  (semidirectProductHomeomorph φ).isEmbedding.t2Space

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MeanSubgroup
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.smallCoefficientBoundedReal_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Restricting invariant means to subgroups

The finite-index height kernel in the recognition argument inherits amenability
from the ambient group. The construction below works for an arbitrary subgroup:
choose representatives for right cosets, construct an equivariant map to the subgroup,
and extend each bounded function by composition with this map.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability
open scoped ENNReal

universe u

variable {G : Type u} [Group G]

/-- Extend a bounded subgroup function to the whole group by the equivariant coordinate. -/
def subgroupFunctionExtension (K : Subgroup G) : BoundedReal K →ₗ[ℝ] BoundedReal G where
  toFun f := ⟨fun g => f (subgroupCoordinate K g), memℓp_infty ⟨‖f‖, by
    rintro y ⟨g, rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero f (subgroupCoordinate K g)⟩⟩
  map_add' f g := by
    apply lp.ext
    funext x
    rfl
  map_smul' r f := by
    apply lp.ext
    funext x
    rfl

@[simp]
theorem subgroupFunctionExtension_apply (K : Subgroup G) (f : BoundedReal K) (g : G) :
    subgroupFunctionExtension K f g = f (subgroupCoordinate K g) := rfl

@[simp]
theorem subgroupFunctionExtension_one (K : Subgroup G) :
    subgroupFunctionExtension K 1 = 1 := by
  apply lp.ext
  funext g
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangulableLieModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published reduction to a real-triangulable Lie model

Y. Cornulier and R. Tessera, *Geometric presentations of Lie groups and
their Dehn functions*, Publications Mathématiques de l'IHÉS 125 (2017),
79–219, Lemma 3.A.1, p.108, gives proper continuous homomorphisms with
cocompact images `G ← G₁ → G₂ ← G₃`, with `G₃` real triangulable.
Definition 1.1, p.83, identifies this last property with being isomorphic
to a closed connected group of invertible upper triangular real matrices.

The input below keeps precisely that topological reduction. Its metric
consequence is proved using the separately identified compatible-metric
existence input and the explicit inverse-map composition lemmas. No
adjoint basis, height control, or recognition conclusion is placed in the
published input.
-/

noncomputable section

namespace PolycyclicRecognition

/-- The solvable-source specialization of CT Lemma 3.A.1. The intermediate
Lie groups are retained only through the locally compact data needed to
compare their metrics. -/
def CornulierTesseraModelInput : Prop :=
  ∀ S : SimplyConnectedSolvableLieModel,
    ∃ T : SimplyConnectedSolvableLieModel, IsRealTriangulable T ∧
      ∃ G₁ G₂ : CompactlyGeneratedLCModel,
        Nonempty (ProperCocompactHom G₁.carrier S.carrier) ∧
        Nonempty (ProperCocompactHom G₁.carrier G₂.carrier) ∧
        Nonempty (ProperCocompactHom T.carrier G₂.carrier)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactExtensionModels
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The locally compact models in the compact-extension comparison -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
attribute [local instance] semidirectProductTopology

def SimplyConnectedSolvableLieModel.toLCModel (S : SimplyConnectedSolvableLieModel) :
    CompactlyGeneratedLCModel := by
  let tg : IsTopologicalGroup S.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ,S.modelSpace)) ⊤
  let lc : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ,S.modelSpace))
  exact { carrier := S.carrier, compactlyGenerated := exists_compact_generating_set S.carrier }

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_CompactProbeLift
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retained compact probes in the ambient product Haar coordinates -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set

/-- The original normalized cell law, viewed on its carrying subtype. -/
def cellSubtypeProbability {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (C : Set X) (hC : MeasurableSet C)
    (hzero : μ C ≠ 0) (hfinite : μ C ≠ ⊤) : ProbabilityMeasure C :=
  supportedProbabilityRestriction (cellProbabilityMeasure μ C hzero hfinite)
    C hC (ae_mem_cellProbabilityMeasure μ C hC hzero hfinite)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_ExtensionInvariantMean
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.smallCoefficientBoundedReal_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Invariant means on extensions

Average first on each kernel coset and then on the quotient. All averages
act on the actual bounded real functions used in the height correction.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability
open scoped ENNReal

def boundedFunctionPull {X Y : Type*} (u : X → Y) : BoundedReal Y →ₗ[ℝ] BoundedReal X where
  toFun f := ⟨fun x => f (u x), memℓp_infty ⟨‖f‖, by
    rintro y ⟨x, rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero f (u x)⟩⟩
  map_add' _ _ := by apply lp.ext; funext x; rfl
  map_smul' _ _ := by apply lp.ext; funext x; rfl

@[simp]
theorem boundedFunctionPull_apply {X Y : Type*} (u : X → Y) (f : BoundedReal Y) (x : X) :
    boundedFunctionPull u f x = f (u x) := rfl

@[simp]
theorem boundedFunctionPull_one {X Y : Type*} (u : X → Y) :
    boundedFunctionPull u 1 = 1 := by apply lp.ext; funext x; rfl

theorem boundedFunctionPull_norm_le {X Y : Type*} (u : X → Y) (f : BoundedReal Y) :
    ‖boundedFunctionPull u f‖ ≤ ‖f‖ :=
  lp.norm_le_of_forall_le (norm_nonneg f)
    (fun x => lp.norm_apply_le_norm ENNReal.top_ne_zero f (u x))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_FiniteWordMetric
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete word metrics used in the metric-free main statement -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric

namespace WordMetric

variable {G I : Type*} [Group G] (P : Group.Generators G I)

theorem dist_eq (x y : G) :
    letI := P.normedGroup
    dist x y = (P.wordLength (x⁻¹ * y) : ℝ) := rfl

theorem leftInvariant : letI := P.normedGroup; IsIsometricSMul G G := by
  let := P.normedGroup
  refine ⟨fun g => Isometry.of_dist_eq (fun x y => ?_)⟩
  simp only [smul_eq_mul, dist_eq, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

/-- Prefixes of a shortest representing word form a unit-step chain whose
length is the word distance. -/
def chains : letI := P.normedGroup; LinearMetricChains G := by
  let := P.normedGroup
  let := leftInvariant P
  refine {
    step := 1
    step_pos := by norm_num
    slope := 1
    slope_nonneg := by norm_num
    error := 0
    error_nonneg := by norm_num
    chain := ?_ }
  intro x y
  obtain ⟨l, hl, he⟩ := P.exists_isGeodesic (x⁻¹ * y)
  refine ⟨l.length, fun n => x * P.wordProd (l.take n), by simp, by simp [he], ?_, ?_⟩
  · rw [one_mul, add_zero, dist_eq, ← he, hl.eq]
  · intro i hi
    rw [dist_mul_left, dist_eq, ← List.take_concat_get' l i hi, P.wordProd_append,
      inv_mul_cancel_left]
    exact_mod_cast (P.wordLength_wordProd_le [l[i]] )

end WordMetric

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_IntegralFinsuppFunctor
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact direct sums of integral modules -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits

theorem moduleFinsuppFunctor_map_exact (k : Type) [Ring k] (α : Type)
    (S : ShortComplex (ModuleCat k))
    (hS : S.Exact) : (S.map (moduleFinsuppFunctor k α)).Exact := by
  classical
  let preimage (x : S.X₂) : S.X₁ :=
    if x = 0 then 0 else if h : S.g.hom x = 0 then
      ((ShortComplex.moduleCat_exact_iff S).mp hS x h).choose else 0
  have hzero : preimage 0 = 0 := by simp [preimage]
  have hpre (x : S.X₂) (hx : S.g.hom x = 0) : S.f.hom (preimage x) = x := by
    by_cases hz : x = 0
    · simp [preimage, hz]
    · simp only [preimage, ite_eq_right hz, dite_eq_left hx]
      exact ((ShortComplex.moduleCat_exact_iff S).mp hS x hx).choose_spec
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  change ∀ x : α →₀ S.X₂,
    Finsupp.mapRange S.g.hom (map_zero _) x = 0 →
      ∃ y : α →₀ S.X₁, Finsupp.mapRange S.f.hom (map_zero _) y = x
  intro x hx
  refine ⟨Finsupp.mapRange preimage hzero x, ?_⟩
  ext i
  have hi := congrArg (fun y : α →₀ S.X₃ => y i) hx
  change S.g.hom (x i) = 0 at hi
  exact hpre (x i) hi

instance instPreservesHomologyModuleCatModuleFinsuppFunctor (k : Type) [Ring k] (α : Type) : (moduleFinsuppFunctor k α).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (moduleFinsuppFunctor_map_exact k α)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MeasuredProbeRegions
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The measured regions produced by the two-path construction -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped Topology

/-- One section and three containing regions, with their actual measure
bounds. The ideal exponent is fixed while the loss is subexponential. -/
structure MeasuredProbeRegions {N D Q : Type*} [Group N] [Group Q]
    [TopologicalSpace N] [TopologicalSpace Q]
    [MeasurableSpace Q] [MeasurableSpace N] [MeasurableSpace D]
    (π : N →* Q) (μQ : Measure Q) (μI : Measure π.ker) (ν : Measure D)
    (scale : ℕ → ℝ) (P : ℝ) where
  sectionMap : C(Q, N)
  section_rightInverse : ∀ q, π (sectionMap q) = q
  quotientRegion : ℕ → Set Q
  idealRegion : ℕ → Set π.ker
  cartanRegion : ℕ → Set D
  idealLoss : ℕ → ℝ
  quotient_finite : ∀ n, μQ (quotientRegion n) ≠ ⊤
  ideal_finite : ∀ n, μI (idealRegion n) ≠ ⊤
  cartan_finite : ∀ n, ν (cartanRegion n) ≠ ⊤
  quotient_subexponential : HasSubexponentialUpperBoundSeq scale
    (fun n => (μQ (quotientRegion n)).toReal)
  ideal_subexponential : HasSubexponentialUpperBoundSeq scale idealLoss
  idealLoss_nonneg : ∀ n, 0 ≤ idealLoss n
  cartan_subexponential : HasSubexponentialUpperBoundSeq scale
    (fun n => (ν (cartanRegion n)).toReal)
  ideal_volume : ∀ n, (μI (idealRegion n)).toReal = idealLoss n * Real.exp (P * scale n)

variable {N D G Q W : Type*} [Group N] [Group D] [Group G] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q]
  [MeasurableSpace Q] [MeasurableSpace N] [MeasurableSpace D]
  [MetricSpace G] [NormedAddCommGroup W] [NormedSpace ℝ W]
  {π : N →* Q} {μQ : Measure Q} {μI : Measure π.ker} {ν : Measure D}
  {scale : ℕ → ℝ} {P : ℝ}

/-- The path property proved for the measured regions. This records
geometric input paths and the single fixed lift controlling the whole
right cell, without choosing points or tile frames. -/
def MeasuredProbeRegions.ControlsTwoPaths
    (R : MeasuredProbeRegions π μQ μI ν scale P)
    (project : N → D → G) (φ : D →* MulAut N) (act : G → Q → Q)
    (height : G →* Multiplicative W) (cell : Set (N × D))
    (E₁ E₂ : Set W) (η : ℕ → ℝ) (A B δ : ℝ) (n : ℕ) : Prop :=
  ∀ (base anchor first second : G)
    (path₁ : Path (1 : G) (base⁻¹ * first))
    (path₂ : Path (1 : G) (anchor⁻¹ * second)),
    PathMetricBound path₁ (A * scale n) (B * (1 + Real.log (2 + scale n))) →
    PathMetricBound path₂ (A * scale n) (B * (1 + Real.log (2 + scale n))) →
    (∀ t, ∃ w ∈ E₁, ‖(height (path₁ t)).toAdd - scale n • w‖ ≤
      2 * scale n * η n + A * (1 + Real.log (2 + scale n))) →
    (∀ t, ∃ w ∈ E₂, ‖(height (path₂ t)).toAdd - scale n • w‖ ≤
      2 * scale n * η n + A * (1 + Real.log (2 + scale n))) →
    ‖(height (anchor⁻¹ * second)).toAdd‖ ≤ δ * scale n →
    dist second first ≤ δ * scale n →
    ∃ (u : N) (d : D), project u d = anchor⁻¹ * first ∧ ∀ z ∈ cell,
      act (base⁻¹ * (first * project z.1 z.2)) 1 ∈ R.quotientRegion n ∧
      quotientSectionResidual π R.sectionMap R.section_rightInverse (u * φ d z.1) ∈
        R.idealRegion n ∧ d * z.2 ∈ R.cartanRegion n

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_MinimizingMetricChains
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Metric chains supplied by the chosen minimizing paths -/

noncomputable section
namespace PolycyclicRecognition

open Metric Set

/-- Sampling the chosen minimizing paths gives the concrete chain witnesses
needed by the canonical-height and proper-homomorphism metric bridges. -/
def linearMetricChains_of_minimizing_paths
    {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|) :
    LinearMetricChains G := by
  refine {
    step := 1
    step_pos := zero_lt_one
    slope := 1
    slope_nonneg := zero_le_one
    error := 1
    error_nonneg := zero_le_one
    chain := ?_ }
  intro x y
  obtain ⟨γ, h0, h1, hγ⟩ := hpath (x⁻¹ * y)
  let n := ⌊dist 1 (x⁻¹ * y)⌋₊ + 1
  have hn : 0 < n := Nat.succ_pos _
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlen : dist 1 (x⁻¹ * y) ≤ (n : ℝ) := by
    simpa [n] using (Nat.lt_floor_add_one (dist 1 (x⁻¹ * y))).le
  let p : ℕ → G := fun k => x * γ ((k : ℝ) / n)
  refine ⟨n, p, ?_, ?_, ?_, ?_⟩
  · simp [p, h0]
  · simp [p, h1, hnr.ne']
  · simpa only [n, Nat.cast_add, Nat.cast_one, dist_one_groupDifference, one_mul, add_comm]
      using add_le_add_right (Nat.floor_le (dist_nonneg (x := (1 : G))
        (y := x⁻¹ * y))) 1
  · intro k hk
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk.le
    have hks : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hk
    have ht : (k : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hnr).mpr hkn⟩
    have hu : ((k + 1 : ℕ) : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hnr).mpr hks⟩
    have hdiff : |(k : ℝ) / n - ((k + 1 : ℕ) : ℝ) / n| = 1 / n := by
      rw [abs_of_nonpos (sub_nonpos.mpr (div_le_div_of_nonneg_right (by simp) hnr.le))]
      push_cast
      ring
    change dist (x * γ _) (x * γ _) ≤ 1
    rw [dist_mul_left]
    refine (hγ _ ht _ hu).trans ?_
    rw [hdiff, mul_one_div]
    exact (div_le_one hnr).mpr hlen

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_SupportPolytope
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanWordModel.supportDatum_weight _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite covector body of the segment support norm

The positive-part formula is the maximum of finitely many actual linear
forms, obtained by choosing subsets of the weights in a word basis. This
constructs the support body used to define the finite height-label group.
-/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open scoped BigOperators

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : PolycyclicRecognition.SupportDatum W I B)

/-- A linear piece in the positive-part expression for segment support. -/
def supportForm (b : B) (S : Finset I) : W →L[ℝ] ℝ :=
  ∑ i ∈ S, (D.multiplicity b i : ℝ) • (D.weight i).toContinuousLinearMap

omit [Nonempty B] in
theorem supportForm_apply (b : B) (S : Finset I) (w : W) :
    D.supportForm b S w = ∑ i ∈ S, (D.multiplicity b i : ℝ) * D.weight i w := by
  simp [supportForm]

/-- The explicitly finite set of all linear pieces. -/
def supportForms : Finset (W →L[ℝ] ℝ) := by
  classical
  exact Finset.univ.image (fun p : B × Finset I => D.supportForm p.1 p.2)

omit [Nonempty B] in
theorem mem_supportForms (b : B) (S : Finset I) : D.supportForm b S ∈ D.supportForms := by
  classical
  exact Finset.mem_image.mpr ⟨(b, S), Finset.mem_univ _, rfl⟩

theorem supportForm_le (b : B) (S : Finset I) (w : W) :
    D.supportForm b S w ≤ D.segmentSupport w := by
  classical
  apply le_trans _ (D.basisSupport_le b w)
  rw [supportForm_apply]
  calc
    (∑ i ∈ S, (D.multiplicity b i : ℝ) * D.weight i w) ≤
        ∑ i ∈ S, (D.multiplicity b i : ℝ) * max 0 (D.weight i w) := by
      exact Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (le_max_right _ _) (Nat.cast_nonneg _))
    _ ≤ ∑ i, (D.multiplicity b i : ℝ) * max 0 (D.weight i w) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun i _ _ => mul_nonneg (Nat.cast_nonneg _) (le_max_left _ _))

/-- Every support value is attained by a member of the finite covector set. -/
theorem exists_supportForm_eq (w : W) :
    ∃ φ ∈ D.supportForms, φ w = D.segmentSupport w := by
  classical
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun b => D.basisSupport b w)
  let S := Finset.univ.filter (fun i => 0 ≤ D.weight i w)
  refine ⟨D.supportForm b S, D.mem_supportForms b S, ?_⟩
  have h : D.supportForm b S w = D.basisSupport b w := by
    rw [supportForm_apply]
    simp only [S, Finset.sum_filter, basisSupport]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hi
    · rw [max_eq_right hi]
    · rw [max_eq_left (le_of_not_ge hi), mul_zero]
  exact h.trans hb.symm

theorem supportForms_le (w : W) {φ : W →L[ℝ] ℝ} (hφ : φ ∈ D.supportForms) :
    φ w ≤ D.segmentSupport w := by
  classical
  obtain ⟨⟨b, S⟩, _, rfl⟩ := Finset.mem_image.mp hφ
  exact D.supportForm_le b S w

/-- The finite pieces still separate the entire height space. -/
theorem supportForms_separate (w : W)
    (hw : ∀ φ ∈ D.supportForms, φ w = 0) : w = 0 := by
  obtain ⟨φ, hφ, heq⟩ := D.exists_supportForm_eq w
  exact (D.segmentSupport_eq_zero_iff w).mp (heq.symm.trans (hw φ hφ))

/-- The concrete support forms span the continuous dual height space. -/
theorem supportForms_span : Submodule.span ℝ (D.supportForms : Set (W →L[ℝ] ℝ)) = ⊤ := by
  classical
  let e : Module.Dual ℝ W ≃ₗ[ℝ] (W →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
  have hspan : Submodule.span ℝ (e ⁻¹' (D.supportForms : Set (W →L[ℝ] ℝ))) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro w hw
    have hex : ∃ φ ∈ D.supportForms, φ w ≠ 0 := by
      by_contra h
      push Not at h
      exact hw (D.supportForms_separate w h)
    obtain ⟨φ, hφ, hφw⟩ := hex
    refine ⟨e.symm φ, ?_, hφw⟩
    change e (e.symm φ) ∈ D.supportForms
    simpa using hφ
  have hm := congrArg (Submodule.map e.toLinearMap) hspan
  rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at hm
  change Submodule.span ℝ (e '' (e ⁻¹' (D.supportForms : Set (W →L[ℝ] ℝ)))) = ⊤ at hm
  rw [Set.image_preimage_eq _ e.surjective] at hm
  exact hm

/-- The finite convex body is exactly the set of covectors dominated by the
segment support. This is the polarity step used to detect its symmetries. -/
theorem mem_supportBody_iff (φ : W →L[ℝ] ℝ) :
    φ ∈ convexHull ℝ (D.supportForms : Set (W →L[ℝ] ℝ)) ↔
      ∀ w, φ w ≤ D.segmentSupport w := by
  constructor
  · intro hφ w
    have hc : Convex ℝ {ψ : W →L[ℝ] ℝ | ψ w ≤ D.segmentSupport w} := by
      intro f hf g hg a b ha hb hab
      change a * f w + b * g w ≤ D.segmentSupport w
      calc
        a * f w + b * g w ≤ a * D.segmentSupport w + b * D.segmentSupport w :=
          add_le_add (mul_le_mul_of_nonneg_left hf ha) (mul_le_mul_of_nonneg_left hg hb)
        _ = D.segmentSupport w := by rw [← add_mul, hab, one_mul]
    exact (convexHull_min (fun ψ hψ => D.supportForms_le w hψ) hc) hφ
  · intro hφ
    by_contra hn
    obtain ⟨L, r, hbody, hrφ⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ (D.supportForms : Set (W →L[ℝ] ℝ)))
      (D.supportForms.finite_toSet.isClosed_convexHull ℝ) hn
    let e : Module.Dual ℝ W ≃ₗ[ℝ] (W →L[ℝ] ℝ) := LinearMap.toContinuousLinearMap
    let L₀ : Module.Dual ℝ (Module.Dual ℝ W) := L.toLinearMap.comp e.toLinearMap
    let w := (Module.evalEquiv ℝ W).symm L₀
    have heval (ψ : W →L[ℝ] ℝ) : L ψ = ψ w := by
      exact (Module.apply_evalEquiv_symm_apply ℝ W ψ.toLinearMap L₀).symm
    obtain ⟨ψ, hψ, heq⟩ := D.exists_supportForm_eq w
    have hlt := hbody ψ (subset_convexHull ℝ _ hψ)
    rw [heval ψ, heq] at hlt
    rw [heval φ] at hrφ
    exact (not_lt_of_ge (hφ w)) (hlt.trans hrφ)

end PolycyclicRecognition.SupportDatum

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_WordChartScaleTransition
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact coordinate and height identities between two chart scales -/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {L J : Type*} [LieRing L] [LieAlgebra ℝ L] [Finite J]

/-- Coordinates of the same Lie-algebra point in the second scaled basis. -/
def basisScaleTransition (b : Basis J ℝ L) (cost : J → ℝ) (r t : ℝ) :
    (J → ℝ) ≃ₗ[ℝ] (J → ℝ) :=
  (exponentialRescaleBasis b cost r).equivFun.symm.trans
    (exponentialRescaleBasis b cost t).equivFun

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_BilateralCochainShift
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Translation on direct sums of cochain complexes and their cohomology -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory

variable (k : Type) [CommRing k]

variable (C : CochainComplex (ModuleCat k) ℕ)

def bilateralCohomologyIso (i : ℕ) :
    (((moduleFinsuppFunctor k ℤ).mapHomologicalComplex _).obj C).homology i ≅
      (moduleFinsuppFunctor k ℤ).obj (C.homology i) :=
  (C.sc i).mapHomologyIso (moduleFinsuppFunctor k ℤ)

theorem bilateralCohomologyIso_translation (z : Multiplicative ℤ) (i : ℕ) :
    HomologicalComplex.homologyMap (bilateralCochainTranslation k C z) i ≫
        (bilateralCohomologyIso k C i).hom =
      (bilateralCohomologyIso k C i).hom ≫
        (bilateralFunctorTranslation k z).app (C.homology i) := by
  have h := (C.sc i).homologyMap_mapNatTrans (bilateralFunctorTranslation k z)
  change HomologicalComplex.homologyMap (bilateralCochainTranslation k C z) i =
    (bilateralCohomologyIso k C i).hom ≫
      (bilateralFunctorTranslation k z).app (C.homology i) ≫
        (bilateralCohomologyIso k C i).inv at h
  rw [h, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem bilateralCohomologyIso_map (f : C ⟶ C) (i : ℕ) :
    HomologicalComplex.homologyMap
        (((moduleFinsuppFunctor k ℤ).mapHomologicalComplex _).map f) i ≫
        (bilateralCohomologyIso k C i).hom =
      (bilateralCohomologyIso k C i).hom ≫
        (moduleFinsuppFunctor k ℤ).map (HomologicalComplex.homologyMap f i) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ i).map f) (moduleFinsuppFunctor k ℤ)

theorem bilateralCohomologyIso_twist (f : C ⟶ C) (i : ℕ) :
    HomologicalComplex.homologyMap (bilateralCochainTwist k C f) i ≫
        (bilateralCohomologyIso k C i).hom =
      (bilateralCohomologyIso k C i).hom ≫
        (bilateralFunctorTranslation k (Multiplicative.ofAdd 1)).app (C.homology i) ≫
          (moduleFinsuppFunctor k ℤ).map (HomologicalComplex.homologyMap f i) := by
  rw [bilateralCochainTwist, HomologicalComplex.homologyMap_comp, Category.assoc,
    bilateralCohomologyIso_map, ← Category.assoc, bilateralCohomologyIso_translation]
  exact Category.assoc _ _ _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_BooleanStepProjective
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.telescopeAugmentation_epi _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countable Boolean step rings are projective over the integers

Enumerating the Boolean coordinates gives a sequence of finite partitions.
Their modules are free, the refinement maps split, and their colimit is the
step ring itself. No freeness theorem about all bounded functions is needed.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
variable {X I : Type} (a : I → X → Bool) (b : ℕ → I)

theorem booleanPrefix_mono {i j : ℕ} (h : i ≤ j) : booleanPrefix b i ⊆ booleanPrefix b j := by
  classical
  exact Finset.image_subset_image (Finset.range_mono h)

theorem exists_booleanPrefix_contains (hb : Function.Surjective b) (s : Finset I) :
    ∃ n, s ⊆ booleanPrefix b n := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, Finset.empty_subset _⟩
  | @insert i s _ ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, hm⟩ := hb i
    refine ⟨max n (m + 1), Finset.insert_subset_iff.mpr ⟨?_, ?_⟩⟩
    · apply booleanPrefix_mono b (Nat.le_max_right n (m + 1))
      exact Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr (Nat.lt_succ_self m), hm⟩
    · exact hn.trans (booleanPrefix_mono b (Nat.le_max_left n (m + 1)))

def booleanPartitionDiagram : SequentialRepresentationDiagram PUnit.{1} where
  obj n := booleanPartitionStage a (booleanPrefix b n)
  map _ _ h := booleanPartitionMap a (booleanPrefix_mono b h)
  map_id n := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    funext c
    rfl
  map_comp i j k hij hjk := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    funext c
    rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_CompletedIdentity
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalizedStableSyzygyIterate_class
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete identity detects finite integral cohomological dimension

The class of the augmentation is transported into ordinary cohomology. Its
successive connecting images are the syzygy identity classes. Vanishing of
its image in complete cohomology therefore forces a projective syzygy.
No vanishing from FP-infinity is assumed or asserted.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (G : Type) [Group G]

def normalizedGroupIdentityClass (n : ℕ) :
    normalizedCohomologyStage (trivialIntegral G) n :=
  (coefficientNaturalCohomologyIso (normalizedProjectiveResolution (trivialIntegral G))
    ((iteratedNormalizedSyzygy n).obj (trivialIntegral G)) n).inv
      (normalizedIdentityClass (trivialIntegral G) n)

@[simp]
theorem normalizedGroupIdentityClass_comparison (n : ℕ) :
    (coefficientNaturalCohomologyIso (normalizedProjectiveResolution (trivialIntegral G))
      ((iteratedNormalizedSyzygy n).obj (trivialIntegral G)) n).hom
        (normalizedGroupIdentityClass G n) = normalizedIdentityClass (trivialIntegral G) n := by
  exact ConcreteCategory.congr_hom
    (coefficientNaturalCohomologyIso (normalizedProjectiveResolution (trivialIntegral G))
      ((iteratedNormalizedSyzygy n).obj (trivialIntegral G)) n).inv_hom_id
        (normalizedIdentityClass (trivialIntegral G) n)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_FiniteProjectivePresentations
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite projective covers of finitely generated representations -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped MonoidAlgebra
variable {G : Type} [Group G]

theorem finiteIntegralFreeCover_exists (A : Rep.{0} ℤ G)
    (hA : IntegralRepresentationFinite G A) :
    ∃ (ι : Type) (_ : Finite ι) (f : Rep.free ℤ G ι ⟶ A), Epi f := by
  classical
  let : Module ℤ A := A.hV2
  let : Module.Finite ℤ[G] A.ρ.asModule := hA
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp (Module.Finite.fg_top (R := ℤ[G])
    (M := A.ρ.asModule))
  let : Finite s := hs.to_subtype
  let f : Rep.free ℤ G s ⟶ A := Rep.freeLift ℤ G A (fun a : s => A.ρ.asModuleEquiv a.val)
  let fM := Representation.IntertwiningMap.equivLinearMapAsModule
    (Representation.free ℤ G s) A.ρ f.hom
  have hfM : Function.Surjective fM := by
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    intro a ha
    refine ⟨Finsupp.single (⟨a, ha⟩ : s) (MonoidAlgebra.single 1 1), ?_⟩
    apply A.ρ.asModuleEquiv.injective
    change f.hom (Finsupp.single (⟨a, ha⟩ : s) (MonoidAlgebra.single 1 1)) = _
    change Representation.freeLift A.ρ (fun a : s => A.ρ.asModuleEquiv a.val)
      (Finsupp.single (⟨a, ha⟩ : s) (MonoidAlgebra.single 1 1)) = A.ρ.asModuleEquiv a
    rw [Representation.freeLift_single_single]
    simp only [map_one, Module.End.one_apply]
    exact @one_smul ℤ A _ A.hV2.toMulAction _
  have hf : Epi f := by
    rw [Rep.epi_iff_surjective]
    intro a
    obtain ⟨b, hb⟩ := hfM (A.ρ.asModuleEquiv.symm a)
    exact ⟨b, congrArg A.ρ.asModuleEquiv hb⟩
  exact ⟨s, inferInstance, f, hf⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NormalizedSyzygyColimit
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.telescopeAugmentation_epi _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.telescopeShift_inclusion _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.telescopeShift_succ _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.telescopeShift_zero _root_.OAI.PolycyclicRecognition.completedCohomologyMap_of _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalizedCohomologyStageMap_id _root_.OAI.PolycyclicRecognition.normalizedGroupIdentityClass_comparison _root_.OAI.PolycyclicRecognition.normalizedResolutionComplex_d _root_.OAI.PolycyclicRecognition.normalizedStableSyzygyIterate_class _root_.OAI.PolycyclicRecognition.normalizedStableSyzygyMap_class
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized syzygies preserve sequential coefficient colimits -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]
namespace SequentialRepresentationDiagram.ColimitCocone
variable {D : SequentialRepresentationDiagram G} {A : Rep.{0} ℤ G}
  (c : D.ColimitCocone A)

def normalizedSyzygy : (D.mapFunctor normalizedSyzygyFunctor).ColimitCocone
    (PolycyclicRecognition.normalizedSyzygy A) where
  ι i := normalizedSyzygyMap (c.ι i)
  comm i j h := by
    change normalizedSyzygyFunctor.map (D.map i j h) ≫ normalizedSyzygyFunctor.map (c.ι j) =
      normalizedSyzygyFunctor.map (c.ι i)
    rw [← CategoryTheory.Functor.map_comp, c.comm]
  surj x := by
    obtain ⟨i, y, hy⟩ := c.normalizedFree.surj
      ((kernel.ι (normalizedFreeAugmentation A)).hom x)
    change normalizedFreeRepresentation (D.obj i) at y
    change (normalizedFreeMap (c.ι i)).hom y =
      (kernel.ι (normalizedFreeAugmentation A)).hom x at hy
    have h0 : (c.ι i).hom ((normalizedFreeAugmentation (D.obj i)).hom y) = 0 := by
      have he := ConcreteCategory.congr_hom (normalizedFreeAugmentation_natural (c.ι i)) y
      change (normalizedFreeAugmentation A).hom ((normalizedFreeMap (c.ι i)).hom y) = _ at he
      rw [hy] at he
      have hk := ConcreteCategory.congr_hom (kernel.condition (normalizedFreeAugmentation A)) x
      exact he.symm.trans hk
    obtain ⟨j, hij, hj⟩ := c.zero_exact i ((normalizedFreeAugmentation (D.obj i)).hom y) h0
    let yj := (normalizedFreeMap (D.map i j hij)).hom y
    have h0j : (normalizedFreeAugmentation (D.obj j)).hom yj = 0 := by
      have he := ConcreteCategory.congr_hom (normalizedFreeAugmentation_natural (D.map i j hij)) y
      exact he.trans hj
    obtain ⟨z, hz⟩ := (rep_shortComplex_exact_iff
      (normalizedSyzygySequence (D.obj j))).mp
        (normalizedSyzygySequence_shortExact (D.obj j)).exact yj h0j
    change PolycyclicRecognition.normalizedSyzygy (D.obj j) at z
    change (kernel.ι (normalizedFreeAugmentation (D.obj j))).hom z = yj at hz
    refine ⟨j, z, ?_⟩
    apply (Rep.mono_iff_injective (kernel.ι (normalizedFreeAugmentation A))).mp inferInstance
    have he := ConcreteCategory.congr_hom (normalizedSyzygyMap_ι (c.ι j)) z
    change (kernel.ι (normalizedFreeAugmentation A)).hom
      ((normalizedSyzygyMap (c.ι j)).hom z) =
        (normalizedFreeMap (c.ι j)).hom ((kernel.ι (normalizedFreeAugmentation (D.obj j))).hom z) at he
    rw [hz] at he
    have hc : (normalizedFreeMap (c.ι j)).hom yj = (normalizedFreeMap (c.ι i)).hom y := by
      change (normalizedFreeMap (D.map i j hij) ≫ normalizedFreeMap (c.ι j)).hom y = _
      rw [← normalizedFreeMap_comp, c.comm]
    exact he.trans (hc.trans hy)
  zero_exact i x hx := by
    change PolycyclicRecognition.normalizedSyzygy (D.obj i) at x
    change (normalizedSyzygyMap (c.ι i)).hom x = 0 at hx
    have he := ConcreteCategory.congr_hom (normalizedSyzygyMap_ι (c.ι i)) x
    change (kernel.ι (normalizedFreeAugmentation A)).hom ((normalizedSyzygyMap (c.ι i)).hom x) =
      (normalizedFreeMap (c.ι i)).hom ((kernel.ι (normalizedFreeAugmentation (D.obj i))).hom x) at he
    rw [hx, map_zero] at he
    obtain ⟨j, hij, hj⟩ := c.normalizedFree.zero_exact i
      ((kernel.ι (normalizedFreeAugmentation (D.obj i))).hom x) he.symm
    refine ⟨j, hij, ?_⟩
    change (normalizedSyzygyMap (D.map i j hij)).hom x = 0
    apply (Rep.mono_iff_injective (kernel.ι (normalizedFreeAugmentation (D.obj j)))).mp inferInstance
    have hf := ConcreteCategory.congr_hom (normalizedSyzygyMap_ι (D.map i j hij)) x
    change (kernel.ι (normalizedFreeAugmentation (D.obj j))).hom
      ((normalizedSyzygyMap (D.map i j hij)).hom x) =
      (normalizedFreeMap (D.map i j hij)).hom
        ((kernel.ι (normalizedFreeAugmentation (D.obj i))).hom x) at hf
    exact (hf.trans hj).trans (map_zero
      (kernel.ι (normalizedFreeAugmentation (D.obj j))).hom).symm

def iteratedNormalizedSyzygy (n : ℕ) :
    (D.mapFunctor (PolycyclicRecognition.iteratedNormalizedSyzygy n)).ColimitCocone
      ((PolycyclicRecognition.iteratedNormalizedSyzygy n).obj A) := by
  induction n with
  | zero => exact c
  | succ n ih => exact ih.normalizedSyzygy

@[simp]
theorem iteratedNormalizedSyzygy_ι (n i : ℕ) :
    (c.iteratedNormalizedSyzygy n).ι i =
      (PolycyclicRecognition.iteratedNormalizedSyzygy n).map (c.ι i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change normalizedSyzygyMap ((c.iteratedNormalizedSyzygy n).ι i) =
      normalizedSyzygyMap ((PolycyclicRecognition.iteratedNormalizedSyzygy n).map (c.ι i))
    exact congrArg normalizedSyzygyMap ih

end SequentialRepresentationDiagram.ColimitCocone
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ShiftedCompletedCohomology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.iteratedNormalizedSyzygy_ι _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.normalizedGroupIdentityClass_comparison _root_.OAI.PolycyclicRecognition.normalizedResolutionComplex_d _root_.OAI.PolycyclicRecognition.normalizedStableSyzygyIterate_class
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonnegative degree shifts of complete cohomology

The hierarchy argument uses positive connecting degrees. The n-th stage is
H^(n+p)(G, Omega^n A), with the actual coefficient connecting maps.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

def shiftedSyzygyConnecting (p : ℕ) (A : Rep.{0} ℤ G) (n : ℕ) :
    groupCohomology ((iteratedNormalizedSyzygy n).obj A) (n + p) ⟶
      groupCohomology ((iteratedNormalizedSyzygy (n + 1)).obj A) (n + 1 + p) :=
  groupCohomology.δ (normalizedSyzygySequence_shortExact
    ((iteratedNormalizedSyzygy n).obj A)) (n + p) (n + 1 + p) (by omega)

abbrev shiftedCohomologyStage (p : ℕ) (A : Rep.{0} ℤ G) (n : ℕ) : Type :=
  groupCohomology ((iteratedNormalizedSyzygy n).obj A) (n + p)

def shiftedCohomologyStageMap (p : ℕ) {A B : Rep.{0} ℤ G} (f : A ⟶ B) (n : ℕ) :
    shiftedCohomologyStage p A n →ₗ[ℤ] shiftedCohomologyStage p B n :=
  (groupCohomology.map (MonoidHom.id G) ((iteratedNormalizedSyzygy n).map f) (n + p)).hom

@[simp]
theorem shiftedCohomologyStageMap_id (p : ℕ) (A : Rep.{0} ℤ G) (n : ℕ) :
    shiftedCohomologyStageMap p (𝟙 A) n = LinearMap.id := by
  unfold shiftedCohomologyStageMap
  rw [CategoryTheory.Functor.map_id, groupCohomology.map_id]
  rfl

theorem shiftedSyzygyConnecting_natural (p : ℕ) {A B : Rep.{0} ℤ G} (f : A ⟶ B) (n : ℕ) :
    shiftedSyzygyConnecting p A n ≫
        groupCohomology.map (MonoidHom.id G) ((iteratedNormalizedSyzygy (n + 1)).map f) (n + 1 + p) =
      groupCohomology.map (MonoidHom.id G) ((iteratedNormalizedSyzygy n).map f) (n + p) ≫
        shiftedSyzygyConnecting p B n :=
  groupCohomology.δ_naturality
    (normalizedSyzygySequence_shortExact ((iteratedNormalizedSyzygy n).obj A))
    (normalizedSyzygySequence_shortExact ((iteratedNormalizedSyzygy n).obj B))
    (normalizedSyzygySequenceMap ((iteratedNormalizedSyzygy n).map f)) (n + p) (n + 1 + p) (by omega)

def shiftedCohomologyForward (p : ℕ) (A : Rep.{0} ℤ G) (i j : ℕ) (h : i ≤ j) :
    shiftedCohomologyStage p A i →ₗ[ℤ] shiftedCohomologyStage p A j where
  toFun := Nat.leRecOn h (fun {k} => (shiftedSyzygyConnecting p A k).hom)
  map_add' x y := by
    induction h with
    | refl => simp only [Nat.leRecOn_self]
    | @step j h ih => simp only [Nat.leRecOn_succ h, map_add, ih]
  map_smul' r x := by
    induction h with
    | refl => simp only [Nat.leRecOn_self, RingHom.id_apply]
    | @step j h ih =>
      simp only [Nat.leRecOn_succ h, ih, RingHom.id_apply]
      exact (shiftedSyzygyConnecting p A j).hom.map_smul r _

theorem shiftedCohomologyForward_natural (p : ℕ) {A B : Rep.{0} ℤ G} (f : A ⟶ B)
    (i j : ℕ) (h : i ≤ j) (x : shiftedCohomologyStage p A i) :
    shiftedCohomologyStageMap p f j (shiftedCohomologyForward p A i j h x) =
      shiftedCohomologyForward p B i j h (shiftedCohomologyStageMap p f i x) := by
  induction h with
  | refl =>
    simp only [shiftedCohomologyForward, Nat.leRecOn_self]
    rfl
  | @step j h ih =>
    change shiftedCohomologyStageMap p f (j + 1)
      (Nat.leRecOn (C := shiftedCohomologyStage p A) _
        (fun {k} => (shiftedSyzygyConnecting p A k).hom) x) =
      Nat.leRecOn (C := shiftedCohomologyStage p B) _
        (fun {k} => (shiftedSyzygyConnecting p B k).hom) _
    rw [Nat.leRecOn_succ h, Nat.leRecOn_succ h]
    have hn := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (shiftedSyzygyConnecting_natural p f j)) (shiftedCohomologyForward p A i j h x)
    change shiftedCohomologyStageMap p f (j + 1)
      ((shiftedSyzygyConnecting p A j).hom _) =
        (shiftedSyzygyConnecting p B j).hom
          (shiftedCohomologyForward p B i j h (shiftedCohomologyStageMap p f i x))
    rw [← ih]
    exact hn

abbrev ShiftedCompletedCohomology (p : ℕ) (A : Rep.{0} ℤ G) :=
  Module.DirectLimit (shiftedCohomologyStage p A) (shiftedCohomologyForward p A)

def shiftedCompletedCohomologyMap (p : ℕ) {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    ShiftedCompletedCohomology p A →ₗ[ℤ] ShiftedCompletedCohomology p B :=
  Module.DirectLimit.map (f := shiftedCohomologyForward p A)
    (f' := shiftedCohomologyForward p B) (shiftedCohomologyStageMap p f)
    (fun i j h => by
      apply LinearMap.ext
      exact shiftedCohomologyForward_natural p f i j h)

@[simp]
theorem shiftedCompletedCohomologyMap_of (p : ℕ) {A B : Rep.{0} ℤ G} (f : A ⟶ B) (i : ℕ)
    (x : shiftedCohomologyStage p A i) :
    shiftedCompletedCohomologyMap p f
      (Module.DirectLimit.of ℤ ℕ _ (shiftedCohomologyForward p A) i x) =
    Module.DirectLimit.of ℤ ℕ _ (shiftedCohomologyForward p B) i
      (shiftedCohomologyStageMap p f i x) := by
  exact Module.DirectLimit.map_apply_of (shiftedCohomologyStageMap p f)
    (fun i j h => by
      apply LinearMap.ext
      exact shiftedCohomologyForward_natural p f i j h) x

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_InductionExhaustionVanishing
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.SequentialRepresentationDiagram.ColimitCocone.telescopeAugmentation_epi _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complete vanishing for induction along a subgroup exhaustion

The finite stages may have arbitrarily large projective dimensions. The
ambient group's FP-infinity hypothesis supplies continuity of its completed
cohomology for the actual induced-coefficient colimit.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

namespace SequentialRepresentationDiagram.ColimitCocone
variable {D : SequentialRepresentationDiagram G} {A B : Rep.{0} ℤ G}

def transportIso (c : D.ColimitCocone A) (e : A ≅ B) : D.ColimitCocone B where
  ι n := c.ι n ≫ e.hom
  comm i j h := by rw [← Category.assoc, c.comm]
  surj b := by
    obtain ⟨n, x, hx⟩ := c.surj (e.inv.hom b)
    refine ⟨n, x, ?_⟩
    change e.hom.hom ((c.ι n).hom x) = b
    rw [hx]
    exact ConcreteCategory.congr_hom e.inv_hom_id b
  zero_exact i x hx := by
    apply c.zero_exact i x
    apply (Rep.mono_iff_injective e.hom).mp inferInstance
    change e.hom.hom ((c.ι i).hom x) = e.hom.hom 0
    change e.hom.hom ((c.ι i).hom x) = 0 at hx
    simpa only [map_zero] using hx

end SequentialRepresentationDiagram.ColimitCocone

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ProjectiveKernelStableMap
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Maps between projective presentations preserve stable zero maps -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem projectiveKernelMap_stable_zero
    {S T : ShortComplex (Rep.{0} ℤ G)} (_hS : S.ShortExact) (hT : T.ShortExact)
    [Projective S.X₂] (φ : S ⟶ T)
    (hφ : stableRepresentationClass _ _ φ.τ₃ = 0) :
    stableRepresentationClass _ _ φ.τ₁ = 0 := by
  let : Mono T.f := hT.mono_f
  let : Epi T.g := hT.epi_g
  obtain ⟨P, hP, u, v, huv⟩ := (stableRepresentationClass_eq_zero_iff_projective_factor _).mp hφ
  let : Projective P := hP
  let l : P ⟶ T.X₂ := Projective.factorThru v T.g
  have hl : l ≫ T.g = v := Projective.factorThru_comp _ _
  let d := φ.τ₂ - S.g ≫ u ≫ l
  have hd : d ≫ T.g = 0 := by
    dsimp only [d]
    rw [Preadditive.sub_comp, φ.comm₂₃, Category.assoc, Category.assoc, hl, huv, sub_self]
  let w := hT.exact.lift d hd
  apply (stableRepresentationClass_eq_zero_iff_projective_factor _).mpr
  refine ⟨S.X₂, inferInstance, S.f, w, ?_⟩
  apply (cancel_mono T.f).mp
  rw [Category.assoc, hT.exact.lift_f, φ.comm₁₂]
  dsimp only [d]
  rw [Preadditive.comp_sub, ← Category.assoc, ← Category.assoc,
    S.zero, zero_comp, zero_comp, sub_zero]

theorem projectiveKernelMap_stable_eq
    {S T : ShortComplex (Rep.{0} ℤ G)} (hS : S.ShortExact) (hT : T.ShortExact)
    [Projective S.X₂] (φ ψ : S ⟶ T)
    (hφψ : stableRepresentationClass _ _ φ.τ₃ = stableRepresentationClass _ _ ψ.τ₃) :
    stableRepresentationClass _ _ φ.τ₁ = stableRepresentationClass _ _ ψ.τ₁ := by
  have h : stableRepresentationClass _ _ (φ - ψ).τ₃ = 0 := by
    rw [ShortComplex.sub_τ₃, map_sub, hφψ, sub_self]
  have hz := projectiveKernelMap_stable_zero hS hT (φ - ψ) h
  rw [ShortComplex.sub_τ₁, map_sub] at hz
  exact sub_eq_zero.mp hz

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_IntegralProjectiveTower
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.IntegralProjectiveTower.instDirectedSystemNatCohomologyStageCoeLinearMapIntIdForward _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integral projective syzygy towers

This records the successive projective presentations used by the normalized
and horseshoe constructions. Maps lift recursively, and their induced stable
maps depend only on the stable map at the initial coefficient.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

namespace IntegralProjectiveTower

namespace Map
variable {T U V : IntegralProjectiveTower G}

theorem stable_eq (f g : Map T U)
    (h : stableRepresentationClass _ _ (f.app 0) = stableRepresentationClass _ _ (g.app 0))
    (n : ℕ) :
    stableRepresentationClass _ _ (f.app n) = stableRepresentationClass _ _ (g.app n) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    exact projectiveKernelMap_stable_eq (T.shortExact n) (U.shortExact n)
      (f.sequenceMap n) (g.sequenceMap n) ih

end Map

end IntegralProjectiveTower
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ProjectiveTowerCohomology
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cohomology along a projective syzygy tower -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem cohomologyConnecting_projective_factor
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (i j : ℕ) (hij : i + 1 = j) {A : Rep.{0} ℤ G} (f : A ⟶ S.X₃)
    (hf : stableRepresentationClass _ _ f = 0) :
    (groupCohomology.functor ℤ G i).map f ≫ groupCohomology.δ hS i j hij = 0 := by
  let F := groupCohomology.functor ℤ G i
  let δ : F.obj S.X₃ ⟶ groupCohomology S.X₁ j := groupCohomology.δ hS i j hij
  change F.map f ≫ δ = 0
  let : Epi S.g := hS.epi_g
  obtain ⟨P, hP, u, v, huv⟩ := (stableRepresentationClass_eq_zero_iff_projective_factor f).mp hf
  let : Projective P := hP
  let l := Projective.factorThru v S.g
  have hl : l ≫ S.g = v := Projective.factorThru_comp _ _
  have hz := (groupCohomology.mapShortComplex₃ hS hij).zero
  change F.map S.g ≫ δ = 0 at hz
  rw [← huv, ← hl, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    Category.assoc, Category.assoc, hz, comp_zero, comp_zero]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_ProjectiveTowerComparison
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independence of the projective syzygy tower -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]
namespace IntegralProjectiveTower
namespace Map
variable {T U V : IntegralProjectiveTower G}

theorem cohomologyMap_eq_of_stable_eq (f g : Map T U)
    (h : stableRepresentationClass _ _ (f.app 0) = stableRepresentationClass _ _ (g.app 0))
    (p : ℕ) : f.cohomologyMap p = g.cohomologyMap p := by
  apply LinearMap.ext
  intro x
  obtain ⟨n, z, rfl⟩ := Module.DirectLimit.exists_of x
  have hs : stableRepresentationClass _ _ (f.app n - g.app n) = 0 := by
    rw [map_sub, f.stable_eq g h n, sub_self]
  have hc := cohomologyConnecting_projective_factor (U.sequence n) (U.shortExact n)
    (n + p) (n + 1 + p) (by omega) (f.app n - g.app n) hs
  have hz := ConcreteCategory.congr_hom hc z
  change (U.connecting p n).hom
    (((groupCohomology.functor ℤ G (n + p)).map (f.app n - g.app n)).hom z) = 0 at hz
  rw [CategoryTheory.Functor.map_sub] at hz
  have hstep : U.forward p n (n + 1) (Nat.le_succ n)
      (f.stageMap p n z - g.stageMap p n z) = 0 := by
    change Nat.leRecOn (C := U.cohomologyStage p) (Nat.le_succ n)
      (fun {k} => (U.connecting p k).hom) _ = 0
    rw [Nat.leRecOn_succ (le_refl n), Nat.leRecOn_self]
    exact hz
  have he := Module.DirectLimit.of_f (R := ℤ) (ι := ℕ) (G := U.cohomologyStage p)
    (f := U.forward p) (hij := Nat.le_succ n) (x := f.stageMap p n z - g.stageMap p n z)
  rw [hstep, map_zero] at he
  rw [cohomologyMap_of, cohomologyMap_of, ← sub_eq_zero, ← map_sub]
  exact he.symm

end Map

def cohomologyEquiv {T U : IntegralProjectiveTower G} (e : T.obj 0 ≅ U.obj 0) (p : ℕ) :
    T.Cohomology p ≃ₗ[ℤ] U.Cohomology p := by
  let f := liftMap T U e.hom
  let g := liftMap U T e.inv
  refine LinearEquiv.ofLinearMap (f.cohomologyMap p) (g.cohomologyMap p) ?_ ?_
  · rw [← Map.cohomologyMap_comp]
    have h : stableRepresentationClass _ _ ((g.comp f).app 0) =
        stableRepresentationClass _ _ ((Map.identity U).app 0) := by
      change stableRepresentationClass _ _ (e.inv ≫ e.hom) = stableRepresentationClass _ _ (𝟙 _)
      rw [e.inv_hom_id]
    rw [Map.cohomologyMap_eq_of_stable_eq (g.comp f) (Map.identity U) h, Map.cohomologyMap_identity]
  · rw [← Map.cohomologyMap_comp]
    have h : stableRepresentationClass _ _ ((f.comp g).app 0) =
        stableRepresentationClass _ _ ((Map.identity T).app 0) := by
      change stableRepresentationClass _ _ (e.hom ≫ e.inv) = stableRepresentationClass _ _ (𝟙 _)
      rw [e.hom_inv_id]
    rw [Map.cohomologyMap_eq_of_stable_eq (f.comp g) (Map.identity T) h, Map.cohomologyMap_identity]

end IntegralProjectiveTower
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Finiteness_NormalizedProjectiveTower
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.booleanPartitionStage_projective _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparison with the normalized complete-cohomology construction -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

def normalizedProjectiveTower (A : Rep.{0} ℤ G) : IntegralProjectiveTower G where
  obj n := (iteratedNormalizedSyzygy n).obj A
  projectiveObj n := normalizedFreeRepresentation ((iteratedNormalizedSyzygy n).obj A)
  projective _n := inferInstance
  ι n := kernel.ι (normalizedFreeAugmentation ((iteratedNormalizedSyzygy n).obj A))
  π n := normalizedFreeAugmentation ((iteratedNormalizedSyzygy n).obj A)
  zero _n := kernel.condition _
  shortExact _n := normalizedSyzygySequence_shortExact _

def normalizedProjectiveTowerCohomology (A : Rep.{0} ℤ G) (p : ℕ) :
    (normalizedProjectiveTower A).Cohomology p ≃ₗ[ℤ] ShiftedCompletedCohomology p A :=
  LinearEquiv.refl ℤ _

def IntegralProjectiveTower.completeCohomologyEquiv (T : IntegralProjectiveTower G)
    (A : Rep.{0} ℤ G) (e : T.obj 0 ≅ A) (p : ℕ) :
    T.Cohomology p ≃ₗ[ℤ] ShiftedCompletedCohomology p A :=
  (IntegralProjectiveTower.cohomologyEquiv (show T.obj 0 ≅ (normalizedProjectiveTower A).obj 0 from e) p).trans
    (normalizedProjectiveTowerCohomology A p)

def IntegralProjectiveTower.normalization (T : IntegralProjectiveTower G) :
    IntegralProjectiveTower.Map T (normalizedProjectiveTower (T.obj 0)) :=
  IntegralProjectiveTower.liftMap T (normalizedProjectiveTower (T.obj 0)) (𝟙 _)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AbelianLieModel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The abelian base case of nilpotent Lie model existence

An abelian real Lie algebra is integrated by its additive vector group.
The equivalence below identifies the actual invariant-vector-field bracket.
-/

noncomputable section
namespace PolycyclicRecognition

open VectorField
open scoped Manifold

variable {V : Type*} [RealNormedLieAlgebra V]

local instance vectorGroupChartedSpace : ChartedSpace V (Multiplicative V) :=
  inferInstanceAs (ChartedSpace V V)

local instance vectorGroupLieGroup : LieGroup (𝓘(ℝ, V)) ⊤ (Multiplicative V) where
  toIsManifold := by change IsManifold (𝓘(ℝ, V)) ⊤ V; infer_instance
  contMDiff_mul := by
    change ContMDiff ((𝓘(ℝ, V)).prod (𝓘(ℝ, V))) (𝓘(ℝ, V)) ⊤
      (fun p : V × V => p.1 + p.2)
    exact contMDiff_add (I := 𝓘(ℝ, V)) (n := ⊤)
  contMDiff_inv := by
    change ContMDiff (𝓘(ℝ, V)) (𝓘(ℝ, V)) ⊤ (fun v : V => -v)
    exact contDiff_neg.contMDiff

theorem vectorGroup_invariantField
    (v : GroupLieAlgebra (𝓘(ℝ, V)) (Multiplicative V)) (g : Multiplicative V) :
    mulInvariantVectorField v g = v := by
  change mfderiv (𝓘(ℝ, V)) (𝓘(ℝ, V)) (fun x : V => g.toAdd + x) 0 v = v
  have hd : HasFDerivAt (fun x : V => g.toAdd + x) (ContinuousLinearMap.id ℝ V) 0 :=
    (hasFDerivAt_id (𝕜 := ℝ) (0 : V)).const_add g.toAdd
  exact congrArg (fun A : V →L[ℝ] V => A (v : V)) hd.hasMFDerivAt.mfderiv

theorem vectorGroup_bracket
    (v w : GroupLieAlgebra (𝓘(ℝ, V)) (Multiplicative V)) : ⁅v, w⁆ = 0 := by
  rw [GroupLieAlgebra.bracket_def]
  have hv : mulInvariantVectorField v = (fun _ : Multiplicative V => v) :=
    funext (vectorGroup_invariantField v)
  have hw : mulInvariantVectorField w = (fun _ : Multiplicative V => w) :=
    funext (vectorGroup_invariantField w)
  rw [hv, hw]
  have hconst (x y : V) :
      lieBracketWithin ℝ (fun _ : V => x) (fun _ : V => y) Set.univ 0 = 0 := by
    simp [lieBracketWithin]
  exact (congrFun (mlieBracketWithin_eq_lieBracketWithin
    (V := fun _ : V => v) (W := fun _ : V => w) (s := Set.univ)) (0 : V)).trans (hconst v w)

variable [FiniteDimensional ℝ V] [IsLieAbelian V]

/-- The additive group, equipped with its actual tangent Lie algebra. -/
def abelianLieModel : NilpotentLieModel V := by
  let : MeasurableSpace (Multiplicative V) := borel _
  let : BorelSpace (Multiplicative V) := ⟨rfl⟩
  let : SimplyConnectedSpace (Multiplicative V) :=
    inferInstanceAs (SimplyConnectedSpace V)
  exact
    { modelSpace := V
      carrier := Multiplicative V
      equiv :=
        { LinearEquiv.refl ℝ V with
          map_lie' := by
            intro x y
            have hzero : ⁅x, y⁆ = (0 : V) := LieModule.IsTrivial.trivial x y
            exact hzero.trans (vectorGroup_bracket (V := V) x y).symm } }

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AdjointExponentialRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the actual adjoint exponential through a faithful representation -/

noncomputable section
namespace PolycyclicRecognition

section Algebra

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

local instance adjointExponentialNormedAddCommGroup : NormedAddCommGroup L :=
  generatorConjugationNormedAddCommGroup
local instance adjointExponentialNormedSpace : NormedSpace ℝ L := generatorConjugationNormedSpace

open scoped Matrix.Norms.Operator

/-- The algebraic endomorphism underlying the analytic exponential of `ad x`.
The auxiliary finite-dimensional norm is not part of the output. -/
def adjointExponentialLinear (x : L) : L →ₗ[ℝ] L :=
  (NormedSpace.exp (continuousAd x)).toLinearMap

attribute [local instance 100] LieRing.ofAssociativeRing

end Algebra

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularMatrixExponential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Diagonal entries of an upper triangular matrix exponential -/

noncomputable section
namespace PolycyclicRecognition

open scoped Matrix.Norms.Operator

variable {n : ℕ}

theorem matrix_exp_diagonal (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) (i : Fin n) :
    NormedSpace.exp A i i = Real.exp (A i i) := by
  have hp (k : ℕ) : (A ^ k) i i = (A i i) ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, triangular_mul_diag _ _ (hA.pow k) hA, ih, pow_succ]
  have hs := matrix_exp_entry_hasSum A i i
  simp only [hp] at hs
  have ht : HasSum (fun k : ℕ => (k.factorial : ℝ)⁻¹ * (A i i) ^ k)
      (Real.exp (A i i)) := by
    simpa only [smul_eq_mul, ← Real.exp_eq_exp_ℝ] using
      NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (A i i)
  exact hs.unique ht

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AdjointMatrixHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic diagonal characters of the actual adjoint action -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

def adjointMatrixHom {n : ℕ} (b : Module.Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    G →* Matrix (Fin n) (Fin n) ℝ :=
  (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp
    (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp conjugationDifferentialHom)

attribute [local instance 100] LieRing.ofAssociativeRing

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AlgebraExponentialNaturality
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential compatibility from the actual algebra-valued derivative -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem hom_exp_eq_algebraExpUnit
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (ρ : G →* Aˣ) (j : GroupLieAlgebra (𝓘(ℝ, E)) G →L[ℝ] A)
    (hd : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, A)) (fun g => (ρ g : A)) 1 j)
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) : ρ (Exp x) = algebraExpUnit (j x) := by
  let f : ℝ → A := fun t => (ρ (Exp (t • x)) : A)
  have hbase : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, A))
      (fun g => (ρ g : A)) (Exp ((0 : ℝ) • x)) j := by
    rw [zero_smul, hExp.map_zero]
    exact hd
  have h := hbase.comp 0 (hExp.hasMFDerivAt_zero x)
  have hf : HasDerivAt f (j x) 0 := by
    have hF : HasFDerivAt f
        (j.comp (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) x)) 0 :=
      h.hasFDerivAt
    have hh := hF.hasDerivAt
    change HasDerivAt f (j ((1 : ℝ) • x)) 0 at hh
    simpa only [one_smul] using hh
  have hf0 : f 0 = 1 := by
    dsimp only [f]
    rw [zero_smul, hExp.map_zero, map_one]
    rfl
  have hadd (s t : ℝ) : f (s + t) = f s * f t := by
    dsimp only [f]
    rw [hExp.map_add_smul, map_mul]
    rfl
  apply Units.ext
  have heq := oneParameter_eq_exp hf0 hadd hf 1
  simpa only [f, one_smul, coe_algebraExpUnit] using heq

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AlgebraHomLieDifferential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual differential of an algebra-unit homomorphism

Left-invariant vector fields are related to left multiplication in the
algebra. Preservation of their brackets gives the matrix commutator law.
-/

noncomputable section
namespace PolycyclicRecognition

open Function VectorField
open scoped Manifold ContDiff

variable {E G A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedRing A] [NormedAlgebra ℝ A]

theorem unitsHomDifferential_map_bracket [CompleteSpace E]
    (ρ : G →* Aˣ)
    (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, A)) ∞ (fun g => (ρ g : A)))
    (v w : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    unitsHomDifferential (E := E) ρ 1 (⁅v, w⁆ : GroupLieAlgebra (𝓘(ℝ, E)) G) =
      unitsHomDifferential (E := E) ρ 1 v * unitsHomDifferential (E := E) ρ 1 w -
      unitsHomDifferential (E := E) ρ 1 w * unitsHomDifferential (E := E) ρ 1 v := by
  let D := unitsHomDifferential (E := E) ρ 1
  have hb := mfderiv_mlieBracket_of_related (V' := fun a : A => a * D v)
    (W' := fun a : A => a * D w) hf
    (contMDiff_invariantVectorField_infty v) (contMDiff_invariantVectorField_infty w)
    (differentiable_id.mul_const (D v)) (differentiable_id.mul_const (D w))
    (fun x => mfderiv_unitsHom_invariant ρ hf v x)
    (fun x => mfderiv_unitsHom_invariant ρ hf w x) (1 : G)
  simp only [map_one, Units.val_one, lieBracket_rightMultiplication, one_mul] at hb
  change unitsHomDifferential (E := E) ρ 1 (⁅v, w⁆ : GroupLieAlgebra (𝓘(ℝ, E)) G) =
    D v * D w - D w * D v at hb
  exact hb

attribute [local instance 100] LieRing.ofAssociativeRing

def unitsHomLieDifferential [CompleteSpace E]
    (ρ : G →* Aˣ)
    (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, A)) ∞ (fun g => (ρ g : A))) :
    GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A where
  toLinearMap := (unitsHomDifferential (E := E) ρ 1).toLinearMap
  map_lie' := by
    intro v w
    exact unitsHomDifferential_map_bracket ρ hf v w

theorem hasMFDerivAt_unitsHomLieDifferential [FiniteDimensional ℝ E]
    (ρ : G →* Aˣ)
    (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, A)) ∞ (fun g => (ρ g : A))) :
    HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, A)) (fun g => (ρ g : A)) 1
      (unitsHomLieDifferential ρ hf).toLinearMap.toContinuousLinearMap := by
  apply ((hf 1).mdifferentiableAt (by simp)).hasMFDerivAt.congr_mfderiv
  ext v
  exact congrFun
    (LinearMap.coe_toContinuousLinearMap'
      (unitsHomDifferential (E := E) ρ 1).toLinearMap).symm v

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AlgebraTangentLie
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Lie algebra of tangent spans

Bilinearity extends the computed commutator identity from curve derivatives
to their finite linear span. Thus the derived group controls the derived Lie
algebra without a closed-subgroup theorem.
-/

noncomputable section
namespace PolycyclicRecognition

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [FiniteDimensional ℝ A] [CompleteSpace A]

/-- Commutators of tangent spans lie in the tangent span of the derived group. -/
theorem algebraGroupTangentSpan_commutator {D : Subgroup Aˣ} {X Y : A}
    (hX : X ∈ algebraGroupTangentSpan D) (hY : Y ∈ algebraGroupTangentSpan D) :
    X * Y - Y * X ∈ algebraGroupTangentSpan ⁅D, D⁆ := by
  let N := algebraGroupTangentSpan ⁅D, D⁆
  have hright (x : A) (hx : AlgebraGroupTangentVector D x) :
      ∀ y ∈ algebraGroupTangentSpan D, x * y - y * x ∈ N := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact commutator_mem_derived_tangentSpan hx hy
    | zero => simp
    | add y z hy hz ihy ihz =>
      simpa only [mul_add, add_mul, add_sub_add_comm] using N.add_mem ihy ihz
    | smul r y hy ih =>
      simpa only [mul_smul_comm, smul_mul_assoc, ← smul_sub] using N.smul_mem r ih
  induction hX using Submodule.span_induction with
  | mem x hx => exact hright x hx Y hY
  | zero => simp
  | add x z hx hz ihx ihz =>
    simpa only [mul_add, add_mul, add_sub_add_comm] using N.add_mem ihx ihz
  | smul r x hx ih =>
    simpa only [mul_smul_comm, smul_mul_assoc, ← smul_sub] using N.smul_mem r ih

/-- The tangent span is a concrete Lie subalgebra of the ambient matrix algebra. -/
def algebraGroupTangentLie (D : Subgroup Aˣ) : LieSubalgebra ℝ A :=
  { algebraGroupTangentSpan D with
    lie_mem' := fun {_x _y} hx hy =>
      algebraGroupTangentSpan_mono (Subgroup.commutator_le_self D)
        (algebraGroupTangentSpan_commutator hx hy) }

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AnalyticDerivationFlow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The analytic exponential of any finite-dimensional real derivation

Intertwining the bracket with the operator commutator proves bracket
preservation. The derivation need not be nilpotent.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

theorem derivation_bracket_intertwine (D : LieDerivation ℝ L L) (x : L) :
    normedLieBracket (D x) =
      adjointOperator (LinearMap.toContinuousLinearMap D.toLinearMap) (normedLieBracket x) := by
  apply ContinuousLinearMap.ext
  intro y
  change ⁅D x, y⁆ = D ⁅x, y⁆ - ⁅x, D y⁆
  rw [D.apply_lie_eq_sub]
  have h := lie_skew (D x) y
  rw [← h]
  abel

theorem analytic_derivation_exp_preserves_lie (D : LieDerivation ℝ L L) (x y : L) :
    NormedSpace.exp (LinearMap.toContinuousLinearMap D.toLinearMap) ⁅x, y⁆ =
      ⁅NormedSpace.exp (LinearMap.toContinuousLinearMap D.toLinearMap) x,
        NormedSpace.exp (LinearMap.toContinuousLinearMap D.toLinearMap) y⁆ := by
  let d := LinearMap.toContinuousLinearMap D.toLinearMap
  have h := exp_intertwine_apply (normedLieBracket (L := L)) d (adjointOperator d)
    (derivation_bracket_intertwine D) x
  rw [exp_adjointOperator_apply] at h
  have hi := congrArg (fun T : L →L[ℝ] L => T y) (algebraExpUnit d).inv_val
  change NormedSpace.exp (-d) (NormedSpace.exp d y) = y at hi
  have he := DFunLike.congr_fun h (NormedSpace.exp d y)
  change ⁅NormedSpace.exp d x, NormedSpace.exp d y⁆ =
    NormedSpace.exp d ⁅x, NormedSpace.exp (-d) (NormedSpace.exp d y)⁆ at he
  rw [hi] at he
  exact he.symm

def analyticDerivationExp (D : LieDerivation ℝ L L) : L ≃ₗ⁅ℝ⁆ L :=
  { (ContinuousLinearEquiv.ofUnit
      (algebraExpUnit (LinearMap.toContinuousLinearMap D.toLinearMap))).toLinearEquiv with
    map_lie' := fun {x y} => analytic_derivation_exp_preserves_lie D x y }

@[simp] theorem analyticDerivationExp_apply (D : LieDerivation ℝ L L) (x : L) :
    analyticDerivationExp D x =
      NormedSpace.exp (LinearMap.toContinuousLinearMap D.toLinearMap) x := rfl

def analyticDerivationFlow (D : LieDerivation ℝ L L) (t : ℝ) : L ≃ₗ⁅ℝ⁆ L :=
  analyticDerivationExp (t • D)

theorem analyticDerivationFlow_zero (D : LieDerivation ℝ L L) (x : L) :
    analyticDerivationFlow D 0 x = x := by
  rw [analyticDerivationFlow, zero_smul, analyticDerivationExp_apply]
  change NormedSpace.exp (0 : L →L[ℝ] L) x = x
  rw [NormedSpace.exp_zero]
  rfl

theorem analyticDerivationFlow_add (D : LieDerivation ℝ L L) (s t : ℝ) (x : L) :
    analyticDerivationFlow D (s + t) x =
      analyticDerivationFlow D s (analyticDerivationFlow D t x) := by
  let := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  let d := LinearMap.toContinuousLinearMap D.toLinearMap
  change NormedSpace.exp ((s + t) • d) x =
    NormedSpace.exp (s • d) (NormedSpace.exp (t • d) x)
  rw [add_smul, NormedSpace.exp_add_of_commute
    (((Commute.refl d).smul_left s).smul_right t)]
  rfl

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialSmoothHom
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smoothness and differential of exponential-compatible homomorphisms

Coordinates of the second kind reduce smoothness to the individual
one-parameter subgroups. This applies to arbitrary finite-dimensional Lie
group targets and does not assume a linear representation of the target.
-/

noncomputable section
namespace PolycyclicRecognition

open Function
open scoped Manifold ContDiff

variable {E G F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [ChartedSpace F H] [Group H] [LieGroup (𝓘(ℝ, F)) ⊤ H]

omit [LieGroup (𝓘(ℝ, E)) ⊤ G] [LieGroup (𝓘(ℝ, F)) ⊤ H] in
theorem map_exponentialProduct
    {ExpG : GroupLieAlgebra (𝓘(ℝ, E)) G → G}
    {ExpH : GroupLieAlgebra (𝓘(ℝ, F)) H → H}
    (φ : G →* H) (j : E →ₗ[ℝ] F)
    (hcompat : ∀ v, φ (ExpG v) = ExpH (j v))
    {n : ℕ} (v : Fin n → E) (x : Fin n → ℝ) :
    φ (exponentialProduct ExpG v x) =
      exponentialProduct ExpH (fun i => j (v i)) x := by
  induction n with
  | zero => exact φ.map_one
  | succ n ih =>
    simp only [exponentialProduct, map_mul]
    have hhead : φ (ExpG (x 0 • v 0)) = ExpH (x 0 • j (v 0)) :=
      (hcompat _).trans (congrArg ExpH (j.map_smul _ _))
    exact congrArg₂ (· * ·) hhead (ih (v ∘ Fin.succ) (x ∘ Fin.succ))

/-- Differentiating exponential compatibility recovers the specified linear map. -/
theorem mfderiv_eq_of_exponential_compatibility [T2Space H]
    {ExpG : GroupLieAlgebra (𝓘(ℝ, E)) G → G}
    {ExpH : GroupLieAlgebra (𝓘(ℝ, F)) H → H}
    (hG : IsGroupExponential ExpG) (hH : IsGroupExponential ExpH)
    (φ : G →* H) (hφ : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ)
    (j : E →ₗ[ℝ] F) (hcompat : ∀ v, φ (ExpG v) = ExpH (j v)) (v : E) :
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1 v = j v := by
  apply hH.eq_of_oneParameter_eq
  intro t
  calc
    ExpH (t • mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1 v) =
        ExpH (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1 (t • v)) :=
      congrArg ExpH (map_smul (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1 : E →L[ℝ] F) t v).symm
    _ = φ (ExpG (t • v)) := (hG.map_of_mdifferentiable hH φ hφ (t • v)).symm
    _ = ExpH (j (t • v)) := hcompat _
    _ = ExpH (t • j v) := by rw [map_smul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FaithfulDifferential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A faithful group representation has faithful differential

If two tangent vectors have the same image, their represented one-parameter
subgroups agree. Faithfulness of the representation and uniqueness of the
tangent vector then identify the two vectors. No immersion theorem or global
injectivity of the Lie exponential is required.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem injective_algebra_differential
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →L[ℝ] A)
    (hd : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, A)) (fun g => (ρ g : A)) 1 j) :
    Function.Injective j := by
  intro v w hvw
  apply hExp.eq_of_oneParameter_eq
  intro t
  apply hρ
  rw [hom_exp_eq_algebraExpUnit hExp ρ j hd,
    hom_exp_eq_algebraExpUnit hExp ρ j hd, map_smul, map_smul, hvw]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_IntrinsicAdjointHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Intrinsic adjoint height on a connected triangular Lie group

The actual adjoint action is positive upper triangular because this holds
on exponential basis curves, which generate the connected group. Its
logarithmic diagonal is therefore a continuous character without a global
exponential chart or a faithful group representation.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

theorem adjointMatrixHom_exp_intrinsic {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    adjointMatrixHom b (Exp x) =
      NormedSpace.exp (LinearMap.toMatrix b b (LieAlgebra.ad ℝ _ x)) := by
  let f : (E →L[ℝ] E) →+* Matrix (Fin n) (Fin n) ℝ :=
    (LinearMap.toMatrixAlgEquiv b).toRingHom.comp ContinuousLinearMap.toLinearMapRingHom
  let fL : (E →L[ℝ] E) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    (LinearMap.toMatrix b b).toLinearMap.comp (ContinuousLinearMap.coeLM ℝ)
  let : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ _
  let : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have he := adjointLinearMap_exponential hExp x 1
  simp only [one_smul] at he
  have hm := NormedSpace.map_exp f fL.continuous_of_finiteDimensional
    (groupAdjointOperator (E := E) x)
  change f (adjointLinearMap (E := E) (Exp x)) = _
  rw [he]
  exact hm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_LieIntegrationNaturality
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
attribute [-simp] _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing exponential compatibility from the integration input

Only existence of a smooth homomorphism with the prescribed differential
remains from Lee's integration theorem. The exponential maps and their
compatibility are supplied by the proved integral-curve construction.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {EN N EG G : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace N] [ChartedSpace EN N] [Group N] [LieGroup (𝓘(ℝ, EN)) ⊤ N]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace G] [ChartedSpace EG G] [Group G] [LieGroup (𝓘(ℝ, EG)) ⊤ G]

theorem nilpotentLieIntegrationInput_of_smooth [T2Space G]
    (h : NilpotentSmoothIntegrationInput (EN := EN) (N := N) (EG := EG) (G := G)) :
    NilpotentLieIntegrationInput (EN := EN) (N := N) (EG := EG) (G := G) := by
  intro hN hnil j ExpN ExpG hExpN hExpG
  obtain ⟨ι, hsmooth, hderiv⟩ := h hN hnil j
  refine ⟨ι, hsmooth, hderiv, fun x => ?_⟩
  have heq := hExpN.map_of_mdifferentiable hExpG ι (hsmooth.mdifferentiable (by simp)) x
  rw [hderiv] at heq
  exact heq

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_MinimizingLieMetric
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published minimizing metric on the connected Lie model

The sole input is the connected Lie-group specialization of J. M. Lee,
*Introduction to Riemannian Manifolds*, second edition, GTM 176 (2018):
Lemma 3.10(b), p. 68 constructs a left-invariant Riemannian metric;
Problem 6-12(c), p. 188 gives completeness of homogeneous metrics;
Corollary 6.21, p. 170 gives minimizing segments; Problem 6-14(a), p. 188
(or the compact exponential-ball argument in Lemma 6.18) gives properness.
Only the resulting metric and normalized minimizing paths are retained.
The large-scale chain property is proved here rather than included in the
published hypothesis.
-/

noncomputable section
namespace PolycyclicRecognition

open Set

namespace ProperMinimizingMetric

variable {G : Type*} [Group G] [TopologicalSpace G] (d : ProperMinimizingMetric G)

/-- Sampling minimizing paths provides the chain structure for the existing
proper-homomorphism and canonical-height metric comparisons. -/
def toProperChainMetric : ProperChainMetric G where
  metric := d.metric
  topology_eq := d.topology_eq
  proper := d.proper
  leftInvariant := d.leftInvariant
  chains := by
    let := d.metric
    let := d.leftInvariant
    exact linearMetricChains_of_minimizing_paths d.minimizing

end ProperMinimizingMetric
end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_MovingBaseFlow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact control of graded legs with a moving pivot coordinate -/

noncomputable section
namespace PolycyclicRecognition

open Filter Set
open scoped Topology

variable {n : ℕ}

/-- A rescaled Cartan leg with its moving initial coordinate retained. -/
def basedDynkinFlowMap {c : ℕ} (a : DynkinCoefficients c 2)
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (base v : Fin n → ℝ) : C(ℝ, Fin n → ℝ) :=
  ⟨fun t => dynkinProduct a B base (t • v),
    continuous_dynkinProduct a _ _ _ continuous_const continuous_const
      (continuous_id.smul continuous_const)⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentDerivationFlowDerivative
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial velocity of a nilpotent derivation flow -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

local instance instModuleRat_solutions_2 : Module ℚ L := Module.compHom L (algebraMap ℚ ℝ)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularRealizationInput
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Published realization inputs for bounded-height packing

* J. Dixmier, "L'application exponentielle dans les groupes de Lie résolubles",
  Bull. Soc. Math. France 85 (1957), 113–121, Theorem 3, p.120:
  https://www.numdam.org/item/10.24033/bsmf.1483.pdf
  We retain only the global homeomorphism consequence for real triangular
  adjoint action, for the intrinsic exponential.
* A. Onshuus and S. Post, "A definability criterion for connected Lie groups",
  Bull. London Math. Soc. 54 (2022), 449–465, Proposition 2.4 and its proof:
  https://doi.org/10.1112/blms.12574
  https://arxiv.org/html/1910.11287v2#S2
  We retain a positive triangular realization unipotent on the canonical
  nilpotent Lie ideal. That ideal is the nilradical by the already proved
  `kernelIdeal_nilpotent` and `nilpotent_ideal_le_kernelIdeal`. The published
  Lie isomorphism gives the induced topology. Padding a faithful realization
  with a trivial summand allows a positive matrix size, including dimension zero.

The representation is unipotent on the canonical nilpotent Lie ideal.
The resulting height-kernel realization supplies the algebraic data for
bounded-height packing. Definability is not required.
-/

noncomputable section

namespace PolycyclicRecognition

open PositiveTriangular
open scoped Manifold Matrix.Norms.Operator

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)

/-- The part of the published triangular realization needed by this proof.
Unipotence is required only for exponentials of the actual canonical ideal. -/
def OnshuusPostRealizationInput [SimplyConnectedSpace G] : Prop :=
  ∀ (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G), IsGroupExponential Exp →
    ∃ m : ℕ, 0 < m ∧ ∃ ρ : G →* positiveTriangular m,
      Topology.IsInducing (fun g => matrix (ρ g)) ∧
      ∀ x ∈ T.kernelIdeal, StrictUpper (matrix (ρ (Exp x)) - 1)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RiemannianExponentialInputs
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published regularity inputs needed for Lipschitz replacement

These retain regularity that the earlier topological/metric inputs deliberately
discarded. Dixmier, *Bull. Soc. Math. France* 85 (1957), Theorem 3, p.120,
gives a global exponential diffeomorphism for a simply connected solvable group
with real adjoint roots. Lee, *Introduction to Riemannian Manifolds*, second
edition (2018), Lemma 3.10(b), Problem 6-12(c) and Corollary 6.21 give the
complete left-invariant metric and minimizing paths. Lemmas 2.53–2.54,
especially the length comparison (2.22), give local Lipschitz compatibility
of smooth coordinates and their inverses with that Riemannian distance.

Only smooth (`∞`) regularity is retained; analyticity is not needed by the
application. The second input is precisely this coordinate consequence of the published
length comparison, for the chosen tangent-space coordinates. It assumes no
contraction, interpolation, quasi-isometry or height conclusion.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff
open Module

/-- Only the tangent-space global coordinates used by the application are
retained from the general Riemannian local length comparison. -/
def LieRiemannianMetricInput : Prop :=
  ∀ S : SimplyConnectedSolvableLieModel,
    ∃ d : ProperMinimizingMetric S.carrier,
      letI := d.toProperChainMetric.compatibleMetric
      ∀ (n : ℕ) (φ : (Fin n → ℝ) ≃ₜ S.carrier),
        ContMDiff (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, S.modelSpace)) ∞ φ →
        ContMDiff (𝓘(ℝ, S.modelSpace)) (𝓘(ℝ, Fin n → ℝ)) ∞ φ.symm →
        LocallyLipschitz φ ∧ LocallyLipschitz φ.symm

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_TriangularLieDifferential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The differential of a triangular Lie-group realization

The differential of a continuous injective matrix-group homomorphism
is a Lie algebra homomorphism. Precisely, John M. Lee, *Introduction
to Smooth Manifolds*, second edition, GTM 218 (2013), Problem 20-11(b),
pp.537–538, gives automatic smoothness; Theorem 8.44, p.195, gives the
induced Lie algebra homomorphism; Proposition 8.41, pp.193–195, identifies
the matrix-group Lie algebra with the matrix commutator algebra. Its
injectivity follows from Proposition 7.17, pp.157–158 (see its proof using
Theorem 7.5 and the Global Rank Theorem 4.14(b)).

The input retains only the Lie homomorphism and its equality to the
matrix-valued derivative. Its injectivity is proved using faithful
one-parameter subgroups. The derivative is upper triangular and solvable, and admits a
simultaneous adjoint basis.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] OAI.PolycyclicRecognition.matrixModelChartedSpace
/-- The matrix derivative supplied by the precisely cited Lee results.
No injectivity, triangularity or spectral consequence is assumed. -/
def MatrixLieDifferentialInput : Prop :=
  ∀ (S : SimplyConnectedSolvableLieModel) (n : ℕ)
    (ρ : S.carrier →* Matrix.GeneralLinearGroup (Fin n) ℝ),
    Continuous ρ → Function.Injective ρ →
      ∃ d : GroupLieAlgebra (𝓘(ℝ, S.modelSpace)) S.carrier →ₗ⁅ℝ⁆
          Matrix (Fin n) (Fin n) ℝ,
        HasMFDerivAt (𝓘(ℝ, S.modelSpace))
            (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
            (fun g => (ρ g : Matrix (Fin n) (Fin n) ℝ)) 1
            d.toLinearMap.toContinuousLinearMap

end PolycyclicRecognition

end

end OAI
end


