-- Prove2me | Definitions.Def_Q243FI001
-- name    : Q243FI001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T01:37:32.916715+00:00
-- url     : https://prove2.me/theorems/671a0687-60ff-49b7-8876-65893a7dae71
-- title:
--   Definitions bundle Q243FI001 of the split of OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 407 declarations of OpenAI's Lean: 173 definitions, 3 inductive types or structures, 10 instances and 221 theorems. The definitions and types are `OAI.Problem367.ArtanhMartingaleFormula.firstWeight`, `OAI.Problem367.ArtanhMartingaleFormula.linearSum`, `OAI.Problem367.ArtanhTaylor.remainder`, `OAI.Problem367.BoundedMartingaleVariation.incrementModulus`, `OAI.Problem367.BrownianArrayFiltration.nonnegativeCompensator`, `OAI.Problem367.BrownianArrayFiltration.spatialCompensator`, `OAI.Problem367.BrownianArrayFiltration.spatialSquareDensity`, `OAI.Problem367.BrownianContinuousAssociativity.mixedSum`, `OAI.Problem367.BrownianFiltrationGrid.uniformSumLp`, `OAI.Problem367.BrownianGrid.integralSum`, `OAI.Problem367.BrownianGrid.uniformGrid`, `OAI.Problem367.BrownianGrid.uniformSum`, `OAI.Problem367.BrownianIntegralProcess.globalCompensator`, `OAI.Problem367.BrownianIntegralProcess.stoppedUniformSum`, `OAI.Problem367.ClippedArtanhWeight.clip`, `OAI.Problem367.ClippedArtanhWeight.weight`, `OAI.Problem367.ColoredEdgeLifts.EdgeSpace`, `OAI.Problem367.ColoredEdgeLifts.forwardOperator`, `OAI.Problem367.ColoredEdgeLifts.headLift`, `OAI.Problem367.ColoredEdgeLifts.neighborAverage`, `OAI.Problem367.ColoredEdgeLifts.reversal`, `OAI.Problem367.ColoredEdgeLifts.tailLift`, `OAI.Problem367.ColoredPathAverage.Path`, `OAI.Problem367.ColoredPathAverage.colors`, `OAI.Problem367.ColoredPathAverage.pathValue`, `OAI.Problem367.CompensatorVariation.squaredIncrements`, `OAI.Problem367.ComponentSignalAttenuation.lossCoefficient`, `OAI.Problem367.ContinuousCoefficientModulus.pairModulus`, `OAI.Problem367.ContinuousHorizonGluing.glue`, `OAI.Problem367.ContinuousModification.sampledLimit`, `OAI.Problem367.CopyDifference.operator`, `OAI.Problem367.CopyDifference.pullback`, `OAI.Problem367.CopyDifference.rangeClosure`, `OAI.Problem367.CopyDifference.restrictToRangeClosure`, `OAI.Problem367.CopyDifference.toRangeClosure`, `OAI.Problem367.CriticalEndpointBounds`, `OAI.Problem367.CriticalSpatialEndpointBounds`, `OAI.Problem367.CrossEnergyRiemann.sum`, `OAI.Problem367.CylinderAut.orient`, `OAI.Problem367.CylinderAut.pull` and 136 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `FreeIsing_Brownian_ArrayLaw`, `FreeIsing_Brownian_ArrayMoments`, `FreeIsing_Brownian_ArrayObservation`, `FreeIsing_Brownian_Bridge`, `FreeIsing_Brownian_Characterization`, `FreeIsing_Brownian_ContinuousAssociativity`, `FreeIsing_Brownian_FiltrationIntegral`, `FreeIsing_Brownian_FiltrationUniformIntegral`, `FreeIsing_Brownian_GlobalCompensator`, `FreeIsing_Brownian_GridRefinement`, `FreeIsing_Brownian_IntegralContinuitySupport`, `FreeIsing_Brownian_IntegralProcess`, `FreeIsing_Brownian_LinearCombination`, `FreeIsing_Brownian_Martingale`, `FreeIsing_Brownian_Observation`, `FreeIsing_Brownian_PosteriorField`, `FreeIsing_Brownian_SpatialCompensator`, `FreeIsing_Brownian_SpatialPrimitive`, `FreeIsing_Brownian_UniformGrid`, `FreeIsing_Conditioning_Copies`, `FreeIsing_Conditioning_CopyDifference`, `FreeIsing_Conditioning_CopyInvariance`, `FreeIsing_Conditioning_CovarianceLimit`, `FreeIsing_Conditioning_FamilyConditionalPullback`, `FreeIsing_Conditioning_FiniteBayes`, `FreeIsing_Conditioning_FiniteBayesCondExp`, `FreeIsing_Conditioning_FiniteBayesExp`, `FreeIsing_Conditioning_Fubini`, `FreeIsing_Conditioning_GaussianVector`, `FreeIsing_Conditioning_Naturality`, `FreeIsing_Conditioning_Pullback`, `FreeIsing_Conditioning_ShiftedLoss`, `FreeIsing_Critical_Endgame`, `FreeIsing_Critical_GlobalEndgame`, `FreeIsing_Critical_NoisePathConstants`, `FreeIsing_Energy_CrossEnergyRiemann`, `FreeIsing_Energy_EnergyRiemannApproximation`, `FreeIsing_Energy_FiniteLeafCovariance`, `FreeIsing_Energy_NormalizedResponseLimit`, `FreeIsing_Energy_OptionResponseReindex`, `FreeIsing_Energy_SelectedCriticalFieldMoments`, `FreeIsing_Estimates_ArtanhTaylor`, `FreeIsing_Estimates_ChainMarginals`, `FreeIsing_Estimates_CharacteristicRecurrence`, `FreeIsing_Estimates_ClippedArtanhWeight`, `FreeIsing_Estimates_ComponentPairCount`, `FreeIsing_Estimates_ContinuousCoefficientModulus`, `FreeIsing_Estimates_ContinuousHorizonGluing`, `FreeIsing_Estimates_ContinuousModification`, `FreeIsing_Estimates_CoupledSmallLogLoss`, `FreeIsing_Estimates_CylinderAutomorphism`, `FreeIsing_Estimates_DependentInfinitePiPair`, `FreeIsing_Estimates_ExponentialTaylor`, `FreeIsing_Estimates_FairSpin`, `FreeIsing_Estimates_FiniteCavity`, `FreeIsing_Estimates_FiniteChain`, `FreeIsing_Estimates_FiniteSpinCoupling`, `FreeIsing_Estimates_InhomogeneousSpinChain`, `FreeIsing_Estimates_KernelCompatibility`, `FreeIsing_Estimates_LawUniqueness`, `FreeIsing_Estimates_MeanSquareContinuity`, `FreeIsing_Estimates_MessageFunction`, `FreeIsing_Estimates_NNRealArtanhFormula`, `FreeIsing_Estimates_NonbacktrackingComplement`, `FreeIsing_Estimates_NonbacktrackingDecay`, `FreeIsing_Estimates_NonbacktrackingOperator`, `FreeIsing_Estimates_ObservableDisintegration`, `FreeIsing_Estimates_Osgood`, `FreeIsing_Estimates_PairCorrelation`, `FreeIsing_Estimates_PairedFiniteField`, `FreeIsing_Estimates_PastCompatibility`, `FreeIsing_Estimates_ProgressivePrimitive`, `FreeIsing_Estimates_ProgressivePrimitiveFubini`, `FreeIsing_Estimates_ProgressiveVersionPushforward`, `FreeIsing_Estimates_RadialRepresentation`, `FreeIsing_Estimates_RadialWalk`, `FreeIsing_Estimates_RoundedStoppingTimes`, `FreeIsing_Estimates_TerminalSufficiency`, `FreeIsing_Estimates_WeightedOrbitAverage`, `FreeIsing_Estimates_WeightedPrimitiveApproximation`, `FreeIsing_Factors_Transport`, `FreeIsing_Gaussian_ArrayCharacterization`, `FreeIsing_Gaussian_BinaryFusion`, `FreeIsing_Gaussian_BinaryFusionJointLaw`, `FreeIsing_Gaussian_ComponentSignalAttenuation`, `FreeIsing_Gaussian_FiniteGaussianPlanted`, `FreeIsing_Gaussian_FiniteGaussianPosterior`, `FreeIsing_Gaussian_FiniteSignalInformation`, `FreeIsing_Gaussian_Likelihood`, `FreeIsing_Gaussian_LinearSignalTilt`, `FreeIsing_Gaussian_SideSignalLoss`, `FreeIsing_Gaussian_SmallBall`, `FreeIsing_Gaussian_StatisticSideSignalLoss`, `FreeIsing_Gaussian_TreeCovariance`, `FreeIsing_Gibbs_LeafMessage`, `FreeIsing_Ising_CopyPathBounds`, `FreeIsing_Ising_CriticalSmallLogLoss`, `FreeIsing_Ising_OrientedGaussianTail`, `FreeIsing_Ising_WalkObstruction`, `FreeIsing_Martingales_ArtanhMartingaleFormula`, `FreeIsing_Martingales_BoundedMartingaleVariation`, `FreeIsing_Martingales_CharacteristicStep`, `FreeIsing_Martingales_ContinuousMaximal`, `FreeIsing_Martingales_ContinuousSelection`, `FreeIsing_Martingales_GaussianCriterion`, `FreeIsing_Martingales_InnovationMartingale`, `FreeIsing_Martingales_PredictableMeshApproximation`, `FreeIsing_Martingales_QuadraticVariation`, `FreeIsing_Martingales_SpatialLimit`, `FreeIsing_Martingales_StoppedEnergyRiemann`, `FreeIsing_Martingales_StoppedTimePrimitive`, `FreeIsing_Martingales_StrongMaximal`, `FreeIsing_Posterior_CompensatorStopping`, `FreeIsing_Posterior_FieldCalculus`, `FreeIsing_Posterior_FinitePosterior`, `FreeIsing_Posterior_GaussianEnergy`, `FreeIsing_Posterior_GaussianTimeDerivative`, `FreeIsing_Posterior_InteriorLocalization`, `FreeIsing_Posterior_Limit`, `FreeIsing_Posterior_PathPosteriorResponse`, `FreeIsing_Posterior_PlantedBridge`, `FreeIsing_Posterior_PlantedBridgeInfinite`, `FreeIsing_Posterior_PlantedSymmetry`, `FreeIsing_Posterior_StoppingTimes`, `FreeIsing_Spectral_SpectralClosure`, `FreeIsing_Spins_ObservationFusion`, `FreeIsing_Spins_Recovery`, `FreeIsing_Stochastic_CompensatorVariation`, `FreeIsing_Stochastic_FiniteCoordinateFiltration`, `FreeIsing_Stochastic_IntegralAssociativityLimit`, `FreeIsing_Stochastic_RandomRiemannCompensator`, `FreeIsing_Stochastic_SelectedCompensator`, `FreeIsing_Stochastic_SimpleIntegralAssociativity`, `FreeIsing_Stochastic_SimpleIntegralIsometry`, `FreeIsing_Stochastic_StoppedSimpleIntegral`, `FreeIsing_Trees_ColoredEdgeLifts`, `FreeIsing_Trees_ColoredPathAverage`, `FreeIsing_Trees_InnovationPathMap`, `FreeIsing_Trees_PathCutoff`, `FreeIsing_Trees_PathSideLocality`, `FreeIsing_Trees_PathVariance`, `FreeIsing_Trees_ResponseRowEnergy`, `FreeIsing_Trees_RootedBroadcast`, `FreeIsing_Trees_StemRerootAverage`, `FreeIsing_Trees_WeightedPathSummation`.
--
--   **Imports.** It imports the published bundle `Def_FreeIsing`.
--
--   **Imported by** (directly, in this split): the bundles `Q243FI003` and `Q243FI004`; the statements `OAI.Problem367.BrownianArrayFiltration.compensatedSquare_of_spatial_integral_limits`, `OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_channel_integrals`, `OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_spatial_integral`, `OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_spatial_integral_compensatedSquare`, `OAI.Problem367.BrownianIntegralProcess.exists_global_continuous_uniform_integral`, `OAI.Problem367.ConstructedArtanhFormula.exists_artanh_decomposition`, `OAI.Problem367.LocalizedArtanhFormula.exists_jointExit_artanh_decomposition`, `OAI.Problem367.StoppedRowNormalization.stopped_channel_normalization` and `OAI.Problem367.StoppedRowNormalization.stopped_row_normalization`; the proofs of `OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_channel_integrals`, `OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_spatial_integral`, `OAI.Problem367.BrownianArrayFiltration.exists_global_continuous_spatial_integral_compensatedSquare`, `OAI.Problem367.BrownianIntegralProcess.exists_global_continuous_uniform_integral`, `OAI.Problem367.StoppedRowNormalization.stopped_channel_normalization` and `OAI.Problem367.StoppedRowNormalization.stopped_row_normalization`.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Probability.Process.Stopping
import Definitions.Def_FreeIsing

section
-- module Solutions.Q243_FreeIsing.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
end OAICompat434

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_ArrayLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem iIndepFun_of_gaussianArray_crossCovariance
    {ι Ω T : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ι → T → Ω → ℝ}
    (hG : IsGaussianProcess (fun p : (_ : ι) × T => B p.1 p.2) P)
    (hcross : ∀ i j, i ≠ j → ∀ s t, cov[B i s, B j t; P] = 0) :
    iIndepFun (fun i ω t => B i t ω) P := by
  exact hG.iIndepFun_of_covariance_eq_zero
    (fun i t => hG.aemeasurable ⟨i, t⟩) hcross

theorem iIndepFun_of_measurableEmbedding
    {ι Ω E F : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace F] {P : Measure Ω} {X : ι → Ω → E}
    {e : E → F} (he : MeasurableEmbedding e)
    (h : iIndepFun (fun i => e ∘ X i) P) : iIndepFun X P := by
  rw [iIndepFun_iff_iIndep] at h ⊢
  simpa only [← MeasurableSpace.comap_comp, he.comap_eq] using h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_Martingale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem preBrownian_increment_indep_past {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    IndepFun (fun ω => B t ω - B s ω)
      (fun ω (u : Set.Iic s) => B u ω) P := by
  have h : IndepFun (fun ω => B (s + (t - s)) ω - B s ω)
      (fun ω (u : Set.Iic s) => B u ω) P :=
    (hB.indepFun_shift s).comp (measurable_pi_apply (t - s)) measurable_id
  simpa [Function.comp_def, add_tsub_cancel_of_le hst] using h

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_PastCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace Problem367

lemma setIntegral_independent_future
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {mPast mFuture : MeasurableSpace Ω}
    (hPast : mPast ≤ m) (hFuture : mFuture ≤ m)
    (hIndep : Indep mPast mFuture μ)
    {f : Ω → ℝ} (hf : StronglyMeasurable[mPast] f) (hfint : Integrable f μ)
    {s t : Set Ω} (hs : MeasurableSet[mPast] s) (ht : MeasurableSet[mFuture] t) :
    (∫ x in s ∩ t, f x ∂μ) = μ.real t * ∫ x in s, f x ∂μ := by
  have hce := condExp_indep_eq hPast hFuture (hf.indicator hs) hIndep
  have hit : Integrable (s.indicator f) μ := hfint.indicator (hPast _ hs)
  have hse := setIntegral_condExp hFuture hit ht
  have hcongr := setIntegral_congr_ae (hFuture _ ht)
    (hce.mono (fun x hx _ => hx))
  rw [hse] at hcongr
  rw [setIntegral_indicator (hPast _ hs), integral_indicator (hPast _ hs),
    setIntegral_const, smul_eq_mul, Set.inter_comm] at hcongr
  exact hcongr

lemma measurable_sup_eq_generate_intersections
    {Ω : Type*} (m₁ m₂ : MeasurableSpace Ω) :
    m₁ ⊔ m₂ = MeasurableSpace.generateFrom
      {u | ∃ s t, MeasurableSet[m₁] s ∧ MeasurableSet[m₂] t ∧ u = s ∩ t} := by
  apply le_antisymm
  · apply sup_le
    · intro s hs
      apply MeasurableSpace.measurableSet_generateFrom
      exact ⟨s, Set.univ, hs, MeasurableSet.univ, by simp⟩
    · intro t ht
      apply MeasurableSpace.measurableSet_generateFrom
      exact ⟨Set.univ, t, MeasurableSet.univ, ht, by simp⟩
  · apply MeasurableSpace.generateFrom_le
    rintro u ⟨s, t, hs, ht, rfl⟩
    exact ((show m₁ ≤ m₁ ⊔ m₂ from le_sup_left) s hs).inter
      ((show m₂ ≤ m₁ ⊔ m₂ from le_sup_right) t ht)

lemma isPiSystem_measurable_intersections
    {Ω : Type*} (m₁ m₂ : MeasurableSpace Ω) :
    IsPiSystem {u | ∃ s t, MeasurableSet[m₁] s ∧ MeasurableSet[m₂] t ∧ u = s ∩ t} := by
  rintro u ⟨s, t, hs, ht, rfl⟩ v ⟨s', t', hs', ht', rfl⟩ _
  refine ⟨s ∩ s', t ∩ t', hs.inter hs', ht.inter ht', ?_⟩
  ext x
  simp only [Set.mem_inter_iff]
  tauto

lemma condExp_sup_independent_future
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {mSmall mPast mFuture : MeasurableSpace Ω}
    (hSmall : mSmall ≤ mPast) (hPast : mPast ≤ m) (hFuture : mFuture ≤ m)
    (hIndep : Indep mPast mFuture μ)
    {f : Ω → ℝ} (hf : StronglyMeasurable[mPast] f) (hfint : Integrable f μ) :
    μ[f | mSmall ⊔ mFuture] =ᵐ[μ] μ[f | mSmall] := by
  have hSmallAmbient : mSmall ≤ m := hSmall.trans hPast
  have hJoin : mSmall ⊔ mFuture ≤ m := sup_le hSmallAmbient hFuture
  let g : Ω → ℝ := μ[f | mSmall]
  have hgint : Integrable g μ := integrable_condExp
  have hgsm : StronglyMeasurable[mSmall] g := stronglyMeasurable_condExp
  refine (ae_eq_condExp_of_forall_setIntegral_eq hJoin hfint
    (fun s _ _ => hgint.integrableOn) ?_
    (hgsm.mono (show mSmall ≤ mSmall ⊔ mFuture from le_sup_left)).aestronglyMeasurable).symm
  intro s hs _
  refine MeasurableSpace.induction_on_inter
    (measurable_sup_eq_generate_intersections mSmall mFuture)
    (isPiSystem_measurable_intersections mSmall mFuture) (by simp) ?_ ?_ ?_ s hs
  · rintro u ⟨a, b, ha, hb, rfl⟩
    rw [setIntegral_independent_future hPast hFuture hIndep (hgsm.mono hSmall)
        hgint (hSmall _ ha) hb,
      setIntegral_independent_future hPast hFuture hIndep hf hfint (hSmall _ ha) hb]
    rw [show (∫ x in a, g x ∂μ) = ∫ x in a, f x ∂μ from
      setIntegral_condExp hSmallAmbient hfint ha]
  · intro a ha heq
    rw [setIntegral_compl (hJoin _ ha) hgint, setIntegral_compl (hJoin _ ha) hfint, heq]
    rw [show (∫ x, g x ∂μ) = ∫ x, f x ∂μ from integral_condExp hSmallAmbient]
  · intro a hdisj ha heq
    rw [integral_iUnion (fun i => hJoin _ (ha i)) hdisj hgint.integrableOn,
      integral_iUnion (fun i => hJoin _ (ha i)) hdisj hfint.integrableOn]
    exact tsum_congr heq

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_Fubini
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter

namespace Problem367

theorem integral_of_conditional_versions
    {T Ω : Type*} [mT : MeasurableSpace T] (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (ν : Measure T) (μ : Measure Ω) [SFinite ν] [SFinite μ]
    (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {F G : T × Ω → ℝ}
    (hF : Integrable F (ν.prod μ)) (hG : Integrable G (ν.prod μ))
    (hGm : StronglyMeasurable[@MeasurableSpace.prod T Ω mT m] G)
    (hcond : ∀ᵐ t ∂ν,
      (fun ω => G (t, ω)) =ᵐ[μ] μ[(fun ω => F (t, ω)) | m]) :
    (fun ω => ∫ t, G (t, ω) ∂ν) =ᵐ[μ]
      μ[(fun ω => ∫ t, F (t, ω) ∂ν) | m] := by
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hF.integral_prod_right
  · intro s hs hfin
    exact hG.integral_prod_right.integrableOn
  · intro s hs hfin
    have hFrestrict : Integrable F (ν.prod (μ.restrict s)) :=
      hF.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
    have hGrestrict : Integrable G (ν.prod (μ.restrict s)) :=
      hG.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
    calc
      (∫ ω in s, ∫ t, G (t, ω) ∂ν ∂μ) =
          ∫ t, ∫ ω in s, G (t, ω) ∂μ ∂ν :=
        (integral_integral_swap (f := fun t ω => G (t, ω)) hGrestrict).symm
      _ = ∫ t, ∫ ω in s, F (t, ω) ∂μ ∂ν := by
        apply integral_congr_ae
        filter_upwards [hcond, hF.prod_right_ae] with t ht hFt
        exact (setIntegral_congr_ae (hm s hs) (ht.mono (fun ω hω _ => hω))).trans
          (setIntegral_condExp hm hFt hs)
      _ = ∫ ω in s, ∫ t, F (t, ω) ∂ν ∂μ :=
        integral_integral_swap (f := fun t ω => F (t, ω)) hFrestrict
  · have hgm : StronglyMeasurable[m] (fun ω => ∫ t, G (t, ω) ∂ν) := by
      let : MeasurableSpace Ω := m
      exact hGm.integral_prod_left'
    exact hgm.aestronglyMeasurable

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_InnovationMartingale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

theorem martingale_increment_condExp_subfiltration
    {Ω ι : Type*} [Preorder ι] [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {F G : Filtration ι mΩ}
    {B : ι → Ω → ℝ} (hB : Martingale B G P)
    (hFG : ∀ t, F t ≤ G t) {s t : ι} (hst : s ≤ t) :
    P[B t - B s | F s] =ᵐ[P] fun _ => 0 := by
  have hGB : P[B t - B s | G s] =ᵐ[P] fun _ => 0 := by
    have hsub := condExp_sub (hB.integrable t) (hB.integrable s) (G s)
    filter_upwards [hsub, hB.condExp_ae_eq hst, hB.condExp_ae_eq (le_refl s)] with ω h1 h2 h3
    simpa only [Pi.sub_def, h2, h3, sub_self] using h1
  calc
    P[B t - B s | F s] =ᵐ[P] P[P[B t - B s | G s] | F s] :=
      (condExp_condExp_of_le (hFG s) (G.le s)).symm
    _ =ᵐ[P] P[(fun _ : Ω => (0 : ℝ)) | F s] := condExp_congr_ae hGB
    _ =ᵐ[P] fun _ => 0 := by simp

theorem observation_increment_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ}
    (hB : Martingale B G P) (hFG : ∀ t, F t ≤ G t) (hσ : Integrable σ P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    P[(fun ω => (B t ω + (t : ℝ) * σ ω) - (B s ω + (s : ℝ) * σ ω)) | F s] =ᵐ[P]
      fun ω => ((t : ℝ) - (s : ℝ)) * P[σ | F s] ω := by
  have hfun : (fun ω => (B t ω + (t : ℝ) * σ ω) - (B s ω + (s : ℝ) * σ ω)) =
      (B t - B s) + (((t : ℝ) - (s : ℝ)) • σ) := by
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun]
  have hadd := condExp_add ((hB.integrable t).sub (hB.integrable s))
    (hσ.const_mul ((t : ℝ) - (s : ℝ))) (F s)
  have hscale := condExp_smul (μ := P) ((t : ℝ) - (s : ℝ)) σ (F s)
  have hzero := martingale_increment_condExp_subfiltration hB hFG hst
  filter_upwards [hadd, hscale, hzero] with ω ha hc hz
  simp only [Pi.add_def, Pi.smul_def, smul_eq_mul] at ha hc ⊢
  rw [hc, hz, zero_add] at ha
  exact ha

theorem condExp_nnrealIntervalIntegral_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (F : Filtration ℝ≥0 mΩ) {m : ℝ≥0 → Ω → ℝ} (hm : Martingale m F P)
    {s t : ℝ≥0} (hst : s ≤ t)
    (hInt : Integrable (fun p : ℝ × Ω => m p.1.toNNReal p.2)
      ((volume.restrict (Set.Ioc (s : ℝ) (t : ℝ))).prod P)) :
    P[(fun ω => ∫ u in (s : ℝ)..(t : ℝ), m u.toNNReal ω) | F s] =ᵐ[P]
      fun ω => ((t : ℝ) - (s : ℝ)) * m s ω := by
  let ν : Measure ℝ := volume.restrict (Set.Ioc (s : ℝ) (t : ℝ))
  have hGm : StronglyMeasurable[@MeasurableSpace.prod ℝ Ω inferInstance (F s)]
      (fun p : ℝ × Ω => m s p.2) := by
    let : MeasurableSpace Ω := F s
    exact (hm.stronglyMeasurable s).comp_measurable measurable_snd
  have hcond : ∀ᵐ u ∂ν, (fun ω => m s ω) =ᵐ[P]
      P[(fun ω => m u.toNNReal ω) | F s] := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    apply (hm.condExp_ae_eq ?_).symm
    simpa using Real.toNNReal_mono hu.1.le
  have h := integral_of_conditional_versions (F s) ν P (F.le s)
    hInt ((hm.integrable s).comp_snd ν) hGm hcond
  simpa [ν, Real.volume_real_Ioc_of_le (show (s : ℝ) ≤ (t : ℝ) from hst),
    intervalIntegral.integral_of_le (show (s : ℝ) ≤ (t : ℝ) from hst)] using h.symm

theorem martingale_of_conditional_increment_zero
    {Ω ι : Type*} [Preorder ι] [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι mΩ}
    {W : ι → Ω → ℝ} (had : StronglyAdapted F W) (hint : ∀ t, Integrable (W t) P)
    (hzero : ∀ s t, s ≤ t → P[W t - W s | F s] =ᵐ[P] fun _ => 0) :
    Martingale W F P := by
  refine ⟨had, ?_⟩
  intro s t hst
  have hs : P[W s | F s] = W s := condExp_of_stronglyMeasurable (F.le s) (had s) (hint s)
  have hd := condExp_sub (hint t) (hint s) (F s)
  filter_upwards [hd, hzero s t hst] with ω hd hz
  rw [hs] at hd
  simp only [Pi.sub_apply] at hd
  rw [hz] at hd
  linarith

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_Observation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem naturalFiltration_le_of_stronglyAdapted
    {Ω ι : Type*} [Preorder ι] [mΩ : MeasurableSpace Ω]
    {X : ι → Ω → ℝ} (hm : ∀ t, StronglyMeasurable (X t))
    {G : Filtration ι mΩ} (had : StronglyAdapted G X) :
    Filtration.natural X hm ≤ G := by
  intro t
  change (⨆ s ≤ t, MeasurableSpace.comap (X s) inferInstance) ≤ G t
  exact iSup₂_le fun s hst => ((had s).mono (G.mono hst)).measurable.comap_le

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_Bridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

variable {Omega : Type*} [MeasurableSpace Omega]
  {B : ℝ≥0 → Omega → ℝ} {mu : Measure Omega}

def brownianBridge (B : ℝ≥0 → Omega → ℝ) (T : ℝ≥0)
    (s : ℝ≥0) (w : Omega) : ℝ :=
  B s w - ((s : ℝ) / (T : ℝ)) * B T w

lemma preBrownian_bridge_indep_terminal (hB : IsPreBrownianReal B mu)
    {T : ℝ≥0} (hT : T ≠ 0) :
    IndepFun (fun w (s : Set.Iic T) => brownianBridge B T s w) (B T) mu := by
  classical
  have hind : IndepFun
      (fun w (s : Set.Iic T) => brownianBridge B T s w)
      (fun w (_ : Unit) => B T w) mu := by
    apply IsGaussianProcess.indepFun_of_covariance_eq_zero
    · apply hB.isGaussianProcess.of_isGaussianProcess
      rintro (⟨s, hs⟩ | u)
      · exact ⟨{s, T},
          { toFun x := x ⟨s, by simp⟩ - ((s : ℝ) / (T : ℝ)) * x ⟨T, by simp⟩
            map_add' x y := by simp; ring
            map_smul' c x := by simp; ring }, by simp [brownianBridge]⟩
      · exact ⟨{T},
          { toFun x := x ⟨T, by simp⟩
            map_add' x y := by simp
            map_smul' c x := by simp }, by simp⟩
    · intro s
      exact (hB.aemeasurable s).sub ((hB.aemeasurable T).const_mul _)
    · intro u
      exact hB.aemeasurable T
    · intro s u
      have : IsProbabilityMeasure mu := hB.isGaussianProcess.isProbabilityMeasure
      change cov[fun w => B s w - ((s : ℝ) / (T : ℝ)) * B T w, B T; mu] = 0
      rw [covariance_fun_sub_left, covariance_const_mul_left,
        hB.covariance_eval, hB.covariance_eval, min_eq_left s.property, min_self]
      · have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT
        simp [div_mul_cancel₀ _ hT']
      · exact (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
      · exact (hB.isGaussianProcess.hasGaussianLaw_eval T).memLp_two.const_mul _
      · exact (hB.isGaussianProcess.hasGaussianLaw_eval T).memLp_two
  simpa only [Function.comp_def, id_eq] using
    hind.comp measurable_id (measurable_pi_apply ())

omit [MeasurableSpace Omega]

lemma brownianBridge_add_drift (B : ℝ≥0 → Omega → ℝ) (sigma : Omega → ℝ)
    {T : ℝ≥0} (hT : T ≠ 0) (s : ℝ≥0) (w : Omega) :
    brownianBridge (fun t w => (t : ℝ) * sigma w + B t w) T s w =
      brownianBridge B T s w := by
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT
  simp only [brownianBridge]
  field_simp
  ring

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_PlantedBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

lemma indepFun_prod_left_of_indepFun
    {S Omega E F : Type*} [MeasurableSpace S] [MeasurableSpace Omega]
    [MeasurableSpace E] [MeasurableSpace F]
    (nu : Measure S) (mu : Measure Omega)
    [IsProbabilityMeasure nu] [IsProbabilityMeasure mu]
    {f : Omega → E} {g : Omega → F} (hf : Measurable f) (hg : Measurable g)
    (hfg : IndepFun f g mu) :
    IndepFun (fun q : S × Omega => (q.1, f q.2)) (fun q => g q.2) (nu.prod mu) := by
  have hfirst : (nu.prod mu).map (fun q : S × Omega => (q.1, f q.2)) =
      nu.prod (mu.map f) := by
    calc
      _ = (nu.prod mu).map (Prod.map id f) := by
        congr 1
      _ = _ := by
        simpa only [Measure.map_id] using (Measure.map_prod_map nu mu measurable_id hf).symm
  have hsecond : (nu.prod mu).map (fun q : S × Omega => g q.2) = mu.map g := by
    rw [← Function.comp_def, ← Measure.map_map hg measurable_snd]
    simp
  apply (indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).2
  rw [hfirst, hsecond]
  calc
    _ = ((nu.prod mu).map (Prod.map id (fun w => (f w, g w)))).map
        (MeasurableEquiv.prodAssoc.symm : S × (E × F) ≃ᵐ (S × E) × F) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (nu.prod (mu.map (fun w => (f w, g w)))).map
        (MeasurableEquiv.prodAssoc.symm : S × (E × F) ≃ᵐ (S × E) × F) := by
      rw [← Measure.map_prod_map nu mu measurable_id (hf.prodMk hg), Measure.map_id]
    _ = _ := by
      rw [hfg.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable]
      exact (measurePreserving_prodAssoc nu (mu.map f) (mu.map g)).symm.map_eq

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_PlantedBridgeInfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

lemma indepFun_comp_measurePreserving
    {Omega Omega' E F : Type*} [MeasurableSpace Omega] [MeasurableSpace Omega']
    [MeasurableSpace E] [MeasurableSpace F]
    {mu : Measure Omega} {nu : Measure Omega'}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {r : Omega → Omega'} (hr : MeasurePreserving r mu nu)
    {f : Omega' → E} {g : Omega' → F}
    (hf : Measurable f) (hg : Measurable g) (hfg : IndepFun f g nu) :
    IndepFun (f ∘ r) (g ∘ r) mu := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (hf.comp hr.measurable).aemeasurable (hg.comp hr.measurable).aemeasurable).2
  have h := hfg.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable
  rw [← hr.map_eq] at h
  simpa only [Measure.map_map (hf.prodMk hg) hr.measurable,
    Measure.map_map hf hr.measurable, Measure.map_map hg hr.measurable,
    Function.comp_def] using h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_ArrayObservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

lemma planted_noise_coordinate_measurePreserving
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    MeasurePreserving (fun q : S × (ι → Ω) => q.2 i)
      (ν.prod (Measure.infinitePi μ)) (μ i) := by
  refine ⟨(measurable_pi_apply i).comp measurable_snd, ?_⟩
  change Measure.map ((fun w : ι → Ω => w i) ∘ Prod.snd) _ = _
  rw [← Measure.map_map (measurable_pi_apply i) measurable_snd]
  simp only [Measure.map_snd_prod, measure_univ, one_smul]
  exact Measure.infinitePi_map_eval μ i

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_SimpleIntegralIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Problem367.SimpleIntegral

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_sq_sum_of_orthogonal {ι : Type*} (s : Finset ι)
    (Y : ι → Ω → ℝ)
    (hint : ∀ i ∈ s, ∀ j ∈ s, Integrable (fun ω => Y i ω * Y j ω) μ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∫ ω, Y i ω * Y j ω ∂μ = 0) :
    ∫ ω, (∑ i ∈ s, Y i ω) ^ 2 ∂μ = ∑ i ∈ s, ∫ ω, Y i ω ^ 2 ∂μ := by
  classical
  calc
    ∫ ω, (∑ i ∈ s, Y i ω) ^ 2 ∂μ =
        ∫ ω, ∑ i ∈ s, ∑ j ∈ s, Y i ω * Y j ω ∂μ := by
      congr 1
      funext ω
      simp only [pow_two, Finset.sum_mul_sum]
    _ = ∑ i ∈ s, ∑ j ∈ s, ∫ ω, Y i ω * Y j ω ∂μ := by
      rw [integral_finsetSum s (fun i hi =>
        integrable_finsetSum s (fun j hj => hint i hi j hj))]
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finsetSum s (fun j hj => hint i hi j hj)
    _ = ∑ i ∈ s, ∫ ω, Y i ω ^ 2 ∂μ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_eq_single i]
      · simp only [pow_two]
      · intro j hj hji
        exact horth i hi j hj hji.symm
      · exact fun h => (h hi).elim

end Problem367.SimpleIntegral

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_ArrayMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem planted_coordinate_preBrownian
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i)) (i : ι) :
    IsPreBrownianReal (fun t (q : S × (ι → Ω)) => B i t (q.2 i))
      (ν.prod (Measure.infinitePi μ)) where
  hasLaw I := by
    have (j : ι) : IsProbabilityMeasure (μ j) :=
      (hB j).isGaussianProcess.isProbabilityMeasure
    exact ((hB i).hasLaw I).comp
      (planted_noise_coordinate_measurePreserving ν μ i).hasLaw

theorem planted_coordinate_increments_indep
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t)) (s t : ℝ≥0) {i j : ι} (hij : i ≠ j) :
    IndepFun (fun q : S × (ι → Ω) => B i t (q.2 i) - B i s (q.2 i))
      (fun q : S × (ι → Ω) => B j t (q.2 j) - B j s (q.2 j))
      (ν.prod (Measure.infinitePi μ)) := by
  have (k : ι) : IsProbabilityMeasure (μ k) :=
    (hB k).isGaussianProcess.isProbabilityMeasure
  have hind := (iIndepFun_infinitePi
    (fun k => (hmB k t).sub (hmB k s)) (P := μ)).indepFun hij
  exact indepFun_comp_measurePreserving measurePreserving_snd
    (((hmB i t).sub (hmB i s)).comp (measurable_pi_apply i))
    (((hmB j t).sub (hmB j s)).comp (measurable_pi_apply j)) hind

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_Characterization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.BrownianCharacterization

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem hasIndepIncrements_of_past_events_general
    {T E : Type*} [Preorder T] [MeasurableSpace E] [Sub E] [MeasurableSub₂ E]
    {B : T → Ω → E} (F : Filtration T mΩ) (hB : Adapted F B)
    (hind : ∀ s t : T, s ≤ t → ∀ A : Set Ω, MeasurableSet[F s] A →
      ∀ S : Set E, MeasurableSet S →
        μ (A ∩ (fun ω => B t ω - B s ω) ⁻¹' S) =
          μ A * μ ((fun ω => B t ω - B s ω) ⁻¹' S)) :
    HasIndepIncrements B μ := by
  intro n t ht
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hlt ih =>
    intro hsets
    have ha : a ∉ S := by
      intro ha
      exact lt_irrefl a (hlt a ha)
    have hmsets : ∀ i ∈ S, MeasurableSet (sets i) :=
      fun i hi => hsets i (Finset.mem_insert_of_mem hi)
    have hA : MeasurableSet[F (t a.castSucc)]
        (⋂ i ∈ S, (fun ω => B (t i.succ) ω - B (t i.castSucc) ω) ⁻¹' sets i) := by
      apply S.measurableSet_biInter
      intro i hi
      have hi1 : t i.succ ≤ t a.castSucc := ht (by
        change i.val + 1 ≤ a.val
        exact Nat.succ_le_of_lt (hlt i hi))
      have hi0 : t i.castSucc ≤ t a.castSucc := ht (by
        change i.val ≤ a.val
        exact (hlt i hi).le)
      exact ((hB.measurable_le hi1).sub (hB.measurable_le hi0)) (hmsets i hi)
    have h := hind (t a.castSucc) (t a.succ) (ht (by change a.val ≤ a.val + 1; omega)) _ hA
      (sets a) (hsets a (Finset.mem_insert_self a S))
    rw [Finset.prod_insert ha]
    rw [Finset.set_biInter_insert]
    rw [Set.inter_comm, h, ih hmsets, mul_comm]

theorem hasIndepIncrements_of_past_events
    {B : ℝ≥0 → Ω → ℝ} (F : Filtration ℝ≥0 mΩ)
    (hB : StronglyAdapted F B)
    (hind : ∀ s t : ℝ≥0, s ≤ t → ∀ A : Set Ω, MeasurableSet[F s] A →
      ∀ S : Set ℝ, MeasurableSet S →
        μ (A ∩ (fun ω => B t ω - B s ω) ⁻¹' S) =
          μ A * μ ((fun ω => B t ω - B s ω) ⁻¹' S)) :
    HasIndepIncrements B μ :=
  hasIndepIncrements_of_past_events_general F hB.adapted hind

end Problem367.BrownianCharacterization

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_FiltrationIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.BrownianFiltration

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem increment_indep_of_past
    {s t : ℝ≥0}
    (hind : Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    {H : Ω → ℝ} (hH : StronglyMeasurable[F s] H) :
    IndepFun (fun ω => B t ω - B s ω) H P :=
  indep_of_indep_of_le_right hind hH.measurable.comap_le

theorem predictable_mul_memLp_two
    (hB : IsPreBrownianReal B P) {s t : ℝ≥0}
    (hind : Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    {H : Ω → ℝ} (hH : StronglyMeasurable[F s] H) (hH2 : MemLp H 2 P) :
    MemLp (fun ω => H ω * (B t ω - B s ω)) 2 P := by
  have hD2 : MemLp (fun ω => B t ω - B s ω) 2 P :=
    (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two.sub
      (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have hi := (increment_indep_of_past hind hH).symm
  have hint := (hi.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)).integrable_mul
    hH2.integrable_sq hD2.integrable_sq
  apply (memLp_two_iff_integrable_sq (hH2.aestronglyMeasurable.mul hD2.aestronglyMeasurable)).2
  simpa only [Function.comp_def, Pi.mul_def, mul_pow, id_eq] using hint

end Problem367.BrownianFiltration

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_GridRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.BrownianGrid

def integralSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0)
    (H : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, H i ω * (B (t (i + 1)) ω - B (t i) ω)

end Problem367.BrownianGrid

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_UniformGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.BrownianGrid

def uniformGrid (T : ℝ≥0) (n i : ℕ) : ℝ≥0 := (i : ℝ≥0) * T / (n : ℝ≥0)

@[simp] lemma uniformGrid_zero (T : ℝ≥0) (n : ℕ) : uniformGrid T n 0 = 0 := by
  simp [uniformGrid]

lemma uniformGrid_mono (T : ℝ≥0) (n : ℕ) : Monotone (uniformGrid T n) := by
  intro i j hij
  change (i : ℝ≥0) * T / (n : ℝ≥0) ≤ (j : ℝ≥0) * T / (n : ℝ≥0)
  gcongr

@[simp] lemma uniformGrid_end (T : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    uniformGrid T n n = T := by
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  dsimp [uniformGrid]
  field_simp

def uniformSum {Ω : Type*} (B H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) : Ω → ℝ :=
  integralSum B (uniformGrid T n) (fun i => H (uniformGrid T n i)) n

end Problem367.BrownianGrid

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_MeanSquareContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.MeanSquareContinuity

def discrepancy {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (u : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) : ℝ :=
  ∫ ω, (u s ω - u t ω) ^ 2 ∂P

@[simp] theorem discrepancy_self {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (u : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    discrepancy P u t t = 0 := by simp [discrepancy]

end Problem367.MeanSquareContinuity

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_EnergyRiemannApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators

namespace Problem367.EnergyRiemann

def point (T : ℝ) (n i : ℕ) : ℝ := (i : ℝ) * (T / n)

def sum (f : ℝ → ℝ) (T : ℝ) (n : ℕ) : ℝ :=
  (T / n) * ∑ i ∈ Finset.range n, f (point T n i)

@[simp] theorem point_zero (T : ℝ) (n : ℕ) : point T n 0 = 0 := by simp [point]

def energy {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : ℝ := ∫ ω, (H t ω) ^ 2 ∂P

end Problem367.EnergyRiemann

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_FiltrationUniformIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianFiltrationGrid
open BrownianGrid

theorem integralSum_memLp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (_hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (t i)] (H i))
    (hH2 : ∀ i, MemLp (H i) 2 P) (n : ℕ) :
    MemLp (integralSum B t H n) 2 P := by
  apply memLp_finsetSum
  intro i hi
  exact BrownianFiltration.predictable_mul_memLp_two hB (hind _ _ (ht (Nat.le_succ i))) (hH i) (hH2 i)

theorem uniformSum_memLp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P) (T : ℝ≥0) (n : ℕ) :
    MemLp (uniformSum B H T n) 2 P :=
  integralSum_memLp hB hAd hind (uniformGrid T n) (uniformGrid_mono T n)
    (fun i => H (uniformGrid T n i)) (fun _ => hH _) (fun _ => hH2 _) n

def uniformSumLp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {F : Filtration ℝ≥0 mΩ} (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P) (H : ℝ≥0 → Ω → ℝ)
    (hH : StronglyAdapted (F) H)
    (hH2 : ∀ t, MemLp (H t) 2 P) (T : ℝ≥0) (n : ℕ) : Lp ℝ 2 P :=
  (uniformSum_memLp hB hAd hind H hH hH2 T n).toLp (uniformSum B H T n)

end Problem367.BrownianFiltrationGrid

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_StoppedSimpleIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367.StoppedSimpleIntegral

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [LinearOrder ι]
  {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι mΩ}
  {B : ι → Ω → ℝ}

def intervalSum (B : ι → Ω → ℝ) (H : Ω → ℝ) (a b t : ι) (ω : Ω) : ℝ :=
  H ω * (B (min t b) ω - B (min t a) ω)

end Problem367.StoppedSimpleIntegral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_IntegralProcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianIntegralProcess

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

def stoppedUniformSum (B H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, StoppedSimpleIntegral.intervalSum B
    (H (BrownianGrid.uniformGrid T n i)) (BrownianGrid.uniformGrid T n i)
    (BrownianGrid.uniformGrid T n (i + 1)) t ω

end Problem367.BrownianIntegralProcess

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_IntegralContinuitySupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianIntegralProcess

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

omit [MeasurableSpace Ω] in
@[simp] theorem stoppedUniformSum_zero (B H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) :
    stoppedUniformSum B H T n 0 = 0 := by
  funext ω
  simp [stoppedUniformSum, StoppedSimpleIntegral.intervalSum]

end Problem367.BrownianIntegralProcess

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_PredictableMeshApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.PredictableMesh

def point (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / (n + 1 : ℕ)

def left (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  point n (⌈(n + 1 : ℕ) * t⌉₊ - 1)

@[simp] theorem point_zero (n : ℕ) : point n 0 = 0 := by simp [point]

@[simp] theorem left_zero (n : ℕ) : left n 0 = 0 := by simp [left]

def sample {Ω : Type*} (u : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  u (left n t) ω

end Problem367.PredictableMesh

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_ContinuousMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Problem367.MartingaleSquareMaximal

def dyadicPoint (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / (2 ^ n : ℕ)

end Problem367.MartingaleSquareMaximal

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_ContinuousSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.PredictableMesh

def repair {Ω : Type*} (u : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  limUnder atTop (fun n => sample u n t ω)

end Problem367.PredictableMesh

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_SimpleIntegralAssociativity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.BrownianGrid

theorem memLp_compose_of_bounded
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {H K : Ω → ℝ} (hH : MemLp H 2 P) (hK : AEStronglyMeasurable K P)
    {C : ℝ} (hb : ∀ᵐ ω ∂P, |K ω| ≤ C) :
    MemLp (fun ω => K ω * H ω) 2 P := by
  apply hH.of_le_mul (c := C) (hK.mul hH.aestronglyMeasurable)
  filter_upwards [hb] with ω hω
  simpa only [Real.norm_eq_abs, Pi.mul_apply, abs_mul] using
    mul_le_mul_of_nonneg_right hω (abs_nonneg (H ω))

end Problem367.BrownianGrid

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_IntegralAssociativityLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem367.SimpleIntegral

section Multiplier

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {K : Ω → ℝ} {C : ℝ}

abbrev bounded_mul_memLp (hK : AEStronglyMeasurable K μ)
    (hbound : ∀ᵐ ω ∂μ, |K ω| ≤ C) {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    MemLp (fun ω => K ω * X ω) 2 μ :=
  BrownianGrid.memLp_compose_of_bounded hX hK hbound

end Multiplier

section Limits

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

def coarseTransform (K M : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range n, K j ω * (M (j + 1) ω - M j ω)

end Limits
end Problem367.SimpleIntegral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_ContinuousAssociativity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianContinuousAssociativity

open BrownianGrid BrownianIntegralProcess

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B H K : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

def mixedSum (B H K : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n k : ℕ) : Ω → ℝ :=
  integralSum B (uniformGrid T (n * k))
    (fun i ω => K (uniformGrid T n (i / k)) ω * H (uniformGrid T (n * k) i) ω)
    (n * k)

end Problem367.BrownianContinuousAssociativity

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_RandomRiemannCompensator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace Problem367.RandomRiemann

def partitionSum (f : ℝ → ℝ) (τ : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (τ (i + 1) - τ i) * f (τ i)

def stoppedPoint (T t : ℝ) (n i : ℕ) : ℝ := min t (EnergyRiemann.point T n i)

def stoppedSum (f : ℝ → ℝ) (T t : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    (stoppedPoint T t n (i + 1) - stoppedPoint T t n i) * f (EnergyRiemann.point T n i)

end Problem367.RandomRiemann

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_SelectedCompensator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Problem367.SelectedCompensator

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

def squareSum (H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n,
    ((min t (BrownianGrid.uniformGrid T n (i + 1)) : ℝ) -
      (min t (BrownianGrid.uniformGrid T n i) : ℝ)) *
        (H (BrownianGrid.uniformGrid T n i) ω) ^ 2

def selected (H : ℝ≥0 → Ω → ℝ) (T t : ℝ≥0) (ω : Ω) : ℝ :=
  limUnder atTop (fun n => squareSum H T n t ω)

omit mΩ in
@[simp] theorem selected_zero (H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    selected H T 0 ω = 0 := by
  apply Filter.Tendsto.limUnder_eq
  simp [squareSum]

end Problem367.SelectedCompensator

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_GlobalCompensator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Problem367.BrownianIntegralProcess

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

def globalCompensator (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  SelectedCompensator.selected H t t ω

end Problem367.BrownianIntegralProcess

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_LinearCombination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.BrownianLinearCombination

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ι → ℝ≥0 → Ω → ℝ}

omit [IsProbabilityMeasure μ] in

theorem isGaussianProcess_sum
    (hB : ∀ i, IsGaussianProcess (B i) μ)
    (hind : iIndepFun (fun i ω t => B i t ω) μ) (a : ι → ℝ) :
    IsGaussianProcess (fun t ω => ∑ i, a i * B i t ω) μ := by
  classical
  constructor
  intro I
  let C : ι → Ω → (I → ℝ) := fun i ω t => a i * B i t ω
  have hC (i : ι) : HasGaussianLaw (C i) μ := by
    exact ((hB i).smul (fun _ => a i)).hasGaussianLaw I
  have hCi : iIndepFun C μ := by
    have h := hind.comp (fun i (x : ℝ≥0 → ℝ) (t : I) => a i * x t)
      (fun i => by fun_prop)
    exact h
  have hsum := hCi.hasGaussianLaw_fun_sum hC
  have heq : (fun ω => ∑ i, C i ω) =
      (fun ω => I.restrict (fun t => ∑ i, a i * B i t ω)) := by
    funext ω t
    simp only [Finset.sum_apply, C, Finset.restrict_def]
  rw [heq] at hsum
  exact hsum

omit [Fintype ι] [IsProbabilityMeasure μ] in

theorem covariance_channel_ne
    (hB : ∀ i, IsPreBrownianReal (B i) μ)
    (hind : iIndepFun (fun i ω t => B i t ω) μ)
    {i j : ι} (hij : i ≠ j) (s t : ℝ≥0) :
    cov[B i s, B j t; μ] = 0 := by
  have h := (hind.indepFun hij).comp (measurable_pi_apply s) (measurable_pi_apply t)
  exact h.covariance_eq_zero
    ((hB i).isGaussianProcess.hasGaussianLaw_eval s).memLp_two
    ((hB j).isGaussianProcess.hasGaussianLaw_eval t).memLp_two

omit [IsProbabilityMeasure μ] in
theorem martingale_sum {T : Type*} [Preorder T]
    (F : Filtration T ‹MeasurableSpace Ω›) {M : ι → T → Ω → ℝ}
    (hM : ∀ i, Martingale (M i) F μ) (a : ι → ℝ) :
    Martingale (fun t ω => ∑ i, a i * M i t ω) F μ := by
  classical
  have hsum (s : Finset ι) : Martingale (fun t ω => ∑ i ∈ s, a i * M i t ω) F μ := by
    induction s using Finset.induction_on with
    | empty =>
      have heq : (fun t ω => ∑ i ∈ (∅ : Finset ι), a i * M i t ω) =
          (0 : T → Ω → ℝ) := by funext t ω; simp
      rw [heq]
      exact martingale_zero ℝ F μ
    | @insert i s hi ih =>
      have h := ((hM i).smul (a i)).add ih
      have heq : a i • M i + (fun t ω => ∑ j ∈ s, a j * M j t ω) =
          (fun t ω => ∑ j ∈ insert i s, a j * M j t ω) := by
        funext t ω
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_insert hi]
      rw [heq] at h
      exact h
  exact hsum Finset.univ

end Problem367.BrownianLinearCombination

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_Pullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem setIntegral_comp_measurePreserving
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (e : Ω → Ω')
    (he : MeasurePreserving e μ ν) {f : Ω' → ℝ}
    (hf : AEStronglyMeasurable f ν) {B : Set Ω'} (hB : MeasurableSet B) :
    (∫ ω in e ⁻¹' B, f (e ω) ∂μ) = ∫ ω' in B, f ω' ∂ν := by
  have hres := he.restrict_preimage hB
  have hfm : AEStronglyMeasurable f (Measure.map e (μ.restrict (e ⁻¹' B))) := by
    rw [hres.map_eq]
    exact hf.restrict
  calc
    _ = ∫ ω', f ω' ∂Measure.map e (μ.restrict (e ⁻¹' B)) :=
      (integral_map hres.measurable.aemeasurable hfm).symm
    _ = _ := by rw [hres.map_eq]

theorem condExp_comp_measurePreserving
    {Ω Ω' : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (e : Ω → Ω') (he : MeasurePreserving e μ ν)
    (m : MeasurableSpace Ω') (hm : m ≤ mΩ')
    {f : Ω' → ℝ} (hf : Integrable f ν) :
    μ[f ∘ e | m.comap e] =ᵐ[μ] (ν[f | m]) ∘ e := by
  let : MeasurableSpace Ω' := mΩ'
  have hsource : m.comap e ≤ mΩ :=
    (MeasurableSpace.comap_mono hm).trans he.measurable.comap_le
  have hcompint : Integrable ((ν[f | m]) ∘ e) μ :=
    he.integrable_comp_of_integrable integrable_condExp
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hsource
    (he.integrable_comp_of_integrable hf)
    (fun _ _ _ => hcompint.integrableOn)
  · intro A hA _
    obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
    simp only [Function.comp_apply]
    rw [setIntegral_comp_measurePreserving μ ν e he (f := ν[f | m])
        integrable_condExp.aestronglyMeasurable (hm B hB),
      setIntegral_comp_measurePreserving μ ν e he hf.aestronglyMeasurable (hm B hB),
      setIntegral_condExp hm hf hB]
  · exact (stronglyMeasurable_condExp.comp_measurable
      (Measurable.of_comap_le le_rfl)).aestronglyMeasurable

theorem ae_eq_iff_comp_measurePreserving
    {Ω Ω' C : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace C] [MeasurableEq C]
    (μ : Measure Ω) (ν : Measure Ω') (e : Ω → Ω')
    (he : MeasurePreserving e μ ν) {f g : Ω' → C}
    (hf : Measurable f) (hg : Measurable g) :
    f =ᵐ[ν] g ↔ f ∘ e =ᵐ[μ] g ∘ e := by
  rw [← he.map_eq]
  exact ae_map_iff he.measurable.aemeasurable (measurableSet_eq_fun hf hg)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_FiniteBayes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory

namespace Problem367

theorem finite_observation_law_density
    {A X : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace X] (π : Measure A) (ν : Measure X) (κ : Kernel A X)
    (L : A → X → ℝ≥0∞) (hL : ∀ a, Measurable (L a))
    (hκ : ∀ a, κ a = ν.withDensity (L a)) :
    κ ∘ₘ π = ν.withDensity (fun x => ∑ a, π {a} * L a x) := by
  ext s hs
  rw [Measure.bind_apply hs κ.aemeasurable, withDensity_apply _ hs,
    lintegral_fintype]
  simp_rw [hκ, withDensity_apply _ hs]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [lintegral_const_mul _ (hL a), mul_comm]
  · intro a ha
    exact measurable_const.mul (hL a)

theorem finite_posterior_singletons
    {A X : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [StandardBorelSpace A] [Nonempty A] [MeasurableSpace X]
    (π : Measure A) [IsFiniteMeasure π] (ν : Measure X) [SigmaFinite ν]
    (κ : Kernel A X) [IsFiniteKernel κ]
    (L : A → X → ℝ≥0∞) (hL : ∀ a, Measurable (L a))
    (hκ : ∀ a, κ a = ν.withDensity (L a))
    (hpos : ∀ᵐ x ∂ν, (∑ a, π {a} * L a x) ≠ 0)
    (hfinite : ∀ᵐ x ∂ν, (∑ a, π {a} * L a x) ≠ ∞) :
    ∀ᵐ x ∂κ ∘ₘ π, ∀ a,
      (posterior κ π) x {a} = π {a} * L a x / (∑ b, π {b} * L b x) := by
  let Z : X → ℝ≥0∞ := fun x => ∑ a, π {a} * L a x
  have hZ : Measurable Z := by
    exact Finset.measurable_sum _ (fun a _ => measurable_const.mul (hL a))
  have hdata : κ ∘ₘ π = ν.withDensity Z := finite_observation_law_density π ν κ L hL hκ
  have hRNν (a : A) :
      (κ a).rnDeriv (κ ∘ₘ π) =ᵐ[ν] fun x => L a x / Z x := by
    rw [hdata]
    have hright := Measure.rnDeriv_withDensity_right (κ a) ν hZ.aemeasurable hpos hfinite
    have hleft : (κ a).rnDeriv ν =ᵐ[ν] L a := by
      rw [hκ a]
      exact Measure.rnDeriv_withDensity ν (hL a)
    filter_upwards [hright, hleft] with x hr hl
    rw [hr, hl, div_eq_mul_inv, mul_comm]
  have hRN (a : A) :
      (κ a).rnDeriv (κ ∘ₘ π) =ᵐ[κ ∘ₘ π] fun x => L a x / Z x := by
    have hac : κ ∘ₘ π ≪ ν := by
      rw [hdata]
      exact withDensity_absolutelyContinuous ν Z
    exact hac.ae_eq (hRNν a)
  have hpost := posterior_eq_withDensity_of_countable κ π
  filter_upwards [hpost, ae_all_iff.mpr hRN] with x hx hRNx
  intro a
  rw [hx]
  simp only [withDensity_apply _ (measurableSet_singleton a), lintegral_singleton]
  rw [hRNx a]
  dsimp only [Z]
  simp only [div_eq_mul_inv]
  ac_rfl

theorem finite_posterior_singletons_of_positive
    {A X : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [StandardBorelSpace A] [Nonempty A] [MeasurableSpace X]
    (π : Measure A) [IsProbabilityMeasure π] (ν : Measure X) [SigmaFinite ν]
    (κ : Kernel A X) [IsFiniteKernel κ]
    (L : A → X → ℝ≥0∞) (hL : ∀ a, Measurable (L a))
    (hκ : ∀ a, κ a = ν.withDensity (L a))
    (hpos : ∀ a x, L a x ≠ 0) (hfinite : ∀ a x, L a x ≠ ∞) :
    ∀ᵐ x ∂κ ∘ₘ π, ∀ a,
      (posterior κ π) x {a} = π {a} * L a x / (∑ b, π {b} * L b x) := by
  have hp : ∃ a, π {a} ≠ 0 := by
    by_contra! h
    have hs : (∑ a, π {a}) = 0 := Finset.sum_eq_zero (fun a _ => h a)
    simp at hs
  obtain ⟨a, ha⟩ := hp
  apply finite_posterior_singletons π ν κ L hL hκ
  · apply ae_of_all
    intro x
    apply ne_of_gt
    apply lt_of_lt_of_le (pos_iff_ne_zero.mpr (mul_ne_zero ha (hpos a x)))
    exact Finset.single_le_sum (f := fun b => π {b} * L b x)
      (fun b _ => zero_le) (Finset.mem_univ a)
  · apply ae_of_all
    intro x
    exact ENNReal.sum_ne_top.mpr (fun b _ => ENNReal.mul_ne_top (measure_ne_top π _) (hfinite b x))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_FiniteBayesExp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace Problem367.FiniteBayes

theorem posterior_integral
    {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    [Fintype A] [Nonempty A] [StandardBorelSpace A]
    [MeasurableSingletonClass A]
    (mu : Measure A) [IsProbabilityMeasure mu]
    (kappa : Kernel A X) [IsFiniteKernel kappa]
    (nu : Measure X) [SigmaFinite nu]
    (L : A → X → ℝ) (hL : ∀ a, Measurable (L a))
    (hLpos : ∀ a x, 0 < L a x)
    (hkappa : ∀ a, kappa a = nu.withDensity (fun x => ENNReal.ofReal (L a x)))
    (q : A → ℝ) :
    ∀ᵐ x ∂kappa ∘ₘ mu,
      (∫ a, q a ∂(kappa†mu) x) =
        (∑ a, mu.real {a} * L a x * q a) / (∑ a, mu.real {a} * L a x) := by
  have hpost := finite_posterior_singletons_of_positive mu nu kappa
    (fun a x => ENNReal.ofReal (L a x))
    (fun a => (hL a).ennreal_ofReal) hkappa
    (fun a x => ne_of_gt (ENNReal.ofReal_pos.mpr (hLpos a x)))
    (fun a x => ENNReal.ofReal_ne_top)
  filter_upwards [hpost] with x hx
  have hden : (∑ a, mu {a} * ENNReal.ofReal (L a x)).toReal =
      ∑ a, mu.real {a} * L a x := by
    rw [ENNReal.toReal_sum (fun a _ =>
      ENNReal.mul_ne_top (measure_ne_top mu {a}) ENNReal.ofReal_ne_top)]
    apply Finset.sum_congr rfl
    intro a _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hLpos a x).le]
    rfl
  rw [integral_fintype Integrable.of_finite, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  change ((kappa†mu) x {a}).toReal * q a = _
  rw [hx a, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (hLpos a x).le, hden]
  unfold Measure.real
  ring

theorem posterior_integral_exp
    {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    [Fintype A] [Nonempty A] [StandardBorelSpace A]
    [MeasurableSingletonClass A]
    (mu : Measure A) [IsProbabilityMeasure mu]
    (kappa : Kernel A X) [IsFiniteKernel kappa]
    (nu : Measure X) [SigmaFinite nu]
    (E : A → X → ℝ) (hE : ∀ a, Measurable (E a))
    (c : X → ℝ) (hc : Measurable c) (hcpos : ∀ x, 0 < c x)
    (hkappa : ∀ a, kappa a =
      nu.withDensity (fun x => ENNReal.ofReal (c x * Real.exp (E a x))))
    (q : A → ℝ) :
    ∀ᵐ x ∂kappa ∘ₘ mu,
      (∫ a, q a ∂(kappa†mu) x) =
        (∑ a, mu.real {a} * Real.exp (E a x) * q a) /
          (∑ a, mu.real {a} * Real.exp (E a x)) := by
  have hpost := posterior_integral mu kappa nu
    (fun a x => c x * Real.exp (E a x))
    (fun a => hc.mul (hE a).exp)
    (fun a x => mul_pos (hcpos x) (Real.exp_pos _)) hkappa q
  filter_upwards [hpost] with x hx
  rw [hx]
  have hnum : (∑ a, mu.real {a} * (c x * Real.exp (E a x)) * q a) =
      c x * ∑ a, mu.real {a} * Real.exp (E a x) * q a := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hden : (∑ a, mu.real {a} * (c x * Real.exp (E a x))) =
      c x * ∑ a, mu.real {a} * Real.exp (E a x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hnum, hden, mul_div_mul_left _ _ (ne_of_gt (hcpos x))]

end Problem367.FiniteBayes

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_FiniteBayesCondExp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace Problem367.FiniteBayes

variable {S X : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [StandardBorelSpace S] [Nonempty S] [MeasurableSpace X]

section OriginalSpace

variable {Ω : Type*} [MeasurableSpace Ω]

omit [Fintype S] [MeasurableSingletonClass S] in

theorem condDistrib_eq_posterior_of_joint_law
    (μ : Measure Ω) [IsFiniteMeasure μ] (π : Measure S) [IsFiniteMeasure π]
    (κ : Kernel S X) [IsFiniteKernel κ] (Z : Ω → S) (Y : Ω → X)
    (hZ : Measurable Z) (hY : Measurable Y)
    (hlaw : μ.map (fun ω => (Z ω, Y ω)) = π ⊗ₘ κ) :
    condDistrib Z Y μ = κ†π := by
  rw [condDistrib, posterior]
  congr 1
  rw [← hlaw, Measure.map_map measurable_swap (hZ.prodMk hY)]
  rfl

theorem condExp_state_eq_posterior_integral_of_joint_law
    (μ : Measure Ω) [IsFiniteMeasure μ] (π : Measure S) [IsFiniteMeasure π]
    (κ : Kernel S X) [IsFiniteKernel κ] (Z : Ω → S) (Y : Ω → X)
    (hZ : Measurable Z) (hY : Measurable Y)
    (hlaw : μ.map (fun ω => (Z ω, Y ω)) = π ⊗ₘ κ) (A : S → ℝ) :
    μ[fun ω => A (Z ω) | (inferInstance : MeasurableSpace X).comap Y]
      =ᵐ[μ] fun ω => ∫ s, A s ∂(κ†π) (Y ω) := by
  have hint : Integrable (fun ω => A (Z ω)) μ := by
    apply (integrable_const (∑ s, |A s|)).mono'
    · exact ((measurable_of_finite A).comp hZ).aestronglyMeasurable
    · filter_upwards [] with ω
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (fun s _ => abs_nonneg (A s)) (Finset.mem_univ (Z ω))
  have hc := condExp_ae_eq_integral_condDistrib hY hZ.aemeasurable
    (measurable_of_finite A).stronglyMeasurable hint
  rwa [condDistrib_eq_posterior_of_joint_law μ π κ Z Y hZ hY hlaw] at hc

theorem condExp_state_eq_of_posterior_integral
    (μ : Measure Ω) [IsFiniteMeasure μ] (π : Measure S) [IsFiniteMeasure π]
    (κ : Kernel S X) [IsFiniteKernel κ] (Z : Ω → S) (Y : Ω → X)
    (hZ : Measurable Z) (hY : Measurable Y)
    (hlaw : μ.map (fun ω => (Z ω, Y ω)) = π ⊗ₘ κ)
    (A : S → ℝ) (g : X → ℝ)
    (hpost : (fun x => ∫ s, A s ∂(κ†π) x) =ᵐ[κ ∘ₘ π] g) :
    μ[fun ω => A (Z ω) | (inferInstance : MeasurableSpace X).comap Y]
      =ᵐ[μ] fun ω => g (Y ω) := by
  apply (condExp_state_eq_posterior_integral_of_joint_law μ π κ Z Y hZ hY hlaw A).trans
  have hYlaw : μ.map Y = κ ∘ₘ π := by
    rw [← Measure.snd_map_prodMk hZ, hlaw, Measure.snd_compProd]
  rw [← hYlaw] at hpost
  exact ae_of_ae_map hY.aemeasurable hpost

end OriginalSpace

end Problem367.FiniteBayes

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_Likelihood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Problem367

def gaussianSignalLikelihood (t : ℝ≥0) (s x : ℝ) : ℝ :=
  Real.exp (s * x - (t : ℝ) * s ^ 2 / 2)

theorem gaussianPDFReal_signal (t : ℝ≥0) (s x : ℝ) :
    gaussianPDFReal ((t : ℝ) * s) t x =
      gaussianPDFReal 0 t x * gaussianSignalLikelihood t s x := by
  by_cases ht : t = 0
  · simp [ht]
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  have hexp : -(x - (t : ℝ) * s) ^ 2 / (2 * (t : ℝ)) =
      -(x - 0) ^ 2 / (2 * (t : ℝ)) + (s * x - (t : ℝ) * s ^ 2 / 2) := by
    field_simp
    ring
  simp only [gaussianPDFReal, gaussianSignalLikelihood, hexp, Real.exp_add]
  ring

theorem gaussianPDF_signal (t : ℝ≥0) (s x : ℝ) :
    gaussianPDF ((t : ℝ) * s) t x =
      gaussianPDF 0 t x * ENNReal.ofReal (gaussianSignalLikelihood t s x) := by
  rw [gaussianPDF, gaussianPDFReal_signal, ENNReal.ofReal_mul
    (gaussianPDFReal_nonneg 0 t x)]
  rfl

theorem gaussianReal_signal_withDensity (t : ℝ≥0) (s : ℝ) :
    gaussianReal ((t : ℝ) * s) t =
      (gaussianReal 0 t).withDensity
        (fun x => ENNReal.ofReal (gaussianSignalLikelihood t s x)) := by
  by_cases ht : t = 0
  · simp [ht, gaussianSignalLikelihood, MeasureTheory.dirac_withDensity]
  rw [gaussianReal_of_var_ne_zero _ ht, gaussianReal_of_var_ne_zero _ ht,
    ← withDensity_mul volume (measurable_gaussianPDF 0 t) (by
      unfold gaussianSignalLikelihood
      fun_prop)]
  congr 1
  funext x
  exact gaussianPDF_signal t s x

theorem lintegral_pi_prod_of_measurable
    {I : Type*} [Fintype I] {X : I → Type*}
    [∀ i, MeasurableSpace (X i)]
    (mu : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (mu i)]
    (f : ∀ i, X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi mu) = ∏ i, ∫⁻ x, f i x ∂mu i := by
  classical
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun (i : I) (x : ∀ j, X j) => f i (x i))
      (iIndepFun_pi (μ := mu) (X := f) (fun i => (hf i).aemeasurable))
    (fun i => (hf i).comp (measurable_pi_apply i))]
  apply Finset.prod_congr rfl
  intro i hi
  exact (measurePreserving_eval mu i).lintegral_comp (hf i)

theorem pi_withDensity_of_probability
    {I : Type*} [Fintype I] {X : I → Type*}
    [∀ i, MeasurableSpace (X i)]
    (mu nu : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (mu i)] [∀ i, SigmaFinite (nu i)]
    (f : ∀ i, X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (hnu : ∀ i, nu i = (mu i).withDensity (f i)) :
    Measure.pi nu = (Measure.pi mu).withDensity (fun x => ∏ i, f i (x i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  have hpi : MeasurableSet (Set.pi Set.univ s) := MeasurableSet.pi Set.countable_univ
    (fun i hi => hs i)
  rw [withDensity_apply _ hpi, ← lintegral_indicator hpi]
  have hind : (Set.pi Set.univ s).indicator (fun x => ∏ i, f i (x i)) =
      fun x => ∏ i, (s i).indicator (f i) (x i) := by
    funext x
    by_cases hx : ∀ i, x i ∈ s i
    · have hmem : x ∈ Set.pi Set.univ s := by simpa using hx
      rw [Set.indicator_of_mem hmem]
      exact Finset.prod_congr rfl (fun i hi => (Set.indicator_of_mem (hx i) _).symm)
    · obtain ⟨i, hi⟩ := not_forall.mp hx
      have hmem : x ∉ Set.pi Set.univ s := by simpa using not_forall.mpr ⟨i, hi⟩
      rw [Set.indicator_of_notMem hmem]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [hind, lintegral_pi_prod_of_measurable mu _ (fun i => (hf i).indicator (hs i))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [hnu i, withDensity_apply _ (hs i), lintegral_indicator (hs i)]

def gaussianVectorLikelihood {I : Type*} [Fintype I]
    (t : ℝ≥0) (s x : I → ℝ) : ℝ :=
  Real.exp ((∑ i, s i * x i) - (t : ℝ) / 2 * ∑ i, s i ^ 2)

theorem prod_gaussianSignalLikelihood {I : Type*} [Fintype I]
    (t : ℝ≥0) (s x : I → ℝ) :
    (∏ i, gaussianSignalLikelihood t (s i) (x i)) = gaussianVectorLikelihood t s x := by
  classical
  simp only [gaussianSignalLikelihood, gaussianVectorLikelihood, ← Real.exp_sum]
  congr 1
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.sum_div, ← Finset.mul_sum]
  ring

theorem gaussianPi_signal_withDensity {I : Type*} [Fintype I]
    (t : ℝ≥0) (s : I → ℝ) :
    Measure.pi (fun i => gaussianReal ((t : ℝ) * s i) t) =
      (Measure.pi (fun _ : I => gaussianReal 0 t)).withDensity
        (fun x => ENNReal.ofReal (gaussianVectorLikelihood t s x)) := by
  classical
  calc
    Measure.pi (fun i => gaussianReal ((t : ℝ) * s i) t) =
        (Measure.pi (fun _ : I => gaussianReal 0 t)).withDensity
          (fun x => ∏ i, ENNReal.ofReal (gaussianSignalLikelihood t (s i) (x i))) := by
      exact pi_withDensity_of_probability
        (fun _ : I => gaussianReal 0 t)
        (fun i : I => gaussianReal ((t : ℝ) * s i) t)
        (fun i : I => fun x : ℝ => ENNReal.ofReal (gaussianSignalLikelihood t (s i) x))
        (fun i => by unfold gaussianSignalLikelihood; fun_prop)
        (fun i => gaussianReal_signal_withDensity t (s i))
    _ = _ := by
      apply withDensity_congr_ae
      filter_upwards [] with x
      calc
        (∏ i, ENNReal.ofReal (gaussianSignalLikelihood t (s i) (x i))) =
            ENNReal.ofReal (∏ i, gaussianSignalLikelihood t (s i) (x i)) :=
          (ENNReal.ofReal_prod_of_nonneg (fun i hi => by
            unfold gaussianSignalLikelihood
            positivity)).symm
        _ = ENNReal.ofReal (gaussianVectorLikelihood t s x) :=
          congrArg ENNReal.ofReal (prod_gaussianSignalLikelihood t s x)

theorem gaussianVectorLikelihood_of_sq_eq_one {I : Type*} [Fintype I]
    (t : ℝ≥0) (s x : I → ℝ) (hs : ∀ i, s i ^ 2 = 1) :
    gaussianVectorLikelihood t s x =
      Real.exp ((∑ i, s i * x i) - (t : ℝ) * Fintype.card I / 2) := by
  classical
  unfold gaussianVectorLikelihood
  simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  congr 1
  ring

theorem gaussianPi_spin_withDensity {I : Type*} [Fintype I]
    (t : ℝ≥0) (s : I → ℝ) (hs : ∀ i, s i ^ 2 = 1) :
    Measure.pi (fun i => gaussianReal ((t : ℝ) * s i) t) =
      (Measure.pi (fun _ : I => gaussianReal 0 t)).withDensity
        (fun x => ENNReal.ofReal
          (Real.exp ((∑ i, s i * x i) - (t : ℝ) * Fintype.card I / 2))) := by
  simpa only [gaussianVectorLikelihood_of_sq_eq_one t s _ hs] using
    gaussianPi_signal_withDensity t s

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_FiniteGaussianPosterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

namespace Problem367

def finiteGaussianObservationKernel
    {A I : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype I] (t : ℝ≥0) (s : A → I → ℝ) : Kernel A (I → ℝ) where
  toFun a := Measure.pi (fun i => gaussianReal ((t : ℝ) * s a i) t)
  measurable' := measurable_of_finite _

instance finiteGaussianObservationKernel_isMarkov
    {A I : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype I] (t : ℝ≥0) (s : A → I → ℝ) :
    IsMarkovKernel (finiteGaussianObservationKernel t s) where
  isProbabilityMeasure a := by
    change IsProbabilityMeasure (Measure.pi (fun i => gaussianReal ((t : ℝ) * s a i) t))
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem finiteGaussianObservation_posterior_mean
    {A I : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [StandardBorelSpace A] [Nonempty A] [Fintype I]
    (mu : Measure A) [IsProbabilityMeasure mu]
    (t : ℝ≥0) (s : A → I → ℝ) (hs : ∀ a i, s a i ^ 2 = 1)
    (q : A → ℝ) :
    ∀ᵐ x ∂finiteGaussianObservationKernel t s ∘ₘ mu,
      (∫ a, q a ∂(posterior (finiteGaussianObservationKernel t s) mu) x) =
        (∑ a, mu.real {a} * Real.exp (∑ i, s a i * x i) * q a) /
          (∑ a, mu.real {a} * Real.exp (∑ i, s a i * x i)) := by
  have hlikelihood (a : A) :
      finiteGaussianObservationKernel t s a =
        (Measure.pi (fun _ : I => gaussianReal 0 t)).withDensity
          (fun x => ENNReal.ofReal
            (Real.exp (-((t : ℝ) * Fintype.card I / 2)) *
              Real.exp (∑ i, s a i * x i))) := by
    change Measure.pi (fun i => gaussianReal ((t : ℝ) * s a i) t) = _
    rw [gaussianPi_spin_withDensity t (s a) (hs a)]
    congr 1
    funext x
    rw [sub_eq_add_neg, Real.exp_add, mul_comm]
  exact FiniteBayes.posterior_integral_exp mu (finiteGaussianObservationKernel t s)
    (Measure.pi (fun _ : I => gaussianReal 0 t))
    (fun a x => ∑ i, s a i * x i)
    (fun a => Finset.measurable_sum _
      (fun i _ => measurable_const.mul (measurable_pi_apply i)))
    (fun _ => Real.exp (-((t : ℝ) * Fintype.card I / 2))) measurable_const
    (fun _ => Real.exp_pos _) hlikelihood q

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_FiniteGaussianPlanted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

namespace Problem367

theorem map_planted_eq_compProd
    {A B X : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace X]
    (μ : Measure A) [SFinite μ] (ν : Measure B) [SFinite ν]
    (κ : Kernel A X) [IsSFiniteKernel κ] (F : A → B → X)
    (hF : Measurable (fun z : A × B => F z.1 z.2))
    (hκ : ∀ a, ν.map (F a) = κ a) :
    (μ.prod ν).map (fun z : A × B => (z.1, F z.1 z.2)) = μ ⊗ₘ κ := by
  ext s hs
  rw [Measure.map_apply (measurable_fst.prodMk hF) hs,
    Measure.prod_apply (hs.preimage (measurable_fst.prodMk hF)), Measure.compProd_apply hs]
  apply lintegral_congr
  intro a
  have hFa : Measurable (F a) := hF.comp measurable_prodMk_left
  have hsa : MeasurableSet (Prod.mk a ⁻¹' s) := hs.preimage measurable_prodMk_left
  rw [← hκ a, Measure.map_apply hFa hsa]
  rfl

theorem gaussianPi_map_signal {I : Type*} [Fintype I]
    (t : ℝ≥0) (s : I → ℝ) :
    (Measure.pi (fun _ : I => gaussianReal 0 t)).map
      (fun x i => (t : ℝ) * s i + x i) =
        Measure.pi (fun i => gaussianReal ((t : ℝ) * s i) t) := by
  rw [Measure.pi_map_pi (μ := fun _ : I => gaussianReal 0 t)
    (f := fun i (x : ℝ) => (t : ℝ) * s i + x) (fun i => by fun_prop)]
  congr 1
  funext i
  simpa using (gaussianReal_map_const_add (μ := 0) (v := t) ((t : ℝ) * s i))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_FinitePosterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FinitePosterior

variable {ι : Type*} [Fintype ι]

def weight (energy signal : ι → ℝ) (t : ℝ) (s : ι) : ℝ :=
  Real.exp (energy s + t * signal s)

def partition (energy signal : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ s, weight energy signal t s

def mean (energy signal observable : ι → ℝ) (t : ℝ) : ℝ :=
  (∑ s, observable s * weight energy signal t s) / partition energy signal t

def mass (energy signal : ι → ℝ) (t : ℝ) (s : ι) : ℝ :=
  weight energy signal t s / partition energy signal t

omit [Fintype ι] in
lemma weight_pos (energy signal : ι → ℝ) (t : ℝ) (s : ι) :
    0 < weight energy signal t s := Real.exp_pos _

lemma partition_pos [Nonempty ι] (energy signal : ι → ℝ) (t : ℝ) :
    0 < partition energy signal t := by
  exact Finset.sum_pos (fun s _ => weight_pos energy signal t s) Finset.univ_nonempty

lemma mean_lt [Nonempty ι] (energy signal observable : ι → ℝ) (t c : ℝ)
    (hle : ∀ s, observable s ≤ c) (hlt : ∃ s, observable s < c) :
    mean energy signal observable t < c := by
  apply (div_lt_iff₀ (partition_pos energy signal t)).2
  rw [partition, Finset.mul_sum]
  apply Finset.sum_lt_sum
  · intro s _
    exact mul_le_mul_of_nonneg_right (hle s) (weight_pos energy signal t s).le
  · obtain ⟨s, hs⟩ := hlt
    exact ⟨s, Finset.mem_univ s, mul_lt_mul_of_pos_right hs (weight_pos energy signal t s)⟩

lemma lt_mean [Nonempty ι] (energy signal observable : ι → ℝ) (t c : ℝ)
    (hle : ∀ s, c ≤ observable s) (hlt : ∃ s, c < observable s) :
    c < mean energy signal observable t := by
  apply (lt_div_iff₀ (partition_pos energy signal t)).2
  rw [partition, Finset.mul_sum]
  apply Finset.sum_lt_sum
  · intro s _
    exact mul_le_mul_of_nonneg_right (hle s) (weight_pos energy signal t s).le
  · obtain ⟨s, hs⟩ := hlt
    exact ⟨s, Finset.mem_univ s, mul_lt_mul_of_pos_right hs (weight_pos energy signal t s)⟩

theorem spin_mean_mem_Ioo [Nonempty ι] (energy signal spin : ι → ℝ) (t : ℝ)
    (hspin : ∀ s, spin s = -1 ∨ spin s = 1)
    (hneg : ∃ s, spin s = -1) (hpos : ∃ s, spin s = 1) :
    mean energy signal spin t ∈ Set.Ioo (-1 : ℝ) 1 := by
  constructor
  · apply lt_mean energy signal spin t (-1)
    · intro s
      rcases hspin s with hs | hs <;> simp [hs]
    · obtain ⟨s, hs⟩ := hpos
      exact ⟨s, by simp [hs]⟩
  · apply mean_lt energy signal spin t 1
    · intro s
      rcases hspin s with hs | hs <;> simp [hs]
    · obtain ⟨s, hs⟩ := hneg
      exact ⟨s, by simp [hs]⟩

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_Limit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367

theorem artanh_continuous_at_interior {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) : ContinuousAt Real.artanh x := by
  have hd : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx.2)
  have hp : 0 < (1 + x) / (1 - x) := div_pos (by linarith [hx.1]) (sub_pos.mpr hx.2)
  unfold Real.artanh
  exact ((continuousAt_const.add continuousAt_id).div
    (continuousAt_const.sub continuousAt_id) hd).sqrt.log
      (ne_of_gt (Real.sqrt_pos.2 hp))

theorem posterior_field_limit_of_tanh_bounds
    {u : ℕ → ℝ} {z X K : ℝ} (hu : Tendsto u atTop (𝓝 z))
    (hb : ∀ n, Real.tanh (X - K) ≤ u n ∧ u n ≤ Real.tanh (X + K)) :
    z ∈ Set.Ioo (-1 : ℝ) 1 ∧ |Real.artanh z - X| ≤ K ∧
      Tendsto (fun n => Real.artanh (u n)) atTop (𝓝 (Real.artanh z)) := by
  have hlo : Real.tanh (X - K) ≤ z :=
    ge_of_tendsto hu (Filter.Eventually.of_forall (fun n => (hb n).1))
  have hhi : z ≤ Real.tanh (X + K) :=
    le_of_tendsto hu (Filter.Eventually.of_forall (fun n => (hb n).2))
  have hz : z ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨lt_of_lt_of_le (Real.neg_one_lt_tanh _) hlo,
      lt_of_le_of_lt hhi (Real.tanh_lt_one _)⟩
  refine ⟨hz, ?_, (artanh_continuous_at_interior hz).tendsto.comp hu⟩
  have hleft := Real.artanh_le_artanh (Real.neg_one_lt_tanh (X - K)) hz.2 hlo
  have hright := Real.artanh_le_artanh hz.1 (Real.tanh_lt_one (X + K)) hhi
  rw [Real.artanh_tanh] at hleft hright
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem tendsto_posterior_fields_ae
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ m) (f X : Ω → ℝ) (K : ℝ)
    (hb : ∀ n, ∀ᵐ ω ∂μ,
      Real.tanh (X ω - K) ≤ (μ[f | ℱ n]) ω ∧
        (μ[f | ℱ n]) ω ≤ Real.tanh (X ω + K)) :
    ∀ᵐ ω ∂μ,
      (μ[f | ⨆ n, ℱ n]) ω ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh ((μ[f | ⨆ n, ℱ n]) ω) - X ω| ≤ K ∧
      Tendsto (fun n => Real.artanh ((μ[f | ℱ n]) ω)) atTop
        (𝓝 (Real.artanh ((μ[f | ⨆ n, ℱ n]) ω))) := by
  filter_upwards [tendsto_ae_condExp (μ := μ) (ℱ := ℱ) f,
    ae_all_iff.mpr hb] with ω hlim hbound
  exact posterior_field_limit_of_tanh_bounds hlim hbound

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_Naturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped MeasureTheory

namespace Problem367

theorem condExp_comp_measurePreserving_equiv
    {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {mSmall m : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    (hm : mSmall ≤ m)
    (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ)
    (heSmall : @Measurable Ω Ω mSmall mSmall e.toEquiv)
    (heSymmSmall : @Measurable Ω Ω mSmall mSmall e.toEquiv.symm)
    {f : Ω → E} (hf : Integrable f μ) :
    (μ[f | mSmall]) ∘ e =ᵐ[μ] μ[f ∘ e | mSmall] := by
  have hfc : Integrable (f ∘ e) μ := he.integrable_comp_of_integrable hf
  have hgc : Integrable ((μ[f | mSmall]) ∘ e) μ :=
    he.integrable_comp_of_integrable integrable_condExp
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hfc (fun s _ _ => hgc.integrableOn)
  · intro s hs _
    have hImage : MeasurableSet[mSmall] (e '' s) := by
      rw [e.image_eq_preimage_symm]
      exact heSymmSmall hs
    calc
      (∫ x in s, ((μ[f | mSmall]) ∘ e) x ∂μ) =
          ∫ x in e '' s, (μ[f | mSmall]) x ∂μ :=
        (he.setIntegral_image_emb e.measurableEmbedding _ _).symm
      _ = ∫ x in e '' s, f x ∂μ := setIntegral_condExp hm hf hImage
      _ = ∫ x in s, (f ∘ e) x ∂μ :=
        he.setIntegral_image_emb e.measurableEmbedding _ _
  · exact (stronglyMeasurable_condExp.comp_measurable heSmall).aestronglyMeasurable

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LawUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem measure_eq_of_cofinal_restrict_eq
    {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    {μ ν : Measure (∀ i, α i)} [IsFiniteMeasure μ]
    (C : Finset ι → Prop)
    (hC : ∀ D : Finset ι, ∃ E, D ⊆ E ∧ C E)
    (h : ∀ E : Finset ι, C E → μ.map E.restrict = ν.map E.restrict) :
    μ = ν := by
  apply IsProjectiveLimit.unique (P := fun D : Finset ι => μ.map D.restrict)
  · intro D
    rfl
  · intro D
    obtain ⟨E, hDE, hE⟩ := hC D
    have heq := congrArg (fun ρ => ρ.map (Finset.restrict₂ hDE)) (h E hE)
    rw [Measure.map_map (Finset.measurable_restrict₂ hDE) (Finset.measurable_restrict E),
      Measure.map_map (Finset.measurable_restrict₂ hDE) (Finset.measurable_restrict E)] at heq
    exact heq.symm

theorem map_restrict_eq_of_cylinder_eq
    {ι α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Finite α] [Nonempty α]
    (μ ν : Measure (ι → α)) (D : Finset ι)
    (h : ∀ η : ι → α,
      μ {x | ∀ v ∈ D, x v = η v} = ν {x | ∀ v ∈ D, x v = η v}) :
    μ.map D.restrict = ν.map D.restrict := by
  classical
  apply Measure.ext_of_singleton
  intro η
  let η' : ι → α := fun v => if hv : v ∈ D then η ⟨v, hv⟩ else Classical.choice inferInstance
  have hset : (D.restrict : (ι → α) → (D → α)) ⁻¹' {η} = {x | ∀ v ∈ D, x v = η' v} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · intro hx v hv
      have hv' := congrFun hx ⟨v, hv⟩
      simpa [η', hv, Finset.restrict_def] using hv'
    · intro hx
      funext v
      simpa [η', v.property, Finset.restrict_def] using hx v v.property
  rw [Measure.map_apply (Finset.measurable_restrict D) (measurableSet_singleton η),
    Measure.map_apply (Finset.measurable_restrict D) (measurableSet_singleton η), hset]
  exact h η'

theorem measure_eq_of_cofinal_cylinders
    {ι α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Finite α] [Nonempty α]
    {μ ν : Measure (ι → α)} [IsFiniteMeasure μ]
    (C : Finset ι → Prop)
    (hC : ∀ D : Finset ι, ∃ E, D ⊆ E ∧ C E)
    (h : ∀ E : Finset ι, C E → ∀ η : ι → α,
      μ {x | ∀ v ∈ E, x v = η v} = ν {x | ∀ v ∈ E, x v = η v}) :
    μ = ν := by
  apply measure_eq_of_cofinal_restrict_eq C hC
  intro E hE
  exact map_restrict_eq_of_cylinder_eq μ ν E (h E hE)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Factors_Transport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.FactorTransport

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem map_invariant_of_ae_equivariant
    {μ : Measure α} {a : α → α} {b : β → β} {f : α → β}
    (ha : MeasurePreserving a μ μ) (hb : Measurable b) (hf : Measurable f)
    (heq : ∀ᵐ x ∂μ, f (a x) = b (f x)) :
    Measure.map b (Measure.map f μ) = Measure.map f μ := by
  calc
    Measure.map b (Measure.map f μ) = Measure.map (b ∘ f) μ :=
      Measure.map_map hb hf
    _ = Measure.map (f ∘ a) μ := Measure.map_congr (Filter.EventuallyEq.symm heq)
    _ = Measure.map f (Measure.map a μ) := (Measure.map_map hf ha.measurable).symm
    _ = Measure.map f μ := by rw [ha.map_eq]

end Problem367.FactorTransport

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_PlantedSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.PlantedSymmetry

def gaussianNoiseLaw (ι : Type*) (variance : ℝ≥0) : Measure (ι → ℝ) :=
  Measure.infinitePi (fun _ : ι => gaussianReal 0 variance)

instance gaussianNoiseLaw_probability (ι : Type*) (variance : ℝ≥0) :
    IsProbabilityMeasure (gaussianNoiseLaw ι variance) := by
  unfold gaussianNoiseLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Problem367.PlantedSymmetry

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_MessageFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma artanh_neg_of_mem {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Real.artanh (-x) = -Real.artanh x := by
  have hn : -x ∈ Set.Ioo (-1 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  apply Real.tanh_injective
  rw [Real.tanh_artanh hn, Real.tanh_neg, Real.tanh_artanh hx]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteCavity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem binary_mean_eq_tanh_half_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a - b) / (a + b) = Real.tanh ((Real.log a - Real.log b) / 2) := by
  have hab : 0 < a + b := add_pos ha hb
  have hmem : (a - b) / (a + b) ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · apply (lt_div_iff₀ hab).2
      linarith
    · apply (div_lt_iff₀ hab).2
      linarith
  have hratio : (1 + (a - b) / (a + b)) / (1 - (a - b) / (a + b)) = a / b := by
    apply (div_eq_div_iff (by linarith [hmem.2]) hb.ne').2
    field_simp
    ring
  have hfield : Real.artanh ((a - b) / (a + b)) = (Real.log a - Real.log b) / 2 := by
    rw [Real.artanh_eq_half_log ⟨hmem.1.le, hmem.2.le⟩, hratio,
      Real.log_div ha.ne' hb.ne']
    ring
  rw [← hfield, Real.tanh_artanh hmem]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_PairedFiniteField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

variable {I : Type*} [Fintype I] [Nonempty I]

theorem log_sum_exp_le_of_le_add (E F : I → ℝ) (C : ℝ)
    (h : ∀ i, E i ≤ F i + C) :
    Real.log (∑ i, Real.exp (E i)) ≤ Real.log (∑ i, Real.exp (F i)) + C := by
  have hF : 0 < ∑ i, Real.exp (F i) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hE : 0 < ∑ i, Real.exp (E i) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hsum : (∑ i, Real.exp (E i)) ≤ (∑ i, Real.exp (F i)) * Real.exp C := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (h i))
  have hlog := Real.log_le_log hE hsum
  rwa [Real.log_mul hF.ne' (Real.exp_pos C).ne', Real.log_exp] at hlog

theorem abs_log_sum_exp_sub_le (E F : I → ℝ) (C : ℝ)
    (h : ∀ i, |E i - F i| ≤ C) :
    |Real.log (∑ i, Real.exp (E i)) - Real.log (∑ i, Real.exp (F i))| ≤ C := by
  have hEF := log_sum_exp_le_of_le_add E F C (fun i => by
    have hi := (abs_le.mp (h i)).2
    linarith)
  have hFE := log_sum_exp_le_of_le_add F E C (fun i => by
    have hi := (abs_le.mp (h i)).1
    linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def pairedFieldWeight (E : I → ℝ) (x : ℝ) : ℝ :=
  Real.exp x * ∑ i, Real.exp (E i)

theorem pairedFieldWeight_pos (E : I → ℝ) (x : ℝ) : 0 < pairedFieldWeight E x := by
  exact mul_pos (Real.exp_pos x)
    (Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty)

theorem paired_field_eq (E F : I → ℝ) (x : ℝ) :
    Real.artanh ((pairedFieldWeight E x - pairedFieldWeight F (-x)) /
      (pairedFieldWeight E x + pairedFieldWeight F (-x))) =
      x + (Real.log (∑ i, Real.exp (E i)) - Real.log (∑ i, Real.exp (F i))) / 2 := by
  rw [binary_mean_eq_tanh_half_log (pairedFieldWeight_pos E x)
    (pairedFieldWeight_pos F (-x)), Real.artanh_tanh]
  have hE : (∑ i, Real.exp (E i)) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty)
  have hF : (∑ i, Real.exp (F i)) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty)
  rw [pairedFieldWeight, pairedFieldWeight,
    Real.log_mul (Real.exp_pos x).ne' hE, Real.log_mul (Real.exp_pos (-x)).ne' hF,
    Real.log_exp, Real.log_exp]
  ring

theorem paired_field_difference_bound (E F : I → ℝ) (x K : ℝ)
    (h : ∀ i, |E i - F i| ≤ 2 * K) :
    |Real.artanh ((pairedFieldWeight E x - pairedFieldWeight F (-x)) /
      (pairedFieldWeight E x + pairedFieldWeight F (-x))) - x| ≤ K := by
  rw [paired_field_eq, add_sub_cancel_left, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by
    simpa only [mul_comm K 2] using abs_log_sum_exp_sub_le E F (2 * K) h)

end Problem367

namespace Problem367

theorem finitePosterior_mean_equiv {S R : Type*} [Fintype S] [Fintype R]
    (e : S ≃ R) (energy signal observable : R → ℝ) (x : ℝ) :
    FinitePosterior.mean (energy ∘ e) (signal ∘ e) (observable ∘ e) x =
      FinitePosterior.mean energy signal observable x := by
  unfold FinitePosterior.mean FinitePosterior.partition FinitePosterior.weight
  simp only [Function.comp_apply]
  rw [e.sum_comp (fun s => observable s * Real.exp (energy s + x * signal s)),
    e.sum_comp (fun s => Real.exp (energy s + x * signal s))]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_TerminalSufficiency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace Problem367.TerminalSufficiency

variable {Ω ι : Type*}

theorem condExp_observation_eq_statistic
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (Y : Ω → A) (R : Ω → B) (X : Ω → C)
    (hf : Measurable f) (hY : Measurable Y) (hR : Measurable R)
    (hfint : Integrable f μ)
    (hindep : IndepFun (fun ω => (f ω, Y ω)) R μ)
    (hcomap : MeasurableSpace.comap X inferInstance =
      MeasurableSpace.comap Y inferInstance ⊔ MeasurableSpace.comap R inferInstance) :
    μ[f | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      μ[f | MeasurableSpace.comap Y inferInstance] := by
  rw [hcomap]
  let mPast := MeasurableSpace.comap (fun ω => (f ω, Y ω)) inferInstance
  have hmPair : Measurable[mPast] (fun ω => (f ω, Y ω)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hSmall : MeasurableSpace.comap Y inferInstance ≤ mPast :=
    (measurable_snd.comp hmPair).comap_le
  have hPast : mPast ≤ m := (hf.prodMk hY).comap_le
  have hfm : StronglyMeasurable[mPast] f :=
    (measurable_fst.comp hmPair).stronglyMeasurable
  exact Problem367.condExp_sup_independent_future hSmall hPast hR.comap_le
    hindep hfm hfint

end Problem367.TerminalSufficiency

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_PosteriorField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367

open PlantedSymmetry

theorem condExp_comp_measurePreserving_comap
    {Ω Ξ : Type*} [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {T : Ω → Ξ} (hT : MeasurePreserving T μ ν)
    {f : Ξ → ℝ} (_hf : StronglyMeasurable f) (hfi : Integrable f ν)
    {m : MeasurableSpace Ξ} (hm : m ≤ mΞ) :
    μ[f ∘ T | m.comap T] =ᵐ[μ] (ν[f | m]) ∘ T := by
  let : MeasurableSpace Ξ := mΞ
  exact condExp_comp_measurePreserving μ ν T hT m hm hfi

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_StoppedEnergyRiemann
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators

namespace Problem367.EnergyRiemann

def stoppedSum (f : ℝ → ℝ) (T U : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    (min U (point T n (i + 1)) - min U (point T n i)) * f (point T n i)

end Problem367.EnergyRiemann

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ContinuousHorizonGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.ContinuousHorizonGluing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

def glue (L : ℕ → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  limUnder atTop (fun n => L n t ω)

end Problem367.ContinuousHorizonGluing

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_StrongMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Finset
open scoped NNReal ENNReal Topology

namespace Problem367.MartingaleStrongMaximal

def runningMax (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => x 0
  | n + 1 => max (runningMax x n) (x (n + 1))

@[simp] theorem runningMax_zero (x : ℕ → ℝ) : runningMax x 0 = x 0 := rfl

@[simp] theorem runningMax_succ (x : ℕ → ℝ) (n : ℕ) :
    runningMax x (n + 1) = max (runningMax x n) (x (n + 1)) := rfl

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

def dyadicPoint (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / (2 ^ n : ℕ)

def dyadicCount (n : ℕ) (T : ℝ≥0) : ℕ := ⌊(2 ^ n : ℕ) * T⌋₊

def gridMax (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  runningMax (fun k => |M (dyadicPoint n k) ω|) (dyadicCount n T)

def supremumSq (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ⨆ t : Set.Iic T, ENNReal.ofReal (M t ω ^ 2)

def maximalSquare (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  (supremumSq M T ω).toReal

end Problem367.MartingaleStrongMaximal

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_SpatialLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Finset
open scoped NNReal Topology

namespace Problem367.MartingaleSpatialLimit

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

def finiteSum (M : ι → ℝ≥0 → Ω → ℝ) (s : Finset ι) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ s, M i t ω

end Problem367.MartingaleSpatialLimit

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_SpatialCompensator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Problem367.BrownianArrayFiltration

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ}

def nonnegativeCompensator (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  max (BrownianIntegralProcess.globalCompensator H t ω) 0

def spatialCompensator (H : ι → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑' a, nonnegativeCompensator (H a) t ω

omit mΩ in
@[simp] theorem nonnegativeCompensator_zero (H : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    nonnegativeCompensator H 0 ω = 0 := by
  simp [nonnegativeCompensator, BrownianIntegralProcess.globalCompensator]

end Problem367.BrownianArrayFiltration

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ProgressivePrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem stronglyMeasurable_clipped_nnreal_process
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {F : Filtration ℝ≥0 mΩ}
    {m : ℝ≥0 → Ω → ℝ} (hm : IsStronglyProgressive F m) (t : ℝ≥0) :
    StronglyMeasurable[@MeasurableSpace.prod ℝ Ω inferInstance (F t)]
      (fun p : ℝ × Ω => m (min p.1.toNNReal t) p.2) := by
  let : MeasurableSpace Ω := F t
  let clip : ℝ → Set.Iic t := fun r => ⟨min r.toNNReal t, by exact (min_le_right r.toNNReal t)⟩
  have hc : Measurable clip := by
    dsimp [clip]
    fun_prop
  exact (hm t).comp_measurable ((hc.comp measurable_fst).prodMk measurable_snd)

theorem integrable_nnreal_process_interval_of_progressive_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) (C : ℝ)
    (hbound : ∀ t, ∀ᵐ ω ∂P, |m t ω| ≤ C) (s t : ℝ≥0) :
    Integrable (fun p : ℝ × Ω => m p.1.toNNReal p.2)
      ((volume.restrict (Set.Ioc (s : ℝ) (t : ℝ))).prod P) := by
  let ν : Measure ℝ := volume.restrict (Set.Ioc (s : ℝ) (t : ℝ))
  have hle : @MeasurableSpace.prod ℝ Ω inferInstance (F t) ≤
      @MeasurableSpace.prod ℝ Ω inferInstance mΩ :=
    sup_le_sup le_rfl (MeasurableSpace.comap_mono (F.le t))
  have hcl : StronglyMeasurable (fun p : ℝ × Ω => m (min p.1.toNNReal t) p.2) :=
    (stronglyMeasurable_clipped_nnreal_process hm t).mono hle
  have hb : ∀ᵐ p ∂ν.prod P, ‖m (min p.1.toNNReal t) p.2‖ ≤ C := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hcl.norm.measurable measurable_const)).2
    apply Filter.Eventually.of_forall
    intro r
    simpa only [Real.norm_eq_abs] using hbound (min r.toNNReal t)
  have hi : Integrable (fun p : ℝ × Ω => m (min p.1.toNNReal t) p.2) (ν.prod P) :=
    (integrable_const C).mono' hcl.aestronglyMeasurable hb
  apply hi.congr
  have hmem : ∀ᵐ p ∂ν.prod P, p.1 ∈ Set.Ioc (s : ℝ) (t : ℝ) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [hmem] with p hp
  have hpt : p.1.toNNReal ≤ t := by simpa using Real.toNNReal_mono hp.2
  simp only [min_eq_left hpt]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Brownian_SpatialPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Problem367.BrownianArrayFiltration

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

def spatialSquareDensity (H : ι → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑' a, H a t ω ^ 2

end Problem367.BrownianArrayFiltration

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_Copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

variable {W Ω : Type*} [MeasurableSpace W] [MeasurableSpace Ω]
    (ν : Measure W) [SFinite ν] (κ : Kernel W Ω) [IsMarkovKernel κ]

theorem measurePreserving_conditionalCopy_fst :
    MeasurePreserving (Prod.map id Prod.fst : W × (Ω × Ω) → W × Ω)
      (ν ⊗ₘ (κ ×ₖ κ)) (ν ⊗ₘ κ) := by
  refine ⟨by fun_prop, ?_⟩
  rw [← Measure.compProd_map measurable_fst, ← Kernel.fst_eq, Kernel.fst_prod]

theorem measurePreserving_conditionalCopy_snd :
    MeasurePreserving (Prod.map id Prod.snd : W × (Ω × Ω) → W × Ω)
      (ν ⊗ₘ (κ ×ₖ κ)) (ν ⊗ₘ κ) := by
  refine ⟨by fun_prop, ?_⟩
  rw [← Measure.compProd_map measurable_snd, ← Kernel.snd_eq, Kernel.snd_prod]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_CopyDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem367.CopyDifference

variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

def pullback {μ : Measure A} {ν : Measure B} {p : B → A}
    (hp : MeasurePreserving p ν μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν :=
  (Lp.compMeasurePreservingₗᵢ ℝ p hp).toContinuousLinearMap

@[simp] theorem norm_pullback {μ : Measure A} {ν : Measure B} {p : B → A}
    (hp : MeasurePreserving p ν μ) (f : Lp ℝ 2 μ) :
    ‖pullback hp f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f hp

theorem pullback_comp {μ : Measure A} {ν : Measure B} {ρ : Measure C}
    {p : B → A} {q : C → B}
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ρ ν) :
    pullback (hp.comp hq) = (pullback hq).comp (pullback hp) := by
  ext1 f
  exact Lp.compMeasurePreserving_comp_apply f hp hq

def operator {μ : Measure A} {ν : Measure B} {p q : B → A}
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν := pullback hp - pullback hq

theorem intertwines
    {μ : Measure A} {ν : Measure B} {p q : B → A}
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ)
    {T : A → A} {S : B → B}
    (hT : MeasurePreserving T μ μ) (hS : MeasurePreserving S ν ν)
    (hpT : p ∘ S = T ∘ p) (hqT : q ∘ S = T ∘ q) :
    (pullback hS).comp (operator hp hq) =
      (operator hp hq).comp (pullback hT) := by
  unfold operator
  rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
    ← pullback_comp hp hS, ← pullback_comp hq hS,
    ← pullback_comp hT hp, ← pullback_comp hT hq]
  have congr_pullback {r s : B → A} (hr : MeasurePreserving r ν μ)
      (hs : MeasurePreserving s ν μ) (h : r = s) : pullback hr = pullback hs := by
    subst s
    rfl
  rw [congr_pullback (hp.comp hS) (hT.comp hp) hpT,
    congr_pullback (hq.comp hS) (hT.comp hq) hqT]

section ClosedRange

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def rangeClosure (D : E →L[ℝ] F) : Submodule ℝ F :=
  D.toLinearMap.range.topologicalClosure

instance rangeClosure_completeSpace [CompleteSpace F] (D : E →L[ℝ] F) :
    CompleteSpace (rangeClosure D) := by
  unfold rangeClosure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def toRangeClosure (D : E →L[ℝ] F) : E →L[ℝ] rangeClosure D :=
  D.codRestrict (rangeClosure D) fun x =>
    D.toLinearMap.range.le_topologicalClosure ⟨x, rfl⟩

@[simp] theorem coe_toRangeClosure (D : E →L[ℝ] F) (x : E) :
    (toRangeClosure D x : F) = D x := rfl

theorem mapsTo_rangeClosure (D : E →L[ℝ] F) (A : E →L[ℝ] E) (T : F →L[ℝ] F)
    (h : ∀ x, T (D x) = D (A x)) :
    Set.MapsTo T (rangeClosure D) (rangeClosure D) := by
  have hr : Set.MapsTo T (Set.range D) (Set.range D) := by
    rintro y ⟨x, rfl⟩
    exact ⟨A x, (h x).symm⟩
  exact hr.closure T.continuous

def restrictToRangeClosure (D : E →L[ℝ] F) (A : E →L[ℝ] E) (T : F →L[ℝ] F)
    (h : ∀ x, T (D x) = D (A x)) : rangeClosure D →L[ℝ] rangeClosure D :=
  T.restrict (mapsTo_rangeClosure D A T h)

end ClosedRange

end Problem367.CopyDifference

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_CopyInvariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace Problem367

variable {W X Y : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [MeasurableSpace Y]

lemma map_compProd_prodMap (mu : Measure W) [SFinite mu]
    (kappa : Kernel W X) [IsSFiniteKernel kappa]
    (T : W ≃ᵐ W) {S : X → Y} (hS : Measurable S) :
    (mu ⊗ₘ kappa).map (Prod.map T S) =
      mu.map T ⊗ₘ (kappa.comap T.symm T.symm.measurable).map S := by
  ext A hA
  rw [Measure.map_apply (T.measurable.prodMap hS) hA,
    Measure.compProd_apply ((T.measurable.prodMap hS) hA),
    Measure.compProd_apply hA,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hA) T.measurable]
  apply lintegral_congr
  intro w
  rw [Kernel.map_apply' _ hS _ (measurable_prodMk_left hA), Kernel.comap_apply]
  simp only [MeasurableEquiv.symm_apply_apply]
  rfl

lemma kernel_ae_equivariant_of_joint_invariant
    (mu : Measure W) [IsFiniteMeasure mu]
    (kappa : Kernel W X) [IsFiniteKernel kappa]
    [MeasurableSpace.CountableOrCountablyGenerated W X]
    (T : W ≃ᵐ W) {S : X → X} (hS : Measurable S)
    (hT : MeasurePreserving T mu mu)
    (hjoint : (mu ⊗ₘ kappa).map (Prod.map T S) = mu ⊗ₘ kappa) :
    ∀ᵐ w ∂mu, kappa (T w) = (kappa w).map S := by
  have heq : (kappa.comap T.symm T.symm.measurable).map S =ᵐ[mu] kappa := by
    apply Kernel.ae_eq_of_compProd_eq
    have h := hjoint
    rw [map_compProd_prodMap mu kappa T hS, hT.map_eq] at h
    exact h
  have htrans := hT.quasiMeasurePreserving.ae heq
  filter_upwards [htrans] with w hw
  simpa only [Kernel.map_apply _ hS, Kernel.comap_apply,
    MeasurableEquiv.symm_apply_apply] using hw.symm

lemma joint_invariant_of_kernel_ae_equivariant
    (mu : Measure W) [SFinite mu]
    (kappa : Kernel W X) [IsSFiniteKernel kappa]
    (T : W ≃ᵐ W) {S : X → X} (hS : Measurable S)
    (hT : MeasurePreserving T mu mu)
    (hkappa : ∀ᵐ w ∂mu, kappa (T w) = (kappa w).map S) :
    (mu ⊗ₘ kappa).map (Prod.map T S) = mu ⊗ₘ kappa := by
  rw [map_compProd_prodMap mu kappa T hS, hT.map_eq]
  apply Measure.compProd_congr
  have htrans := hT.symm.quasiMeasurePreserving.ae hkappa
  filter_upwards [htrans] with w hw
  simpa only [Kernel.map_apply _ hS, Kernel.comap_apply,
    MeasurableEquiv.apply_symm_apply] using hw.symm

lemma conditionalCopies_invariant
    (mu : Measure W) [IsFiniteMeasure mu]
    (kappa : Kernel W X) [IsFiniteKernel kappa]
    [MeasurableSpace.CountableOrCountablyGenerated W X]
    (T : W ≃ᵐ W) {S : X → X} (hS : Measurable S)
    (hT : MeasurePreserving T mu mu)
    (hjoint : (mu ⊗ₘ kappa).map (Prod.map T S) = mu ⊗ₘ kappa) :
    (mu ⊗ₘ (kappa ×ₖ kappa)).map (Prod.map T (Prod.map S S)) =
      mu ⊗ₘ (kappa ×ₖ kappa) := by
  apply joint_invariant_of_kernel_ae_equivariant mu (kappa ×ₖ kappa) T
    (hS.prodMap hS) hT
  filter_upwards [kernel_ae_equivariant_of_joint_invariant mu kappa T hS hT hjoint]
    with w hw
  simp only [Kernel.prod_apply, hw]
  exact Measure.map_prod_map (kappa w) (kappa w) hS hS

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_CovarianceLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

def posteriorCovariance (μ : Measure Ω) (m : MeasurableSpace Ω)
    (f g : Ω → ℝ) : Ω → ℝ :=
  fun ω => μ[(fun x => f x * g x) | m] ω - μ[f | m] ω * μ[g | m] ω

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_FamilyConditionalPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem iCondIndepFun_comp_measurePreserving
    {Ω Ω' ι : Type*} {C : ι → Type*}
    [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    [mC : ∀ i, MeasurableSpace (C i)]
    [StandardBorelSpace Ω] [StandardBorelSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (e : Ω → Ω') (he : MeasurePreserving e μ ν)
    (m : MeasurableSpace Ω') (hm : m ≤ mΩ')
    {f : ∀ i, Ω' → C i} (hf : ∀ i, @Measurable Ω' (C i) mΩ' (mC i) (f i))
    (hfamily : iCondIndepFun m hm f ν) :
    iCondIndepFun (m.comap e)
      ((MeasurableSpace.comap_mono hm).trans (@Measurable.comap_le Ω Ω' mΩ mΩ' e
        (@MeasurePreserving.measurable Ω Ω' mΩ mΩ' e μ ν he)))
      (fun i => f i ∘ e) μ := by
  let : MeasurableSpace Ω' := mΩ'
  classical
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul mC (fun i => f i ∘ e)
    (fun i => (hf i).comp he.measurable)]
  intro S sets hsets
  let E : Set Ω' := ⋂ i ∈ S, f i ⁻¹' sets i
  have hE : MeasurableSet E :=
    S.measurableSet_biInter (fun i hi => (hsets i hi).preimage (hf i))
  have hCE := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hE)
  have heach : ∀ᵐ ω ∂μ, ∀ i ∈ S,
      μ[((f i ⁻¹' sets i).indicator (fun _ => (1 : ℝ))) ∘ e | m.comap e] ω =
        ν[(f i ⁻¹' sets i).indicator (fun _ => (1 : ℝ)) | m] (e ω) := by
    apply S.eventually_all.mpr
    intro i hi
    exact condExp_comp_measurePreserving μ ν e he m hm
      ((integrable_const (1 : ℝ)).indicator ((hsets i hi).preimage (hf i)))
  have hmul := he.quasiMeasurePreserving.ae_eq_comp
    ((iCondIndepFun_iff_condExp_inter_preimage_eq_mul mC f hf).mp hfamily S hsets)
  filter_upwards [hCE, heach, hmul] with ω hωE hωeach hωmul
  simp only [Finset.prod_apply, Function.comp_apply] at hωmul ⊢
  have hindicator : (⋂ i ∈ S, (f i ∘ e) ⁻¹' sets i).indicator
      (fun _ => (1 : ℝ)) = (E.indicator (fun _ => (1 : ℝ))) ∘ e := by
    funext x
    simp [E, Set.indicator, Function.comp_def]
  rw [hindicator]
  exact hωE.trans (hωmul.trans (Finset.prod_congr rfl (fun i hi => (hωeach i hi).symm)))

theorem iCondIndepFun_iff_comp_measurePreserving
    {Ω Ω' ι : Type*} {C : ι → Type*}
    [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    [mC : ∀ i, MeasurableSpace (C i)]
    [StandardBorelSpace Ω] [StandardBorelSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (e : Ω → Ω') (he : MeasurePreserving e μ ν)
    (m : MeasurableSpace Ω') (hm : m ≤ mΩ')
    {f : ∀ i, Ω' → C i} (hf : ∀ i, @Measurable Ω' (C i) mΩ' (mC i) (f i)) :
    iCondIndepFun m hm f ν ↔
      iCondIndepFun (m.comap e)
        ((MeasurableSpace.comap_mono hm).trans (@Measurable.comap_le Ω Ω' mΩ mΩ' e
          (@MeasurePreserving.measurable Ω Ω' mΩ mΩ' e μ ν he)))
        (fun i => f i ∘ e) μ := by
  let : MeasurableSpace Ω' := mΩ'
  classical
  refine ⟨iCondIndepFun_comp_measurePreserving μ ν e he m hm hf, ?_⟩
  intro hsource
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul mC f hf]
  intro S sets hsets
  have hmCE (h : Ω' → ℝ) : Measurable (ν[h | m]) :=
    (stronglyMeasurable_condExp.mono hm).measurable
  apply (ae_eq_iff_comp_measurePreserving μ ν e he (hmCE _) ?_).mpr
  swap
  · convert S.measurable_prod (fun i hi =>
      hmCE ((f i ⁻¹' sets i).indicator (fun _ => (1 : ℝ)))) using 1
    all_goals try with_reducible_and_instances rfl
    ext ω'
    simp only [Finset.prod_apply]
  let E : Set Ω' := ⋂ i ∈ S, f i ⁻¹' sets i
  have hE : MeasurableSet E :=
    S.measurableSet_biInter (fun i hi => (hsets i hi).preimage (hf i))
  have hCE := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hE)
  have heach : ∀ᵐ ω ∂μ, ∀ i ∈ S,
      μ[((f i ⁻¹' sets i).indicator (fun _ => (1 : ℝ))) ∘ e | m.comap e] ω =
        ν[(f i ⁻¹' sets i).indicator (fun _ => (1 : ℝ)) | m] (e ω) := by
    apply S.eventually_all.mpr
    intro i hi
    exact condExp_comp_measurePreserving μ ν e he m hm
      ((integrable_const (1 : ℝ)).indicator ((hsets i hi).preimage (hf i)))
  have hmul := (iCondIndepFun_iff_condExp_inter_preimage_eq_mul mC
    (fun i => f i ∘ e) (fun i => (hf i).comp he.measurable)).mp hsource S hsets
  filter_upwards [hCE, heach, hmul] with ω hωE hωeach hωmul
  have hindicator : (⋂ i ∈ S, (f i ∘ e) ⁻¹' sets i).indicator
      (fun _ => (1 : ℝ)) = (E.indicator (fun _ => (1 : ℝ))) ∘ e := by
    funext x
    simp [E, Set.indicator, Function.comp_def]
  rw [hindicator] at hωmul
  simp only [Function.comp_apply, Finset.prod_apply] at hωmul ⊢
  exact hωE.symm.trans (hωmul.trans (Finset.prod_congr rfl (fun i hi => hωeach i hi)))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_GaussianVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

namespace Problem367.ConditionalGaussianVector

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

section FiniteVector

variable {ι : Type*} [Fintype ι]

theorem charFun_product_gaussian (v : ι → ℝ≥0) (t : EuclideanSpace ℝ ι) :
    charFun ((Measure.pi (fun i => gaussianReal 0 (v i))).map (WithLp.toLp 2)) t =
      Complex.exp (-((∑ i, (v i : ℝ) * (t i) ^ 2 : ℝ) : ℂ) / 2) := by
  simp_rw [charFun_pi, charFun_gaussianReal, ← Complex.exp_sum]
  simp [Finset.sum_div, neg_div, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_pow]

end FiniteVector

end Problem367.ConditionalGaussianVector

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_ShiftedLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

def shiftedLossCoefficient (theta beta : ℝ) : ℝ :=
  (1 - theta ^ 2) /
    (Real.cosh (2 * beta + 1) ^ 2 + beta ^ 2 / Real.tanh 1 ^ 2)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_Osgood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Problem367

def osgoodTransform (K x : ℝ) : ℝ := Real.log (1 + Real.log (K / x))

def criticalTimeCoefficient (cutoff C t : ℝ) : ℝ :=
  C * if t ≤ cutoff then
    1 + t ^ (-(3 : ℝ) / 4) + 1 / (t * (Real.log (1 / t)) ^ 2)
  else 1

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Critical_Endgame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem367

structure CriticalEndpointBounds (D Q L Z S V C A B c K t : ℝ) : Prop where
  noise_nonneg : 0 ≤ S
  noise_le : S ≤ C * V
  small_loss : S ≤ A * t ^ ((1 : ℝ) / 4) * V +
    min (A * V) (B * Real.exp (-c * (Real.log (1 / t)) ^ 2))
  quadratic : Q ≤ C * (S * (1 / t + (Real.log (1 + Real.log (K / V))) ^ 2) + V ^ 2)
  linear : L ≤ C * (V * (t ^ (-(3 : ℝ) / 4) + Real.log (1 + Real.log (K / V))) + V ^ 2)
  square_root : Z ≤ C * (Real.sqrt S * (t ^ (-(3 : ℝ) / 4) +
    (Real.log (1 + Real.log (K / V))) ^ ((3 : ℝ) / 2)) + V)
  drift : D ≤ C * (V + Q + L + Real.sqrt V * Z)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

def pathCutoff (C ω I : ℝ) : ℕ := Nat.ceil (C * (ω⁻¹ + Real.log I))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Critical_GlobalEndgame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem367

structure CriticalSpatialEndpointBounds (D Q L Z S V C K ω : ℝ) : Prop where
  noise_nonneg : 0 ≤ S
  noise_le : S ≤ C * V
  quadratic : Q ≤ C * (S * ((ω⁻¹) ^ 2 + (Real.log (1 + Real.log (K / V))) ^ 2) + V ^ 2)
  linear : L ≤ C * (V * (ω⁻¹ + Real.log (1 + Real.log (K / V))) + V ^ 2)
  square_root : Z ≤ C * (Real.sqrt S * (ω⁻¹ * Real.sqrt (ω⁻¹) +
    (Real.log (1 + Real.log (K / V))) ^ ((3 : ℝ) / 2)) + V)
  drift : D ≤ C * (V + Q + L + Real.sqrt V * Z)

def criticalLateCoefficient (C H ε : ℝ) : ℝ :=
  C ^ 2 * (9 * C + 3 * H + 3) *
    (C * (ε⁻¹) ^ 2 + 1 + ε⁻¹ * Real.sqrt (ε⁻¹))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ComponentPairCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

def componentPairWeight {d : ℕ} (r : ℝ) : List (Fin d) → List (Fin d) → ℝ
  | [], v => r ^ v.length
  | _ :: u, [] => r ^ (u.length + 1)
  | a :: u, b :: v =>
      if a = b then r * componentPairWeight r u v else r ^ (u.length + v.length + 2)

def componentWordDistance {α : Type*} [DecidableEq α] : List α → List α → ℕ
  | [], v => v.length
  | _ :: u, [] => u.length + 1
  | a :: u, b :: v =>
      if a = b then componentWordDistance u v else u.length + v.length + 2

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_CylinderAutomorphism
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

noncomputable section

open Relation

variable {d : ℕ}

theorem ConnectedFinset.image {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (g : TreeAut d) :
    ConnectedFinset (D.image g.toEquiv) := by
  classical
  refine ⟨hD.1.image _, ?_⟩
  intro u hu v hv
  obtain ⟨u, huD, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨v, hvD, rfl⟩ := Finset.mem_image.mp hv
  exact ReflTransGen.lift g.toEquiv
    (fun x y hxy => ⟨Finset.mem_image.mpr ⟨x, hxy.1, rfl⟩,
      Finset.mem_image.mpr ⟨y, hxy.2.1, rfl⟩,
      (g.map_adj x y).mpr hxy.2.2⟩) _ _ (hD.2 u huD v hvD)

namespace CylinderAut

theorem adj_symm {u v : TreeVertex d} (h : treeAdj u v) : treeAdj v u :=
  h.symm

theorem length_ne_of_adj {u v : TreeVertex d} (h : treeAdj u v) :
    u.1.length ≠ v.1.length := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  all_goals
    have hlen := congrArg List.length hc
    simp only [List.length_append, List.length_singleton] at hlen
    omega

def orient (e : TreeVertex d × TreeVertex d) : TreeVertex d × TreeVertex d :=
  if e.1.1.length < e.2.1.length then e else e.swap

theorem mem_inducedEdges {D : Finset (TreeVertex d)}
    {e : TreeVertex d × TreeVertex d} :
    e ∈ inducedEdges D ↔ e.1 ∈ D ∧ e.2 ∈ D ∧ treeAdj e.1 e.2 ∧
      e.1.1.length < e.2.1.length := by
  classical
  simp [inducedEdges, and_assoc]

theorem orient_mem {D : Finset (TreeVertex d)}
    {e : TreeVertex d × TreeVertex d} (h₁ : e.1 ∈ D) (h₂ : e.2 ∈ D)
    (ha : treeAdj e.1 e.2) : orient e ∈ inducedEdges D := by
  classical
  unfold orient
  split_ifs with h
  · exact mem_inducedEdges.mpr ⟨h₁, h₂, ha, h⟩
  · exact mem_inducedEdges.mpr ⟨h₂, h₁, adj_symm ha,
      lt_of_le_of_ne (le_of_not_gt h) (length_ne_of_adj ha).symm⟩

def push (g : TreeAut d) (e : TreeVertex d × TreeVertex d) :
    TreeVertex d × TreeVertex d :=
  orient (g.toEquiv e.1, g.toEquiv e.2)

def pull (g : TreeAut d) (e : TreeVertex d × TreeVertex d) :
    TreeVertex d × TreeVertex d :=
  orient (g.toEquiv.symm e.1, g.toEquiv.symm e.2)

theorem push_mem (g : TreeAut d) {D : Finset (TreeVertex d)}
    {e : TreeVertex d × TreeVertex d} (he : e ∈ inducedEdges D) :
    push g e ∈ inducedEdges (D.image g.toEquiv) := by
  classical
  obtain ⟨h₁, h₂, ha, _⟩ := mem_inducedEdges.mp he
  exact orient_mem (Finset.mem_image.mpr ⟨e.1, h₁, rfl⟩)
    (Finset.mem_image.mpr ⟨e.2, h₂, rfl⟩) ((g.map_adj _ _).mpr ha)

theorem pull_push (g : TreeAut d) {D : Finset (TreeVertex d)}
    {e : TreeVertex d × TreeVertex d} (he : e ∈ inducedEdges D) :
    pull g (push g e) = e := by
  have hedir := (mem_inducedEdges.mp he).2.2.2
  unfold push pull orient
  by_cases h : (g.toEquiv e.1).1.length < (g.toEquiv e.2).1.length
  all_goals simp [h, hedir, not_lt_of_ge (le_of_lt hedir)]

theorem pull_mem (g : TreeAut d) {D : Finset (TreeVertex d)}
    {e : TreeVertex d × TreeVertex d} (he : e ∈ inducedEdges (D.image g.toEquiv)) :
    pull g e ∈ inducedEdges D := by
  classical
  obtain ⟨h₁, h₂, ha, _⟩ := mem_inducedEdges.mp he
  have hp₁ : g.toEquiv.symm e.1 ∈ D := by
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp h₁
    simpa [← hxe] using hx
  have hp₂ : g.toEquiv.symm e.2 ∈ D := by
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp h₂
    simpa [← hxe] using hx
  have hpa : treeAdj (g.toEquiv.symm e.1) (g.toEquiv.symm e.2) := by
    apply (g.map_adj _ _).mp
    simpa using ha
  exact orient_mem hp₁ hp₂ hpa

theorem push_pull (g : TreeAut d) {D : Finset (TreeVertex d)}
    {e : TreeVertex d × TreeVertex d} (he : e ∈ inducedEdges (D.image g.toEquiv)) :
    push g (pull g e) = e := by
  have hedir := (mem_inducedEdges.mp he).2.2.2
  unfold push pull orient
  by_cases h : (g.toEquiv.symm e.1).1.length < (g.toEquiv.symm e.2).1.length
  all_goals simp [h, hedir, not_lt_of_ge (le_of_lt hedir)]

theorem prod_inducedEdges_image {M : Type*} [CommMonoid M]
    (g : TreeAut d) (D : Finset (TreeVertex d))
    (f : TreeVertex d → TreeVertex d → M)
    (hf : ∀ u v, f u v = f v u) :
    (∏ e ∈ inducedEdges (D.image g.toEquiv),
      f (g.toEquiv.symm e.1) (g.toEquiv.symm e.2)) =
      ∏ e ∈ inducedEdges D, f e.1 e.2 := by
  classical
  symm
  apply Finset.prod_bij (fun e _ => push g e)
  · intro e he
    exact push_mem g he
  · intro e₁ he₁ e₂ he₂ heq
    have h := congrArg (pull g) heq
    simpa only [pull_push g he₁, pull_push g he₂] using h
  · intro e he
    exact ⟨pull g e, pull_mem g he, push_pull g he⟩
  · intro e he
    unfold push orient
    split_ifs
    · simp
    · simpa using hf e.1 e.2

end CylinderAut

theorem freeCylinderWeight_image_relabel (g : TreeAut d) (theta : ℝ)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight theta (D.image g.toEquiv) (relabel g eta) =
      freeCylinderWeight theta D eta := by
  classical
  unfold freeCylinderWeight
  apply congrArg ENNReal.ofReal
  apply congrArg ((1 / 2 : ℝ) * ·)
  exact CylinderAut.prod_inducedEdges_image g D
    (fun u v => (1 + (if eta u = eta v then theta else -theta)) / 2)
    (by intro u v; simp only [eq_comm])

def cylinderInverseAut (g : TreeAut d) : TreeAut d where
  toEquiv := g.toEquiv.symm
  map_adj := by
    intro u v
    simpa using (g.map_adj (g.toEquiv.symm u) (g.toEquiv.symm v)).symm

theorem measurable_spin_cylinder (D : Finset (TreeVertex d))
    (eta : TreeVertex d → IsingSpin) :
    MeasurableSet {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} := by
  have hsingle (s : IsingSpin) : MeasurableSet ({s} : Set IsingSpin) := by
    trivial
  convert D.measurableSet_biInter
    (fun v _ => (measurable_pi_apply v) (hsingle (eta v))) using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp

theorem HasFreeIsingLaw.map_relabel {theta : ℝ}
    {mu : MeasureTheory.Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (g : TreeAut d) :
    HasFreeIsingLaw theta (MeasureTheory.Measure.map (relabel g) mu) := by
  classical
  intro D hD eta
  have hm : Measurable (relabel g : (TreeVertex d → IsingSpin) → _) :=
    measurable_pi_iff.mpr (fun v => measurable_pi_apply (g.toEquiv.symm v))
  rw [MeasureTheory.Measure.map_apply hm (measurable_spin_cylinder D eta)]
  let gi := cylinderInverseAut g
  have hpre : relabel g ⁻¹' {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} =
      {x : TreeVertex d → IsingSpin | ∀ v ∈ D.image gi.toEquiv,
        x v = relabel gi eta v} := by
    ext x
    constructor
    · intro hx v hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      simpa [relabel, gi, cylinderInverseAut] using hx u hu
    · intro hx v hv
      have hh := hx (gi.toEquiv v) (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
      simpa [relabel, gi, cylinderInverseAut] using hh
  rw [hpre, hmu _ (hD.image gi), freeCylinderWeight_image_relabel]

end
end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367.FiniteChain

variable {A : Type*}

def weight (K : A → A → ℝ) : (n : ℕ) → A → (Fin n → A) → ℝ
  | 0, _, _ => 1
  | n + 1, a, x => K a (x 0) * weight K n (x 0) (Fin.tail x)

def endpoint : (n : ℕ) → A → (Fin n → A) → A
  | 0, a, _ => a
  | n + 1, _, x => endpoint n (x 0) (Fin.tail x)

@[simp] theorem weight_zero (K : A → A → ℝ) (a : A) (x : Fin 0 → A) :
    weight K 0 a x = 1 := rfl

@[simp] theorem endpoint_zero (a : A) (x : Fin 0 → A) :
    endpoint 0 a x = a := rfl

@[simp] theorem weight_cons (K : A → A → ℝ) (n : ℕ) (a b : A) (x : Fin n → A) :
    weight K (n + 1) a (Fin.cons b x) = K a b * weight K n b x := by
  simp [weight]

@[simp] theorem endpoint_cons (n : ℕ) (a b : A) (x : Fin n → A) :
    endpoint (n + 1) a (Fin.cons b x) = endpoint n b x := by
  simp [endpoint]

variable [Fintype A]

def expectation (K : A → A → ℝ) (n : ℕ) (f : A → ℝ) (a : A) : ℝ :=
  ∑ x : Fin n → A, weight K n a x * f (endpoint n a x)

@[simp] theorem expectation_zero (K : A → A → ℝ) (f : A → ℝ) (a : A) :
    expectation K 0 f a = f a := by
  simp [expectation]

end Problem367.FiniteChain

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_PairCorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367

def reducedWordDistance {α : Type*} [DecidableEq α] : List α → List α → ℕ
  | [], v => v.length
  | u, [] => u.length
  | a :: u, b :: v => if a = b then reducedWordDistance u v else u.length + v.length + 2

@[simp] theorem reducedWordDistance_nil_left {α : Type*} [DecidableEq α] (v : List α) :
    reducedWordDistance [] v = v.length := rfl

@[simp] theorem reducedWordDistance_nil_right {α : Type*} [DecidableEq α] (u : List α) :
    reducedWordDistance u [] = u.length := by cases u <;> rfl

@[simp] theorem reducedWordDistance_cons_same {α : Type*} [DecidableEq α]
    (a : α) (u v : List α) :
    reducedWordDistance (a::u) (a::v) = reducedWordDistance u v := by
  simp [reducedWordDistance]

@[simp] theorem reducedWordDistance_self {α : Type*} [DecidableEq α] (u : List α) :
    reducedWordDistance u u = 0 := by
  induction u with
  | nil => rfl
  | cons a u ih => simpa using ih

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_LinearSignalTilt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

def linearSignalTilt {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (q : Ω → ℝ) (a : ℝ) : Measure Ω :=
  mu.withDensity (fun x => ENNReal.ofReal (1 + a * q x))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_SideSignalLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def sideSignalLossCoefficient (theta : ℝ) : ℝ :=
  shiftedLossCoefficient theta (Real.artanh theta) * (1 - theta ^ 2) * theta ^ 2

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_StatisticSideSignalLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

def statisticMessage (theta q : ℝ) : ℝ := Real.artanh (theta * q)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_ComponentSignalAttenuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem367.ComponentSignalAttenuation

open PlantedSymmetry

def lossCoefficient (theta : ℝ) : ℝ := min (sideSignalLossCoefficient theta / 5) (1 / 2)

end Problem367.ComponentSignalAttenuation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Critical_NoisePathConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem367

def criticalNoiseEta (d : ℕ) (beta : ℝ) : ℝ :=
  min (ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) / 4)
    (Real.log ((d : ℝ) - 1) / 8)

def criticalNoiseLengthConstant (beta : ℝ) : ℝ :=
  max 8 (32 * Real.log 2 / ComponentSignalAttenuation.lossCoefficient (Real.tanh beta))

def criticalNoiseTailBase (d : ℕ) : ℝ := ((d : ℝ) - 1) ^ (1 / 16 : ℝ)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_CrossEnergyRiemann
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators

namespace Problem367.CrossEnergyRiemann

open EnergyRiemann

def sum (f : ℝ → ℝ → ℝ) (T : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    ∫ r in point T n i..point T n (i + 1), f (point T n i) r

end Problem367.CrossEnergyRiemann

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_FiniteLeafCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.LeafGibbs

def expectation {A : Type*} [Fintype A] (E f : A → ℝ) : ℝ :=
  (∑ a, f a * Real.exp (E a)) / ∑ a, Real.exp (E a)

def covariance {A : Type*} [Fintype A] (E f g : A → ℝ) : ℝ :=
  expectation E (fun a => f a * g a) - expectation E f * expectation E g

end Problem367.LeafGibbs

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_NormalizedResponseLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

def posteriorResponse (μ : Measure Ω) (m : MeasurableSpace Ω)
    (f g : Ω → ℝ) (ω : Ω) : ℝ :=
  posteriorCovariance (mΩ := mΩ) μ m f g ω / (1 - (μ[f | m] ω) ^ 2)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_OptionResponseReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

variable {Ω ι : Type*} {b : ℕ}

def ownChildFinFamily (e : Fin b ≃ ι) (Z : Option ι → Ω → ℝ) :
    Fin (b + 1) → Ω → ℝ :=
  fun i => Z (((finSuccEquiv b).trans e.optionCongr) i)

@[simp] theorem ownChildFinFamily_zero (e : Fin b ≃ ι)
    (Z : Option ι → Ω → ℝ) : ownChildFinFamily e Z 0 = Z none := rfl

@[simp] theorem ownChildFinFamily_succ (e : Fin b ≃ ι)
    (Z : Option ι → Ω → ℝ) (i : Fin b) :
    ownChildFinFamily e Z i.succ = Z (some (e i)) := by
  simp [ownChildFinFamily]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_FieldCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators ContDiff

namespace Problem367.FinitePosterior

variable {S : Type*} [Fintype S] [Nonempty S]

def tiltCovariance (energy signal observable : S → ℝ) (t : ℝ) : ℝ :=
  mean energy signal (fun s => observable s * signal s) t -
    mean energy signal observable t * mean energy signal signal t

def tiltResponse (energy signal observable : S → ℝ) (t : ℝ) : ℝ :=
  tiltCovariance energy signal observable t /
    (1 - mean energy signal observable t ^ 2)

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_GaussianTimeDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Problem367.FinitePosterior

variable {V : Type*} [Fintype V]

def gaussianObservationCurve (signal noise : V → ℝ) (t : ℝ) : V → ℝ :=
  t • signal + Real.sqrt t • noise

def gaussianObservationVelocity (signal noise : V → ℝ) (t : ℝ) : V → ℝ :=
  signal + (1 / (2 * Real.sqrt t)) • noise

end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_GaussianEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.FinitePosterior

variable {S V : Type*} [Fintype S] [Nonempty S] [Fintype V] [DecidableEq V]

section Planted

variable [MeasurableSpace S] [MeasurableSingletonClass S]

def finiteStandardObservation (spin : S → V → ℝ) (t : ℝ)
    (x : S × (V → ℝ)) : V → ℝ := gaussianObservationCurve (spin x.1) x.2 t

end Planted
end Problem367.FinitePosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_BinaryFusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

def binaryFusion (u v : ℝ) : ℝ := (u + v) / (1 + u * v)

def binaryFusionLoss (u v : ℝ) : ℝ :=
  u ^ 2 * v ^ 2 * (2 - u ^ 2 - v ^ 2) / (1 - u ^ 2 * v ^ 2)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_BinaryFusionJointLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

def binaryFusionJointLaw (mu nu : Measure ℝ) : Measure (ℝ × ℝ) :=
  (mu.prod nu).withDensity (fun p => ENNReal.ofReal (1 + p.1 * p.2))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_ObservationFusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

def observationFusionJointLaw {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu : Measure A) (nu : Measure B) (q : A → ℝ) (r : B → ℝ) : Measure (A × B) :=
  (mu.prod nu).withDensity (fun p => ENNReal.ofReal (1 + q p.1 * r p.2))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_FiniteSignalInformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Problem367

@[reducible] def finiteSignalField {Ω ι : Type*} (m : ι → MeasurableSpace Ω) (I : Finset ι) :
    MeasurableSpace Ω := ⨆ i ∈ I, m i

@[simp] theorem finiteSignalField_singleton {Ω ι : Type*} [DecidableEq ι]
    (m : ι → MeasurableSpace Ω) (i : ι) : finiteSignalField m {i} = m i := by
  simp [finiteSignalField]

@[simp] theorem finiteSignalField_insert {Ω ι : Type*} [DecidableEq ι]
    (m : ι → MeasurableSpace Ω) (I : Finset ι) (i : ι) :
    finiteSignalField m (insert i I) = m i ⊔ finiteSignalField m I := by
  simp [finiteSignalField, Finset.mem_insert, iSup_or, iSup_sup_eq]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FairSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

def fairSpin (u : ℝ) : IsingSpin :=
  if u ≤ 1 / 2 then IsingSpin.neg else IsingSpin.pos

lemma measurable_fairSpin : Measurable fairSpin := by
  exact measurable_const.ite measurableSet_Iic measurable_const

def fairSpinFactor (d : ℕ) (U : TreeVertex d → ℝ) : TreeVertex d → IsingSpin :=
  fun v => fairSpin (U v)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootedBroadcast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

local instance rootedBroadcastMeasurableSingletonSpin :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_SelectedCriticalFieldMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

open PlantedSymmetry

def criticalComponentFieldMomentConstant (d : ℕ) (beta : ℝ) : ℝ :=
  Real.cosh ((d : ℝ) * beta + 1) ^ 2 *
    Real.sqrt (1 / ((1 - (Real.tanh beta) ^ 2) * (Real.tanh beta) ^ 4)) +
    16 * (1 + ((d : ℝ) * beta) ^ 2) * (1 + Real.exp 32)

def criticalComponentBaseExponent (d : ℕ) (beta : ℝ) : ℝ :=
  2 + criticalComponentFieldMomentConstant d beta +
    Real.sqrt (criticalComponentFieldMomentConstant d beta)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ArtanhTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace Problem367.ArtanhTaylor

def remainder (x y : ℝ) : ℝ :=
  Real.artanh y - Real.artanh x - (y - x) / (1 - x ^ 2) -
    x * (y - x) ^ 2 / (1 - x ^ 2) ^ 2

end Problem367.ArtanhTaylor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_InhomogeneousSpinChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.InhomogeneousChain

variable {A : Type*}

def jointWeight (K : ℕ → A → A → ℝ) (w : A → ℝ) (n : ℕ)
    (x : Fin (n + 1) → A) : ℝ :=
  w (x 0) * ∏ i : Fin n, K i (x i.castSucc) (x i.succ)

end Problem367.InhomogeneousChain

namespace Problem367.PosteriorChain

def intercept (beta z : ℝ) : ℝ :=
  (Real.tanh (z + beta) + Real.tanh (z - beta)) / 2

def slope (beta z : ℝ) : ℝ :=
  (Real.tanh (z + beta) - Real.tanh (z - beta)) / 2

end Problem367.PosteriorChain

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ChainMarginals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem367.InhomogeneousChain

variable {A : Type*} [Fintype A]

def advance (K : ℕ → A → A → ℝ) (w : A → ℝ) (b : A) : ℝ :=
  ∑ a, w a * K 0 a b

def coordinateMean (K : ℕ → A → A → ℝ) (w f : A → ℝ)
    (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  ∑ x : Fin (n + 1) → A, jointWeight K w n x * f (x i)

end Problem367.InhomogeneousChain

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ExponentialTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.ExponentialTaylor

theorem norm_exp_I_taylor_two_le (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I +
      (x : ℂ) ^ 2 / 2‖ ≤ 4 * |x| ^ 3 := by
  have hnorm : ‖(x : ℂ) * Complex.I‖ = |x| := by simp
  by_cases hx : |x| ≤ 1
  · have h := Complex.exp_bound (x := (x : ℂ) * Complex.I)
      (by simpa only [hnorm] using hx) (n := 3) (by norm_num)
    have heq : (∑ m ∈ Finset.range 3,
        ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)) =
        1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2 := by
      norm_num [Finset.sum_range_succ, mul_pow, Complex.I_sq]
      ring
    rw [heq, hnorm] at h
    norm_num at h
    have heq' : Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I +
        (x : ℂ) ^ 2 / 2 =
        Complex.exp ((x : ℂ) * Complex.I) -
          (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2) := by ring
    rw [heq']
    exact h.trans (by nlinarith [abs_nonneg x, pow_nonneg (abs_nonneg x) 3])
  · have hx1 : 1 ≤ |x| := (lt_of_not_ge hx).le
    have hsq : |x| ≤ |x| ^ 2 := by nlinarith [abs_nonneg x]
    have hcube : |x| ^ 2 ≤ |x| ^ 3 := by nlinarith [sq_nonneg (|x| - 1)]
    calc
      _ ≤ ‖Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I‖ +
          ‖(x : ℂ) ^ 2 / 2‖ := norm_add_le _ _
      _ ≤ (‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ +
          ‖(x : ℂ) * Complex.I‖) + ‖(x : ℂ) ^ 2 / 2‖ := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ ((‖Complex.exp ((x : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖) +
          ‖(x : ℂ) * Complex.I‖) + ‖(x : ℂ) ^ 2 / 2‖ := by
        gcongr
        exact norm_sub_le _ _
      _ = 2 + |x| + |x| ^ 2 / 2 := by norm_num
      _ ≤ 4 * |x| ^ 3 := by nlinarith

theorem norm_exp_neg_sub_one_add_le_sq {x : ℝ} (hx : 0 ≤ x) :
    ‖Complex.exp ((-x : ℝ) : ℂ) - 1 + (x : ℂ)‖ ≤ x ^ 2 := by
  have heq : Complex.exp ((-x : ℝ) : ℂ) - 1 + (x : ℂ) =
      ((Real.exp (-x) - 1 + x : ℝ) : ℂ) := by simp
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  by_cases hsmall : x ≤ 1
  · have h := Real.norm_exp_sub_one_sub_id_le (x := -x) (by simpa [abs_of_nonneg hx] using hsmall)
    simpa only [Real.norm_eq_abs, sub_neg_eq_add, sq_abs, neg_sq] using h
  · have hlarge : 1 ≤ x := (lt_of_not_ge hsmall).le
    have hnonneg : 0 ≤ Real.exp (-x) - 1 + x := by
      linarith [Real.add_one_le_exp (-x)]
    rw [abs_of_nonneg hnonneg]
    have hbound : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)
    nlinarith

theorem norm_recurrence_error_le_sum
    (z a : ℕ → ℂ) (e : ℕ → ℝ) (n : ℕ)
    (ha : ∀ k < n, ‖a k‖ ≤ 1)
    (he : ∀ k < n, ‖z (k + 1) - a k * z k‖ ≤ e k) :
    ‖z n - (∏ k ∈ Finset.range n, a k) * z 0‖ ≤
      ∑ k ∈ Finset.range n, e k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (fun k hk => ha k (Nat.lt_succ_of_lt hk))
      (fun k hk => he k (Nat.lt_succ_of_lt hk))
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    have heq : z (n + 1) - ((∏ k ∈ Finset.range n, a k) * a n) * z 0 =
        (z (n + 1) - a n * z n) +
          a n * (z n - (∏ k ∈ Finset.range n, a k) * z 0) := by ring
    rw [heq]
    calc
      _ ≤ ‖z (n + 1) - a n * z n‖ +
          ‖a n * (z n - (∏ k ∈ Finset.range n, a k) * z 0)‖ := norm_add_le _ _
      _ ≤ e n + 1 * (∑ k ∈ Finset.range n, e k) := by
        apply add_le_add (he n (by omega))
        rw [norm_mul]
        exact mul_le_mul (ha n (by omega)) hprev (norm_nonneg _) (by norm_num)
      _ = _ := by ring

end Problem367.ExponentialTaylor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_CharacteristicRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology NNReal

namespace Problem367.ExponentialTaylor

theorem norm_gaussian_recurrence_error_le_sum
    (z : ℕ → ℂ) (dt e : ℕ → ℝ) (n : ℕ) {c : ℝ}
    (hc : 0 ≤ c) (hdt : ∀ k < n, 0 ≤ dt k)
    (he : ∀ k < n,
      ‖z (k + 1) - Complex.exp ((-c * dt k : ℝ) : ℂ) * z k‖ ≤ e k) :
    ‖z n - Complex.exp (((-c * ∑ k ∈ Finset.range n, dt k : ℝ) : ℂ)) * z 0‖ ≤
      ∑ k ∈ Finset.range n, e k := by
  have h := norm_recurrence_error_le_sum z
    (fun k => Complex.exp ((-c * dt k : ℝ) : ℂ)) e n
    (fun k hk => ?_) he
  · simpa only [← Complex.exp_sum, ← Complex.ofReal_sum, ← Finset.mul_sum] using h
  · rw [Complex.norm_exp_ofReal]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (hdt k hk))

theorem eq_gaussian_mul_of_recurrence_errors_tendsto_zero
    {ι : Type*} {l : Filter ι} [NeBot l]
    (z : ι → ℕ → ℂ) (dt e : ι → ℕ → ℝ) (N : ι → ℕ)
    {c T : ℝ} {z₀ zT : ℂ}
    (hc : 0 ≤ c)
    (hdt : ∀ i k, k < N i → 0 ≤ dt i k)
    (htotal : ∀ i, ∑ k ∈ Finset.range (N i), dt i k = T)
    (hstart : ∀ i, z i 0 = z₀) (hend : ∀ i, z i (N i) = zT)
    (he : ∀ i k, k < N i →
      ‖z i (k + 1) - Complex.exp ((-c * dt i k : ℝ) : ℂ) * z i k‖ ≤ e i k)
    (hlim : Tendsto (fun i => ∑ k ∈ Finset.range (N i), e i k) l (𝓝 0)) :
    zT = Complex.exp ((-c * T : ℝ) : ℂ) * z₀ := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply ge_of_tendsto hlim
  exact Eventually.of_forall fun i => by
    simpa only [htotal i, hstart i, hend i] using
      norm_gaussian_recurrence_error_le_sum (z i) (dt i) (e i) (N i) hc (hdt i) (he i)

theorem sum_sq_le_total_mul_mesh
    (dt : ℕ → ℝ) (n : ℕ) {mesh : ℝ}
    (hdt : ∀ k < n, 0 ≤ dt k) (hmesh : ∀ k < n, dt k ≤ mesh) :
    (∑ k ∈ Finset.range n, (dt k) ^ 2) ≤
      (∑ k ∈ Finset.range n, dt k) * mesh := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  simpa only [pow_two] using mul_le_mul_of_nonneg_left
    (hmesh k (Finset.mem_range.mp hk)) (hdt k (Finset.mem_range.mp hk))

end Problem367.ExponentialTaylor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ClippedArtanhWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal

namespace Problem367.ClippedArtanhWeight

def clip (r x : ℝ) : ℝ := max (-r) (min r x)

def weight (r x : ℝ) : ℝ := 1 / (1 - clip r x ^ 2)

end Problem367.ClippedArtanhWeight

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ContinuousCoefficientModulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace Problem367.ContinuousCoefficientModulus

def pairModulus (x y : ℕ → ℝ) (n : ℕ) : ℝ :=
  ↑((Finset.range n).sup (fun i => ‖x i - y i‖₊))

end Problem367.ContinuousCoefficientModulus

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ContinuousModification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367
namespace ContinuousModification

variable {T Ω : Type*}

def sampledLimit (q : T → ℕ → T) (F : T → Ω → ℝ) (t : T) (ω : Ω) : ℝ :=
  limUnder atTop (fun n => F (q t n) ω)

end ContinuousModification
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_CoupledSmallLogLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

def cavityLogVarianceCoefficient (theta : ℝ) : ℝ :=
  4 / (1 - theta) ^ 2

def cavityLogTailCoefficient (theta M : ℝ) : ℝ :=
  8 * (M / (1 - theta)) ^ 2

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_DependentInfinitePiPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory MeasureTheory.Measure Set

namespace Problem367

variable {I : Type*} {A B : I → Type*}
  [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (B i)]

def dependentPiPairEquiv : (∀ i, A i × B i) ≃ᵐ ((∀ i, A i) × (∀ i, B i)) where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun p := fun i => (p.1 i, p.2 i)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    change Measurable (fun x : ∀ i, A i × B i =>
      (fun i => (x i).1, fun i => (x i).2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : (∀ i, A i) × (∀ i, B i) =>
      fun i => (p.1 i, p.2 i))
    fun_prop

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteSpinCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FiniteSpinCoupling

variable {A B : Type*} [Fintype A] [Fintype B]

def partition (E : A → ℝ) : ℝ := ∑ x, Real.exp (E x)

end Problem367.FiniteSpinCoupling

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_KernelCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem367.KernelCompatibility

variable {P F X : Type*} [MeasurableSpace P] [MeasurableSpace F] [MeasurableSpace X]

def reorderEquiv : ((P × F) × X) ≃ᵐ ((P × X) × F) where
  toFun q := ((q.1.1, q.2), q.1.2)
  invFun q := ((q.1.1, q.2), q.1.2)
  left_inv q := rfl
  right_inv q := rfl
  measurable_toFun := by
    change Measurable (fun q : (P × F) × X => ((q.1.1, q.2), q.1.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun q : (P × X) × F => ((q.1.1, q.2), q.1.2))
    fun_prop

end Problem367.KernelCompatibility

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_WeightedPrimitiveApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace Problem367.WeightedPrimitiveApproximation

open EnergyRiemann (point point_zero )

def weightedSum (f a : ℝ → ℝ) (T : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, f (point T n i) *
    ∫ s in point T n i..point T n (i + 1), a s

end Problem367.WeightedPrimitiveApproximation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_BoundedMartingaleVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal

namespace Problem367.BoundedMartingaleVariation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

def incrementModulus (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ↑((Finset.range n).sup (fun i => ‖x (i + 1) - x i‖₊))

end Problem367.BoundedMartingaleVariation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_QuadraticVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators

namespace Problem367.MartingaleQuadraticVariation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

def increment {I : Type*} (M : I → Ω → ℝ) (s t : I) : Ω → ℝ :=
  fun ω => M t ω - M s ω

def squareError {I : Type*} (M A : I → Ω → ℝ) (s t : I) : Ω → ℝ :=
  fun ω => (increment M s t ω) ^ 2 - increment A s t ω

end Problem367.MartingaleQuadraticVariation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_CompensatorVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace Problem367.CompensatorVariation

def squaredIncrements (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, (a (i + 1) - a i) ^ 2

end Problem367.CompensatorVariation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_ArtanhMartingaleFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Problem367.ArtanhMartingaleFormula

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

def firstWeight (x : ℝ) : ℝ := 1 / (1 - x ^ 2)

def linearSum {I : Type*} (M : I → Ω → ℝ) (t : ℕ → I) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N, firstWeight (M (t i) ω) * (M (t (i + 1)) ω - M (t i) ω)

end Problem367.ArtanhMartingaleFormula

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_NNRealArtanhFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem367.NNRealArtanhFormula

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

def realFiltration (F : Filtration ℝ≥0 mΩ) : Filtration ℝ mΩ :=
  ⟨fun t => F t.toNNReal, fun _ _ h => F.mono (Real.toNNReal_mono h),
    fun t => F.le t.toNNReal⟩

end Problem367.NNRealArtanhFormula

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_NonbacktrackingComplement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped InnerProduct

namespace Problem367.NonbacktrackingComplement

variable {𝕜 E V : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

def liftComplement (F H : E →L[𝕜] V) : Submodule 𝕜 V :=
  (F†).ker ⊓ (H†).ker

@[simp]
theorem mem_liftComplement (F H : E →L[𝕜] V) (y : V) :
    y ∈ liftComplement F H ↔ (F†) y = 0 ∧ (H†) y = 0 := by
  rfl

def edgeOperator (c r : ℝ) (F H : E →L[𝕜] V) (J : V ≃ₗᵢ[𝕜] V) :
    V →L[𝕜] V :=
  (c : 𝕜) • H.comp (F†) - (r : 𝕜) • J.toContinuousLinearEquiv.toContinuousLinearMap

end Problem367.NonbacktrackingComplement

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_NonbacktrackingOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

section RCLikeOperators
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

def diagonalOperator (B : E →L[𝕜] E) : E × E →L[𝕜] E × E := B.prodMap B

def nonbacktrackingOperator (B c d : E →L[𝕜] E) : E × E →L[𝕜] E × E :=
  (-(c.comp (ContinuousLinearMap.snd 𝕜 E E))).prod
    (d.comp (ContinuousLinearMap.fst 𝕜 E E) + (2 * B).comp (ContinuousLinearMap.snd 𝕜 E E))

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
@[simp]
theorem diagonalOperator_apply (B : E →L[𝕜] E) (x : E × E) :
    diagonalOperator B x = (B x.1, B x.2) := rfl

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
@[simp]
theorem nonbacktrackingOperator_apply (B c d : E →L[𝕜] E) (x : E × E) :
    nonbacktrackingOperator B c d x = (-c x.2, d x.1 + B x.2 + B x.2) := by
  simp [nonbacktrackingOperator, two_mul, add_assoc]

def diagonalOperatorAlgHom : (E →L[𝕜] E) →ₐ[ℝ] (E × E →L[𝕜] E × E) where
  toFun := diagonalOperator
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    rfl
  map_mul' := by
    intro A B
    apply ContinuousLinearMap.ext
    intro x
    rfl
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro x
    rfl
  map_add' := by
    intro A B
    apply ContinuousLinearMap.ext
    intro x
    rfl
  commutes' := by
    intro r
    apply ContinuousLinearMap.ext
    intro x
    rfl

end RCLikeOperators

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_NonbacktrackingDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped InnerProduct

namespace Problem367.NonbacktrackingComplement

section Generic

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace E]

def vertexRate (q : ℝ) : ℝ := 2 * q / (1 + q ^ 2)

def normalizedVertex (q : ℝ) (A : E →L[𝕜] E) : E →L[𝕜] E :=
  ((1 + q ^ 2) / (2 * q)) • A

def normalizedCompanion (q : ℝ) (A : E →L[𝕜] E) : (E × E) →L[𝕜] (E × E) :=
  nonbacktrackingOperator (normalizedVertex q A)
    (algebraMap ℝ (E →L[𝕜] E) q) (algebraMap ℝ (E →L[𝕜] E) q⁻¹)

def companion (q : ℝ) (A : E →L[𝕜] E) : (E × E) →L[𝕜] (E × E) :=
  q • normalizedCompanion q A

end Generic

end Problem367.NonbacktrackingComplement

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ObservableDisintegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.ObservableDisintegration

variable {W X : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [StandardBorelSpace X] [Nonempty X]

omit [StandardBorelSpace X] [Nonempty X] in
theorem measurable_graphMap {Z : X → W} (hZ : Measurable Z) :
    Measurable (fun x => (Z x, x)) := hZ.prodMk measurable_id

end Problem367.ObservableDisintegration

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ProgressivePrimitiveFubini
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367

theorem posterior_version_ae_abs_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ}
    (hposterior : ∀ t, m t =ᵐ[P] P[σ | F t]) {C : ℝ}
    (hσbound : ∀ᵐ ω ∂P, |σ ω| ≤ C) :
    ∀ t, ∀ᵐ ω ∂P, |m t ω| ≤ C := by
  intro t
  filter_upwards [hposterior t,
    ae_bdd_abs_condExp_of_ae_bdd_abs (m := F t) hσbound] with ω hmω hb
  simpa only [hmω] using hb

theorem ae_locally_integrable_bounded_progressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) {C : ℝ}
    (hbound : ∀ t, ∀ᵐ ω ∂P, |m t ω| ≤ C) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      IntegrableOn (fun u : ℝ => m u.toNNReal ω) (Ioc 0 (n : ℝ)) ∧
      ∀ᵐ u ∂volume.restrict (Ioc 0 (n : ℝ)), |m u.toNNReal ω| ≤ C := by
  apply ae_all_iff.mpr
  intro n
  let ν : Measure ℝ := volume.restrict (Ioc 0 (n : ℝ))
  have hclip : StronglyMeasurable
      (fun p : ℝ × Ω => m (min p.1.toNNReal (n : ℝ≥0)) p.2) :=
    (stronglyMeasurable_clipped_nnreal_process hm (n : ℝ≥0)).mono
      (sup_le_sup le_rfl (MeasurableSpace.comap_mono (F.le (n : ℝ≥0))))
  have hb : ∀ᵐ ω ∂P, ∀ᵐ u ∂ν, |m (min u.toNNReal (n : ℝ≥0)) ω| ≤ C := by
    apply (Measure.ae_ae_comm (μ := ν) (ν := P)
      (p := fun u ω => |m (min u.toNNReal (n : ℝ≥0)) ω| ≤ C)
      (measurableSet_le hclip.measurable.abs measurable_const)).mp
    exact Filter.Eventually.of_forall fun u => hbound (min u.toNNReal (n : ℝ≥0))
  have hi := (integrable_nnreal_process_interval_of_progressive_bounded
    hm C hbound 0 (n : ℝ≥0)).prod_left_ae
  filter_upwards [hb, hi] with ω hbω hiω
  constructor
  · simpa only [IntegrableOn, NNReal.coe_zero, NNReal.coe_natCast] using hiω
  · filter_upwards [hbω, ae_restrict_mem measurableSet_Ioc] with u hu hmem
    have hun : u.toNNReal ≤ (n : ℝ≥0) :=
      Real.toNNReal_le_iff_le_coe.mpr hmem.2
    simpa only [min_eq_left hun] using hu

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ProgressiveVersionPushforward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.ProgressiveVersionPushforward
open ContinuousModification

local instance instMeasurableSpaceContinuousMapNNRealReal_solutions : MeasurableSpace C(ℝ≥0, ℝ) := borel _

def gridTime (p : ℤ × ℕ) : ℝ≥0 := ((p.1 : ℝ) / (2 : ℝ) ^ p.2).toNNReal

end Problem367.ProgressiveVersionPushforward

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_RadialWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367
namespace RadialWalk

variable {V : Type*} {d : ℕ}

def average (step : V → Fin d → V) (f : V → ℝ) (v : V) : ℝ :=
  (∑ c : Fin d, f (step v c)) / d

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def vectorAverage (step : V → Fin d → V) (f : V → H) (v : V) : H :=
  (d : ℝ)⁻¹ • ∑ c : Fin d, f (step v c)

def weight (d : ℕ) (n : ℕ) : ℝ :=
  (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ n

def rate (d : ℕ) : ℝ := 2 * Real.sqrt ((d : ℝ) - 1) / d

end RadialWalk
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_RadialRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem367
namespace RadialWalk

variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def operatorAverage (S : Fin d → H →L[ℝ] H) : H →L[ℝ] H :=
  (d : ℝ)⁻¹ • ∑ c, S c

end RadialWalk
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_RoundedStoppingTimes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped NNReal Topology

namespace Problem367.RoundedStoppingTimes

def round (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  (⌈t * (n + 1 : ℝ≥0)⌉₊ : ℝ≥0) / (n + 1 : ℝ≥0)

def roundTop (n : ℕ) : WithTop ℝ≥0 → WithTop ℝ≥0 := WithTop.map (round n)

@[simp] theorem roundTop_top (n : ℕ) : roundTop n ⊤ = ⊤ := rfl

@[simp] theorem roundTop_coe (n : ℕ) (t : ℝ≥0) :
    roundTop n t = (round n t : WithTop ℝ≥0) := rfl

end Problem367.RoundedStoppingTimes

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_WeightedOrbitAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem367.WeightedOrbitAverage

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def average [Fintype ι] (F : ι → Ω → ℝ) : Ω → ℝ :=
  fun ω => (Fintype.card ι : ℝ)⁻¹ * ∑ i, F i ω

end Problem367.WeightedOrbitAverage

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_ArrayCharacterization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.GaussianArrayCharacterization

theorem isGaussianProcess_array_of_finite_coordinate_processes
    {ι T Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ι → T → Ω → ℝ}
    (h : ∀ I : Finset ι,
      IsGaussianProcess (fun t ω (i : I) => B i t ω) P) :
    IsGaussianProcess (fun p : (_ : ι) × T => B p.1 p.2) P := by
  classical
  constructor
  intro S
  let I : Finset ι := S.image Sigma.fst
  let J : Finset T := S.image Sigma.snd
  let L : (J → I → ℝ) →L[ℝ] (S → ℝ) :=
    { toFun x p := x
        ⟨p.1.2, Finset.mem_image_of_mem Sigma.snd p.2⟩
        ⟨p.1.1, Finset.mem_image_of_mem Sigma.fst p.2⟩
      map_add' x y := by rfl
      map_smul' c x := by rfl }
  exact (h I |>.hasGaussianLaw J).map L

open ConditionalGaussianVector

theorem covariance_coordinate_ne_of_gaussianPi_law
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ι → ℝ} (v : ι → ℝ≥0)
    (hX : HasLaw X (Measure.pi (fun i => gaussianReal 0 (v i))) P)
    (i j : ι) (hij : i ≠ j) :
    cov[fun ω => X ω i, fun ω => X ω j; P] = 0 := by
  rw [hX.covariance_fun_comp (f := fun x : ι → ℝ => x i) (g := fun x : ι → ℝ => x j)
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable]
  exact (iIndepFun_pi (X := fun _ : ι => id) (fun _ => aemeasurable_id)).indepFun hij
    |>.covariance_eq_zero
      ((measurePreserving_eval (fun i => gaussianReal 0 (v i)) i).hasLaw.hasGaussianLaw.memLp_two)
      ((measurePreserving_eval (fun i => gaussianReal 0 (v i)) j).hasLaw.hasGaussianLaw.memLp_two)

end Problem367.GaussianArrayCharacterization

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_SmallBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real

namespace Problem367

def gaussianSmallRadius (δ : ℝ≥0) : ℝ :=
  Real.sqrt (2 * Real.pi * δ) / 4

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_LeafMessage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.GibbsLeaf

def eliminationConstant (beta z : ℝ) : ℝ :=
  2 * Real.exp ((Real.log (Real.cosh (z + beta)) + Real.log (Real.cosh (z - beta))) / 2)

end Problem367.GibbsLeaf

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_TreeCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367.GaussianTreeCovariance

def gaussianContraction (beta : ℝ) (δ : ℝ≥0) : ℝ :=
  1 - ((1 - Real.tanh beta ^ 2) * Real.tanh (gaussianSmallRadius δ) ^ 2) / 2

end Problem367.GaussianTreeCovariance

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_CharacteristicStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem norm_integral_weighted_exp_remainder_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℂ) (D : Ω → ℝ)
    (hZ : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ 1)
    (hD3 : Integrable (fun ω => |D ω| ^ 3) μ) :
    ‖∫ ω, Z ω * (Complex.exp ((D ω : ℂ) * Complex.I) - 1 -
      (D ω : ℂ) * Complex.I + (D ω : ℂ) ^ 2 / 2) ∂μ‖ ≤
      4 * ∫ ω, |D ω| ^ 3 ∂μ := by
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le (hD3.const_mul 4)
  filter_upwards [hZ] with ω hω
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖Complex.exp ((D ω : ℂ) * Complex.I) - 1 -
        (D ω : ℂ) * Complex.I + (D ω : ℂ) ^ 2 / 2‖ :=
      mul_le_mul_of_nonneg_right hω (norm_nonneg _)
    _ ≤ 4 * |D ω| ^ 3 := by
      simpa only [one_mul] using ExponentialTaylor.norm_exp_I_taylor_two_le (D ω)

theorem norm_integral_weighted_characteristic_step
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (Z : Ω → ℂ) (D : Ω → ℝ) (h : ℝ)
    (hZm : AEStronglyMeasurable Z μ) (hZ : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ 1)
    (hDm : Measurable D) (hD : Integrable D μ)
    (hD2 : Integrable (fun ω => D ω ^ 2) μ)
    (hD3 : Integrable (fun ω => |D ω| ^ 3) μ)
    (hzero : ∫ ω, Z ω * (D ω : ℂ) ∂μ = 0) :
    ‖(∫ ω, Z ω * Complex.exp ((D ω : ℂ) * Complex.I) ∂μ) -
      (1 - (h : ℂ) / 2) * ∫ ω, Z ω ∂μ‖ ≤
      4 * ∫ ω, |D ω| ^ 3 ∂μ +
        (1 / 2 : ℝ) * ‖∫ ω, Z ω * ((D ω : ℂ) ^ 2 - h) ∂μ‖ := by
  let R : Ω → ℂ := fun ω => Complex.exp ((D ω : ℂ) * Complex.I) - 1 -
    (D ω : ℂ) * Complex.I + (D ω : ℂ) ^ 2 / 2
  have hZint : Integrable Z μ :=
    (integrable_const (1 : ℝ)).mono' hZm hZ
  have hRm : Measurable R := by dsimp [R]; fun_prop
  have hRint : Integrable R μ := (hD3.const_mul 4).mono' hRm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ExponentialTaylor.norm_exp_I_taylor_two_le (D ω))
  have hZR : Integrable (fun ω => Z ω * R ω) μ := hRint.bdd_mul hZm hZ
  have hZD : Integrable (fun ω => Z ω * (D ω : ℂ)) μ :=
    hD.ofReal.bdd_mul hZm hZ
  have hZQ : Integrable (fun ω => Z ω * ((D ω : ℂ) ^ 2 - h)) μ := by
    have hq : Integrable (fun ω => (D ω : ℂ) ^ 2 - h) μ := by
      have hd2 : Integrable (fun ω => (D ω : ℂ) ^ 2) μ := by
        convert hD2.ofReal using 1
        all_goals try with_reducible_and_instances rfl
        funext ω
        exact (Complex.ofReal_pow (D ω) 2).symm
      exact hd2.sub (integrable_const (h : ℂ))
    exact hq.bdd_mul hZm hZ
  have hE : Integrable (fun ω => Z ω * Complex.exp ((D ω : ℂ) * Complex.I)) μ := by
    apply hZint.mul_bdd (c := 1)
    · apply Measurable.aestronglyMeasurable
      fun_prop
    · exact Filter.Eventually.of_forall (fun ω => by simp)
  have halg : (fun ω => Z ω * Complex.exp ((D ω : ℂ) * Complex.I) -
      (1 - (h : ℂ) / 2) * Z ω) =
      (fun ω => Z ω * R ω + (Z ω * (D ω : ℂ)) * Complex.I -
        (Z ω * ((D ω : ℂ) ^ 2 - h)) * (1 / 2 : ℂ)) := by
    funext ω
    dsimp [R]
    ring
  have hid : (∫ ω, Z ω * Complex.exp ((D ω : ℂ) * Complex.I) ∂μ) -
      (1 - (h : ℂ) / 2) * ∫ ω, Z ω ∂μ =
      (∫ ω, Z ω * R ω ∂μ) -
        (∫ ω, Z ω * ((D ω : ℂ) ^ 2 - h) ∂μ) * (1 / 2 : ℂ) := by
    rw [← integral_const_mul, ← integral_sub hE (hZint.const_mul _), halg]
    have hsum : Integrable (fun ω => Z ω * R ω + Z ω * (D ω : ℂ) * Complex.I) μ :=
      hZR.add (hZD.mul_const Complex.I)
    rw [integral_sub hsum (hZQ.mul_const (1 / 2 : ℂ)),
      integral_add hZR (hZD.mul_const Complex.I), integral_mul_const, integral_mul_const, hzero]
    simp
  rw [hid]
  calc
    _ ≤ ‖∫ ω, Z ω * R ω ∂μ‖ +
        ‖(∫ ω, Z ω * ((D ω : ℂ) ^ 2 - h) ∂μ) * (1 / 2 : ℂ)‖ := norm_sub_le _ _
    _ ≤ (4 * ∫ ω, |D ω| ^ 3 ∂μ) +
        (1 / 2 : ℝ) * ‖∫ ω, Z ω * ((D ω : ℂ) ^ 2 - h) ∂μ‖ := by
      have hr := norm_integral_weighted_exp_remainder_le μ Z D hZ hD3
      have hn : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
      rw [norm_mul, hn, mul_comm _ (1 / 2 : ℝ)]
      exact add_le_add hr le_rfl

theorem norm_gaussian_coefficient_sub_euler_le_global {h : ℝ} (h0 : 0 ≤ h) :
    ‖Complex.exp (-(h : ℂ) / 2) - (1 - (h : ℂ) / 2)‖ ≤ h ^ 2 / 4 := by
  have hb := ExponentialTaylor.norm_exp_neg_sub_one_add_le_sq
    (show 0 ≤ h / 2 by positivity)
  convert hb using 1 <;> first | (with_reducible_and_instances rfl) | (push_cast <;> congr 1 <;> ring_nf)

theorem norm_integral_weighted_characteristic_gaussian_step_all
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℂ) (D : Ω → ℝ) {h : ℝ} (h0 : 0 ≤ h)
    (hZm : AEStronglyMeasurable Z μ) (hZ : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ 1)
    (hDm : Measurable D) (hD : Integrable D μ)
    (hD2 : Integrable (fun ω => D ω ^ 2) μ)
    (hD3 : Integrable (fun ω => |D ω| ^ 3) μ)
    (hzero : ∫ ω, Z ω * (D ω : ℂ) ∂μ = 0) :
    ‖(∫ ω, Z ω * Complex.exp ((D ω : ℂ) * Complex.I) ∂μ) -
      Complex.exp (-(h : ℂ) / 2) * ∫ ω, Z ω ∂μ‖ ≤
      4 * ∫ ω, |D ω| ^ 3 ∂μ +
        (1 / 2 : ℝ) * ‖∫ ω, Z ω * ((D ω : ℂ) ^ 2 - h) ∂μ‖ + h ^ 2 / 4 := by
  have he := norm_integral_weighted_characteristic_step μ Z D h
    hZm hZ hDm hD hD2 hD3 hzero
  have hZi : ‖∫ ω, Z ω ∂μ‖ ≤ 1 := by
    simpa using norm_integral_le_of_norm_le (integrable_const (1 : ℝ)) hZ
  have hc : ‖(1 - (h : ℂ) / 2) - Complex.exp (-(h : ℂ) / 2)‖ ≤ h ^ 2 / 4 := by
    rw [norm_sub_rev]
    exact norm_gaussian_coefficient_sub_euler_le_global h0
  have halg : (∫ ω, Z ω * Complex.exp ((D ω : ℂ) * Complex.I) ∂μ) -
        Complex.exp (-(h : ℂ) / 2) * ∫ ω, Z ω ∂μ =
      ((∫ ω, Z ω * Complex.exp ((D ω : ℂ) * Complex.I) ∂μ) -
        (1 - (h : ℂ) / 2) * ∫ ω, Z ω ∂μ) +
      ((1 - (h : ℂ) / 2) - Complex.exp (-(h : ℂ) / 2)) * ∫ ω, Z ω ∂μ := by ring
  rw [halg]
  apply (norm_add_le _ _).trans
  apply add_le_add he
  rw [norm_mul]
  calc
    _ ≤ ‖(1 - (h : ℂ) / 2) - Complex.exp (-(h : ℂ) / 2)‖ * 1 :=
      mul_le_mul_of_nonneg_left hZi (norm_nonneg _)
    _ ≤ h ^ 2 / 4 := by simpa only [mul_one] using hc

theorem norm_integral_weighted_characteristic_gaussian_step_all_mul
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℂ) (D : Ω → ℝ) (u : ℝ) {v : ℝ}
    (hv : 0 ≤ v)
    (hZm : AEStronglyMeasurable Z μ) (hZ : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ 1)
    (hDm : Measurable D) (hD : Integrable D μ)
    (hD2 : Integrable (fun ω => D ω ^ 2) μ)
    (hD3 : Integrable (fun ω => |D ω| ^ 3) μ)
    (hzero : ∫ ω, Z ω * (D ω : ℂ) ∂μ = 0) :
    ‖(∫ ω, Z ω * Complex.exp (((u * D ω : ℝ) : ℂ) * Complex.I) ∂μ) -
      Complex.exp (-((u ^ 2 * v : ℝ) : ℂ) / 2) * ∫ ω, Z ω ∂μ‖ ≤
      4 * |u| ^ 3 * (∫ ω, |D ω| ^ 3 ∂μ) +
        (u ^ 2 / 2) * ‖∫ ω, Z ω * ((D ω : ℂ) ^ 2 - v) ∂μ‖ +
        u ^ 4 * v ^ 2 / 4 := by
  have hs2 : Integrable (fun ω => (u * D ω) ^ 2) μ := by
    simpa only [mul_pow] using hD2.const_mul (u ^ 2)
  have hs3 : Integrable (fun ω => |u * D ω| ^ 3) μ := by
    simpa only [abs_mul, mul_pow] using hD3.const_mul (|u| ^ 3)
  have hsz : ∫ ω, Z ω * ((u * D ω : ℝ) : ℂ) ∂μ = 0 := by
    calc
      _ = (u : ℂ) * ∫ ω, Z ω * (D ω : ℂ) ∂μ := by
        rw [← integral_const_mul]
        congr 1
        funext ω
        push_cast
        ring
      _ = 0 := by rw [hzero, mul_zero]
  have hs := norm_integral_weighted_characteristic_gaussian_step_all μ Z
    (fun ω => u * D ω) (mul_nonneg (sq_nonneg u) hv)
    hZm hZ (hDm.const_mul u) (hD.const_mul u) hs2 hs3 hsz
  have hthird : (∫ ω, |u * D ω| ^ 3 ∂μ) =
      |u| ^ 3 * ∫ ω, |D ω| ^ 3 ∂μ := by
    simp only [abs_mul, mul_pow, integral_const_mul]
  have hquad : (∫ ω, Z ω * (((u * D ω : ℝ) : ℂ) ^ 2 - (u ^ 2 * v : ℝ)) ∂μ) =
      (u : ℂ) ^ 2 * ∫ ω, Z ω * ((D ω : ℂ) ^ 2 - v) ∂μ := by
    rw [← integral_const_mul]
    congr 1
    funext ω
    push_cast
    ring
  rw [hthird, hquad, norm_mul] at hs
  have hn : ‖(u : ℂ) ^ 2‖ = u ^ 2 := by simp [norm_pow, sq_abs]
  rw [hn] at hs
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_GaussianCriterion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem integral_phase_increment_identity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω → ℂ) (A B C : Ω → ℝ) (u : ℝ) :
    (∫ ω, (Z ω * Complex.exp (((u * (B ω - A ω) : ℝ) : ℂ) * Complex.I)) *
      Complex.exp (((u * (C ω - B ω) : ℝ) : ℂ) * Complex.I) ∂P) =
    ∫ ω, Z ω * Complex.exp (((u * (C ω - A ω) : ℝ) : ℂ) * Complex.I) ∂P := by
  congr 1
  funext ω
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_InnovationPathMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

theorem stronglyMeasurable_joint_of_isStronglyProgressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) :
    StronglyMeasurable (fun p : ℝ≥0 × Ω => m p.1 p.2) := by
  have hstop (n : ℕ) : StronglyMeasurable
      (fun p : ℝ≥0 × Ω => m (min p.1 (n : ℝ≥0)) p.2) := by
    have hlocal : StronglyMeasurable[
        @MeasurableSpace.prod ℝ≥0 Ω inferInstance (F n)]
        (fun p : ℝ≥0 × Ω => m (min p.1 (n : ℝ≥0)) p.2) := by
      let : MeasurableSpace Ω := F n
      have htime : Measurable (fun t : ℝ≥0 =>
          (⟨min t (n : ℝ≥0), by simp⟩ : Set.Iic (n : ℝ≥0))) :=
        (measurable_id.min measurable_const).subtype_mk
      exact (hm n).comp_measurable ((htime.comp measurable_fst).prodMk measurable_snd)
    exact hlocal.mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono (F.le n)))
  apply stronglyMeasurable_of_tendsto atTop hstop
  apply tendsto_pi_nhds.mpr
  intro p
  apply tendsto_const_nhds.congr'
  obtain ⟨N, hN⟩ := exists_nat_ge p.1
  filter_upwards [eventually_ge_atTop N] with n hn
  have hpn : p.1 ≤ (n : ℝ≥0) := hN.trans (by exact_mod_cast hn)
  simp [min_eq_left hpn]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_Recovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367.SpinRecovery

def spinSign : IsingSpin → ℝ
  | .neg => -1
  | .pos => 1

def decode (x : ℕ → ℝ) : IsingSpin := by
  classical
  exact if Tendsto (fun n : ℕ => x n / (n : ℝ)) atTop (𝓝 (-1 : ℝ))
    then .neg else .pos

def decodeArray {V : Type*} (x : V → ℕ → ℝ) : V → IsingSpin :=
  fun v => decode (x v)

end Problem367.SpinRecovery

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyPathBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367.IsingCopyPathBounds

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def edgeLogBound (d : ℕ) (beta : ℝ) (T : ℝ≥0) : ℝ :=
  2 * ((2 * (T : ℝ) + 2 * (d : ℝ) * beta) / (1 - Real.tanh beta))

end Problem367.IsingCopyPathBounds

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spectral_SpectralClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367
namespace SpectralClosure

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

def rangeClosure (D : E →L[𝕜] F) : Submodule 𝕜 F :=
  (LinearMap.range (D : E →ₗ[𝕜] F)).topologicalClosure

instance rangeClosure_completeSpace (D : E →L[𝕜] F) : CompleteSpace (rangeClosure D) :=
  (Submodule.isClosed_topologicalClosure (LinearMap.range (D : E →ₗ[𝕜] F))).isComplete.completeSpace_coe

omit [CompleteSpace F] in
@[simp] lemma mem_rangeClosure (D : E →L[𝕜] F) (y : F) :
    y ∈ rangeClosure D ↔ y ∈ closure (Set.range D) := Iff.rfl

omit [CompleteSpace F] in

lemma mapsTo_rangeClosure (T : E →L[𝕜] E) (S : F →L[𝕜] F) (D : E →L[𝕜] F)
    (hDS : ∀ x, S (D x) = D (T x)) :
    ∀ y ∈ rangeClosure D, S y ∈ rangeClosure D := by
  have hmap : Set.MapsTo S (Set.range D) (Set.range D) := by
    rintro y ⟨x, rfl⟩
    exact ⟨T x, (hDS x).symm⟩
  exact hmap.closure S.continuous

def restrict (T : E →L[𝕜] E) (S : F →L[𝕜] F) (D : E →L[𝕜] F)
    (hDS : ∀ x, S (D x) = D (T x)) : rangeClosure D →L[𝕜] rangeClosure D :=
  S.restrict (mapsTo_rangeClosure T S D hDS)

end SpectralClosure
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.UnifIntegrableCompat
attribute [-instance] _root_.OAI.closedSubmoduleNormedAddCommGroup _root_.OAI.isProbabilityMeasure_map_fst _root_.OAI.isProbabilityMeasure_map_measurableEquiv
attribute [-simp] _root_.OAI.fin3_lit_0_1 _root_.OAI.fin3_lit_0_2 _root_.OAI.fin3_lit_1_0 _root_.OAI.fin3_lit_1_2 _root_.OAI.fin3_lit_2_0 _root_.OAI.fin3_lit_2_1 _root_.OAI.fin3_mk_0 _root_.OAI.fin3_mk_1 _root_.OAI.fin3_mk_2 _root_.OAI.fin4_lit_0_1 _root_.OAI.fin4_lit_0_2 _root_.OAI.fin4_lit_0_3 _root_.OAI.fin4_lit_1_0 _root_.OAI.fin4_lit_1_2 _root_.OAI.fin4_lit_1_3 _root_.OAI.fin4_lit_2_0 _root_.OAI.fin4_lit_2_1 _root_.OAI.fin4_lit_2_3 _root_.OAI.fin4_lit_3_0 _root_.OAI.fin4_lit_3_1 _root_.OAI.fin4_lit_3_2 _root_.OAI.fin4_mk_0 _root_.OAI.fin4_mk_1 _root_.OAI.fin4_mk_2 _root_.OAI.fin4_mk_3 _root_.OAI.fin5_lit_0_1 _root_.OAI.fin5_lit_0_2 _root_.OAI.fin5_lit_0_3 _root_.OAI.fin5_mk_0 _root_.OAI.fin5_mk_1 _root_.OAI.fin5_mk_2 _root_.OAI.fin5_mk_3 _root_.OAI.fin5_mk_4 _root_.OAI.vecCons3_one _root_.OAI.vecCons3_two _root_.OAI.vecCons4_one _root_.OAI.vecCons4_three _root_.OAI.vecCons4_two _root_.OAI.vecConsTail1_1 _root_.OAI.vecConsTail2_1 _root_.OAI.vecConsTail2_2 _root_.OAI.vecConsTail3_1 _root_.OAI.vecConsTail3_2 _root_.OAI.vecConsTail3_3 _root_.OAI.vecConsTail4_1 _root_.OAI.vecConsTail4_2 _root_.OAI.vecConsTail4_3 _root_.OAI.vecConsTail4_4
/-!
# Uniform integrability compatibility layer for ports of openai/math

This file is not OpenAI's code. OpenAI's openai/math is built on Mathlib `d13f23b`; prove2.me's
environment is Mathlib `0df444a`. The two disagree on uniform integrability:

* `d13f23b`'s `UnifIntegrable f p μ` is `Tendsto (fun ε ↦ ⨆ i s (_ : μ s ≤ ε), eLpNorm (f i) p
  (μ.restrict s)) (𝓝 0) (𝓝 0)` (extended-real `ε`, `δ`, any set `s`); `0df444a`'s is the real
  `ε`-`δ` form over measurable sets with `eLpNorm (s.indicator (f i)) p μ`.
* `d13f23b`'s `UniformIntegrable f p μ` has two components, `UnifIntegrable f p μ` and a uniform
  bound; `0df444a`'s has three, measurability first. In `d13f23b` the bound alone gives
  measurability, since there `eLpNorm` is `∞` on a function that is not a.e. strongly measurable.
* `d13f23b`'s `UnifTight` takes `ε : ℝ≥0∞`; `0df444a`'s takes `ε : ℝ≥0`.

So that ported proofs keep `d13f23b`'s shapes (`obtain ⟨hu, C, hC⟩ := hf`, `intro ε hε` with
`ε : ℝ≥0∞`, `hu.ae_mono`, `hu.comp`), this file declares `OAI.UnifIntegrable`,
`OAI.UniformIntegrable` and `OAI.UnifTight`, which shadow Mathlib's inside `namespace OAI`, with
`d13f23b`'s API under `d13f23b`'s names, proved from `0df444a`'s. `OAI.UnifIntegrable` carries the
measurability of every member (Mathlib's `UnifIntegrable` together with it), so that
`OAI.UniformIntegrable` keeps `d13f23b`'s two components and is equivalent to Mathlib's
`UniformIntegrable` (`OAI.uniformIntegrable_iff_mathlib`).

`d13f23b`'s `unifIntegrable_iff` and `unifIntegrable_iff'` cannot be stated as equivalences here
(the right sides do not give measurability): the port rewrites their `mp` direction to
`OAI.UnifIntegrable.enn_spec` / `enn_spec'` and their `mpr` direction to
`OAI.UnifIntegrable.of_enn` / `of_enn'`, which take the measurability as a second argument.
-/

noncomputable section UnifIntegrableCompat

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace OAI

variable {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
  {p : ℝ≥0∞} {f g : ι → α → β}

/-- Uniform integrability in the measure theory sense, with the measurability of each member
(`d13f23b`'s `UnifIntegrable`, whose `eLpNorm` bounds carry it). -/
def UnifIntegrable {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  MeasureTheory.UnifIntegrable f p μ ∧ ∀ i, AEStronglyMeasurable (f i) μ

/-! ### `UnifIntegrable` -/

namespace UnifIntegrable

@[aesop 50% apply (rule_sets := [Measurable])]
protected theorem aestronglyMeasurable (hf : UnifIntegrable f p μ) (i : ι) :
    AEStronglyMeasurable (f i) μ :=
  hf.2 i

end UnifIntegrable

/-! ### `UniformIntegrable` -/

/-! ### `UnifTight` -/

end OAI

end UnifIntegrableCompat
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_FiniteCoordinateFiltration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Problem367

def coordinateFiltration
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (s : ℕ → Set ι) (hs : Monotone s) :
    Filtration ℕ (MeasurableSpace.pi (X := X)) where
  seq n := cylinderEvents (s n)
  mono' _ _ h := cylinderEvents_mono (hs h)
  le' _ := cylinderEvents_le_pi

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ColoredEdgeLifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped InnerProductSpace
namespace Problem367.ColoredEdgeLifts
variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {d : ℕ}

abbrev EdgeSpace (d : ℕ) (E : Type*) := PiLp 2 (fun _ : Fin d => E)

def tailLift (hd : 0 < d) : E →ₗᵢ[𝕜] EdgeSpace d E where
  toFun x := WithLp.toLp 2 (fun _ => (((Real.sqrt (d : ℝ))⁻¹ : ℝ) : 𝕜) • x)
  map_add' x y := by
    ext i
    simp [smul_add]
  map_smul' a x := by
    ext i
    simp [smul_smul, mul_comm]
  norm_map' x := by
    have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
    have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdreal
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2]
    change (∑ _i : Fin d, ‖((((Real.sqrt (d : ℝ))⁻¹ : ℝ) : 𝕜) • x)‖ ^ 2) = ‖x‖ ^ 2
    simp only [norm_smul, RCLike.norm_ofReal,
      abs_of_pos (inv_pos.2 hs), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_pow, inv_pow]
    rw [Real.sq_sqrt hdreal.le]
    field_simp

@[simp] theorem tailLift_apply (hd : 0 < d) (x : E) (i : Fin d) :
    tailLift (𝕜 := 𝕜) hd x i = (((Real.sqrt (d : ℝ))⁻¹ : ℝ) : 𝕜) • x := rfl

def reversal (S : Fin d → E ≃ₗᵢ[𝕜] E) : EdgeSpace d E ≃ₗᵢ[𝕜] EdgeSpace d E :=
  LinearIsometryEquiv.piLpCongrRight 2 S

@[simp] theorem reversal_apply (S : Fin d → E ≃ₗᵢ[𝕜] E) (x : EdgeSpace d E) (i : Fin d) :
    reversal S x i = S i (x i) := rfl

def headLift (hd : 0 < d) (S : Fin d → E ≃ₗᵢ[𝕜] E) : E →ₗᵢ[𝕜] EdgeSpace d E :=
  (reversal S).toLinearIsometry.comp (tailLift (𝕜 := 𝕜) hd)

@[simp] theorem headLift_apply (hd : 0 < d) (S : Fin d → E ≃ₗᵢ[𝕜] E) (x : E) (i : Fin d) :
    headLift hd S x i = (((Real.sqrt (d : ℝ))⁻¹ : ℝ) : 𝕜) • S i x := by
  change S i ((((Real.sqrt (d : ℝ))⁻¹ : ℝ) : 𝕜) • x) = _
  exact (S i).map_smul _ _

@[simp] theorem reversal_tail (hd : 0 < d) (S : Fin d → E ≃ₗᵢ[𝕜] E) (x : E) :
    reversal S (tailLift (𝕜 := 𝕜) hd x) = headLift hd S x := rfl

section Adjoint
variable [CompleteSpace E]

def neighborAverage (S : Fin d → E ≃ₗᵢ[𝕜] E) : E →L[𝕜] E :=
  (((d : ℝ)⁻¹ : ℝ) : 𝕜) • ∑ i, (S i).toContinuousLinearEquiv.toContinuousLinearMap

omit [CompleteSpace E] in
@[simp] theorem neighborAverage_apply (S : Fin d → E ≃ₗᵢ[𝕜] E) (x : E) :
    neighborAverage S x = (((d : ℝ)⁻¹ : ℝ) : 𝕜) • ∑ i, S i x := by
  simp [neighborAverage]

def forwardOperator (hd : 0 < d) (S : Fin d → E ≃ₗᵢ[𝕜] E) (r : ℝ) :
    EdgeSpace d E →L[𝕜] EdgeSpace d E :=
  (((d : ℝ) * r : ℝ) : 𝕜) •
    (headLift hd S).toContinuousLinearMap.comp (tailLift (𝕜 := 𝕜) hd).toContinuousLinearMap.adjoint -
      (r : 𝕜) • (reversal S).toContinuousLinearEquiv.toContinuousLinearMap

end Adjoint

end Problem367.ColoredEdgeLifts

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CriticalSmallLogLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367.IsingCriticalSmallLogLoss

def varianceScale (d : ℕ) (beta : ℝ) (T : ℝ≥0) : ℝ :=
  1 + (2 * (T : ℝ) + 2 * (d : ℝ) * beta) ^ 2

end Problem367.IsingCriticalSmallLogLoss

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathSideLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.PathSideBranches

@[implicit_reducible] def coordinateSigma {V A : Type*} [MeasurableSpace A] (S : Set V) :
    MeasurableSpace (V → A) :=
  MeasurableSpace.comap S.domRestrict inferInstance

end Problem367.PathSideBranches

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_PathPosteriorResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.PathPosterior

def childFields {n : ℕ} (y : Fin (n + 1) → ℝ) (i : ℕ) : ℝ :=
  if hi : i < n then y ⟨i + 1, Nat.succ_lt_succ hi⟩ else 0

end Problem367.PathPosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_OrientedGaussianTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingOrientedPath
open PlantedSymmetry PathSideBranches

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def orientationCutCost (beta : ℝ) (inward : Bool) : ℝ :=
  if inward then Real.exp (4 * beta / (1 - Real.tanh beta)) else 1

end Problem367.IsingOrientedPath

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_WalkObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367
namespace IsingWalk

def conjugateRoot (b theta : ℝ) : ℝ := (b * theta)⁻¹

def eigenRate (b theta : ℝ) : ℝ := (b * theta + theta⁻¹) / (b + 1)

def eigenWeight (b theta : ℝ) (n : ℕ) : ℝ :=
  (eigenRate b theta - conjugateRoot b theta) * theta ^ n -
    (eigenRate b theta - theta) * conjugateRoot b theta ^ n

@[simp] theorem eigenWeight_zero (b theta : ℝ) :
    eigenWeight b theta 0 = theta - conjugateRoot b theta := by
  simp [eigenWeight]

end IsingWalk
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Martingales_StoppedTimePrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace Problem367.StoppedTimePrimitive

def stopDensity {Ω : Type*} (a : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : WithTop ℝ≥0) ≤ τ ω then a t ω else 0

end Problem367.StoppedTimePrimitive

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_InteriorLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped NNReal Topology

namespace Problem367.PosteriorInteriorLocalization

def radius (n : ℕ) : ℝ := 1 - ((n : ℝ) + 2)⁻¹

end Problem367.PosteriorInteriorLocalization

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_StoppingTimes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.PosteriorStoppingTimes

def rationalExit {Ω : Type*} (M : ℝ≥0 → Ω → ℝ) (r : ℝ) (ω : Ω) :
    WithTop ℝ≥0 :=
  ⨅ q : ℚ≥0, if r < |M (q : ℝ≥0) ω| then ((q : ℝ≥0) : WithTop ℝ≥0) else ⊤

abbrev threshold := PosteriorInteriorLocalization.radius

def posteriorExit {Ω : Type*} (M : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) :
    WithTop ℝ≥0 :=
  min (rationalExit M (threshold n) ω) (((n : ℝ≥0) + 1) : WithTop ℝ≥0)

end Problem367.PosteriorStoppingTimes

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_CompensatorStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.PosteriorCompensatorStopping

open PosteriorStoppingTimes

def jointExit {Ω : Type*} (M A : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) :
    WithTop ℝ≥0 :=
  min (posteriorExit M n ω) (rationalExit A ((n : ℝ) + 1) ω)

end Problem367.PosteriorCompensatorStopping

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ColoredPathAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace

namespace Problem367.ColoredPathAverage

def Path (d : ℕ) : ℕ → Fin d → Type
  | 0, _ => PUnit
  | n + 1, i => Σ j : {j : Fin d // j ≠ i}, Path d n j.1

instance pathFintype (d : ℕ) : (n : ℕ) → (i : Fin d) → Fintype (Path d n i)
  | 0, _ => inferInstanceAs (Fintype PUnit)
  | n + 1, i => by
      letI : ∀ j : {j : Fin d // j ≠ i}, Fintype (Path d n j.1) :=
        fun j => pathFintype d n j.1
      exact inferInstanceAs (Fintype (Σ j : {j : Fin d // j ≠ i}, Path d n j.1))

def colors {d : ℕ} : {n : ℕ} → {i : Fin d} → Path d n i → List (Fin d)
  | 0, i, _ => [i]
  | _ + 1, i, p => i :: colors p.2

@[simp] theorem colors_length {d n : ℕ} {i : Fin d} (p : Path d n i) :
    (colors p).length = n + 1 := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [colors, ih]

@[simp] theorem colors_head? {d n : ℕ} {i : Fin d} (p : Path d n i) :
    (colors p).head? = some i := by
  cases n <;> rfl

theorem colors_isChain {d n : ℕ} {i : Fin d} (p : Path d n i) :
    List.IsChain (fun a b : Fin d => a ≠ b) (colors p) := by
  induction n generalizing i with
  | zero => simp [colors]
  | succ n ih =>
      rw [colors, List.isChain_cons]
      refine ⟨?_, ih p.2⟩
      intro j hj
      have hji : p.1.1 = j := by simpa using hj
      subst j
      exact Ne.symm p.1.2

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {d : ℕ}

def pathValue (S : Fin d → E ≃ₗᵢ[𝕜] E) (y : ColoredEdgeLifts.EdgeSpace d E) :
    {n : ℕ} → {i : Fin d} → Path d n i → E
  | 0, i, _ => y i
  | _ + 1, i, p => S i (pathValue S y p.2)

@[simp] theorem pathValue_zero (S : Fin d → E ≃ₗᵢ[𝕜] E)
    (y : ColoredEdgeLifts.EdgeSpace d E) (i : Fin d) (p : Path d 0 i) :
    pathValue S y p = y i := rfl

@[simp] theorem pathValue_succ (S : Fin d → E ≃ₗᵢ[𝕜] E)
    (y : ColoredEdgeLifts.EdgeSpace d E) {n : ℕ} {i : Fin d}
    (p : Path d (n + 1) i) : pathValue S y p = S i (pathValue S y p.2) := rfl

end Problem367.ColoredPathAverage

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367

def pathCorrelationKernel (q : ℝ) (k : ℤ) : ℝ :=
  ((k.natAbs : ℝ) + 1) * q ^ k.natAbs

open MeasureTheory

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ResponseRowEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.ResponseRows

def shellProfile (root : ℝ) (tail : ℕ → ℝ) : ℕ → ℝ
  | 0 => root
  | n + 1 => tail n

@[simp] theorem shellProfile_zero (root : ℝ) (tail : ℕ → ℝ) :
    shellProfile root tail 0 = root := rfl

@[simp] theorem shellProfile_succ (root : ℝ) (tail : ℕ → ℝ) (n : ℕ) :
    shellProfile root tail (n + 1) = tail n := rfl

end Problem367.ResponseRows

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_StemRerootAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem367.TreeOrbitAverage

def stemForbidden {d : ℕ} (stem : List (Fin d)) : Finset (Fin d) :=
  stem.getLast?.toFinset

end Problem367.TreeOrbitAverage

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_WeightedPathSummation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
namespace Problem367

structure WeightedPathEstimates (Q L : ℕ → ℝ)
    (A B E c a q C₀ S V ω : ℝ) : Prop where
  noise_nonneg : ∀ n, 0 ≤ Q n
  linear_nonneg : ∀ n, 0 ≤ L n
  noise_short : ∀ n, Q n ≤ A * S * n
  linear_short : ∀ n, L n ≤ A * V
  noise_long : ∀ n : ℕ, C₀ / ω ≤ (n : ℝ) →
    Q n ≤ B * S * ((n : ℝ) * Real.exp (-(c * ω) * n)) +
      E * ((n : ℝ) ^ 2 * Real.exp (-a * q ^ n))
  linear_long : ∀ n : ℕ, C₀ / ω ≤ (n : ℝ) →
    L n ≤ B * V * Real.exp (-(c * ω) * n) + E * Real.exp (-a * q ^ n)

def weightedPathEndpointConstant (A B E c a q C : ℝ) : ℝ :=
  max 1 (max
    (max (2 * A * (C + 1) ^ 2 + B * (2 / min c 1) ^ 2)
      (E * ∑' n : ℕ, (n : ℝ) ^ 2 * Real.exp (-(a / 2) * q ^ n)))
    (max
      (max (A * (C + 1) + B * (2 / min c 1))
        (E * ∑' n : ℕ, Real.exp (-(a / 2) * q ^ n)))
      (max (4 * Real.sqrt A * (C + 1) * Real.sqrt (C + 1) +
        Real.sqrt B * (3 / (min (c / 2) 1 * Real.sqrt (min (c / 2) 1))))
        (Real.sqrt E * ∑' n : ℕ, (n : ℝ) * Real.exp (-((a / 2) / 2) * q ^ n)))))

end Problem367

end

end OAI
end


