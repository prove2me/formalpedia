-- Prove2me | Definitions.Def_OAIQ072A000
-- name    : OAIQ072A000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:16:59.698982+00:00
-- url     : https://prove2.me/theorems/6cb1b862-1d26-4b19-aea0-6c88f691379a
-- title:
--   Definitions bundle OAIQ072A000 of the split of OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1109 declarations of OpenAI's Lean: 793 definitions, 29 inductive types or structures, 33 instances and 254 theorems. The definitions and types are `OAI.SKGap.ClosedConvexNonempty`, `OAI.SKGap.ComplexMatrix.colVec`, `OAI.SKGap.ComplexMatrix.conjugate`, `OAI.SKGap.ComplexMatrix.conjugateCLM`, `OAI.SKGap.ComplexMatrix.conjugateIsometry`, `OAI.SKGap.ComplexMatrix.diagonalChange`, `OAI.SKGap.ComplexMatrix.entryCLM`, `OAI.SKGap.ComplexMatrix.entryLM`, `OAI.SKGap.ComplexMatrix.fl1`, `OAI.SKGap.ComplexMatrix.fl2`, `OAI.SKGap.ComplexMatrix.fourierMoment`, `OAI.SKGap.ComplexMatrix.gBound`, `OAI.SKGap.ComplexMatrix.gChange`, `OAI.SKGap.ComplexMatrix.gLip`, `OAI.SKGap.ComplexMatrix.gMixed`, `OAI.SKGap.ComplexMatrix.hermitianBall`, `OAI.SKGap.ComplexMatrix.imaginary`, `OAI.SKGap.ComplexMatrix.instContinuousENormMatrixComplex_solutions`, `OAI.SKGap.ComplexMatrix.instContinuousENormMatrixComplex_solutions_1`, `OAI.SKGap.ComplexMatrix.instContinuousENormMatrixComplex_solutions_3`, `OAI.SKGap.ComplexMatrix.kBound`, `OAI.SKGap.ComplexMatrix.kChange`, `OAI.SKGap.ComplexMatrix.kLip`, `OAI.SKGap.ComplexMatrix.kMixed`, `OAI.SKGap.ComplexMatrix.kernelMatrix`, `OAI.SKGap.ComplexMatrix.lin`, `OAI.SKGap.ComplexMatrix.linCLM`, `OAI.SKGap.ComplexMatrix.linEquiv`, `OAI.SKGap.ComplexMatrix.linHom`, `OAI.SKGap.ComplexMatrix.matrixProject`, `OAI.SKGap.ComplexMatrix.opNorm`, `OAI.SKGap.ComplexMatrix.parameterGC`, `OAI.SKGap.ComplexMatrix.parameterGM`, `OAI.SKGap.ComplexMatrix.parameterKC`, `OAI.SKGap.ComplexMatrix.parameterKM`, `OAI.SKGap.ComplexMatrix.sandShift`, `OAI.SKGap.ComplexMatrix.schwartzMatrix`, `OAI.SKGap.ComplexMatrix.shiftChange`, `OAI.SKGap.ComplexMatrix.truncatedG`, `OAI.SKGap.ComplexMatrix.truncatedK` and 782 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `SKGap_Brownian_ContinuousPosteriorMass`, `SKGap_Brownian_IntervalMesh`, `SKGap_Brownian_LogDetPath`, `SKGap_Brownian_PathAgreement`, `SKGap_Brownian_PathBias`, `SKGap_Brownian_PathBiasBase`, `SKGap_Brownian_PathCutoff`, `SKGap_Brownian_PathDiagonal`, `SKGap_Brownian_PathExpectation`, `SKGap_Entropy_ConditionalBadSet`, `SKGap_Entropy_EntropyEll`, `SKGap_Entropy_EntropyTransport`, `SKGap_Entropy_RootBadMeasurable`, `SKGap_Entropy_ScalarEntropyTarget`, `SKGap_Entropy_SparseSubsetEntropy`, `SKGap_Entropy_WeightedScalarMoments`, `SKGap_Gaussian_ConditionalGramTail`, `SKGap_Gaussian_FourierMoment`, `SKGap_Gaussian_GOEGaussian`, `SKGap_Gaussian_GOEScalarTail`, `SKGap_Gaussian_GaussianCoordinates`, `SKGap_Gaussian_GaussianGramMomentsJoined`, `SKGap_Gaussian_GaussianLinearDensity`, `SKGap_Gaussian_GaussianMarginal`, `SKGap_Gaussian_GaussianMatrixChaining`, `SKGap_Gaussian_GaussianPartition`, `SKGap_Gaussian_GaussianProductPower`, `SKGap_Gaussian_GaussianQuadratic`, `SKGap_Gaussian_GaussianRegression`, `SKGap_Gaussian_GaussianSign`, `SKGap_Gaussian_LocalGaussianMoments`, `SKGap_Gaussian_MatrixNormTail`, `SKGap_Gaussian_PartitionSecondMoment`, `SKGap_Gaussian_PhiMoments`, `SKGap_Gaussian_PhiStein`, `SKGap_Gaussian_ScalarMomentGram`, `SKGap_Gaussian_SquareTail`, `SKGap_Gaussian_StandardGaussianProduct`, `SKGap_Localization_AffineBilinear`, `SKGap_Localization_Append`, `SKGap_Localization_Bilinear`, `SKGap_Localization_Bilinear2`, `SKGap_Localization_BilinearUnion`, `SKGap_Localization_BlockDegree`, `SKGap_Localization_BoxChaining`, `SKGap_Localization_Character`, `SKGap_Localization_ClosedMarked`, `SKGap_Localization_ClosedMarkedControl`, `SKGap_Localization_ClosedPrediction`, `SKGap_Localization_CoefficientRow`, `SKGap_Localization_CompactTube`, `SKGap_Localization_CondSubConst`, `SKGap_Localization_ConditionalEmpiricalLaw`, `SKGap_Localization_ConditionalIntegralRate`, `SKGap_Localization_ConditionalMiddleSize`, `SKGap_Localization_ConditionalModelAlgebra`, `SKGap_Localization_ConditionalRankAlgebra`, `SKGap_Localization_ConditionalTolerance`, `SKGap_Localization_ConditionalWeight`, `SKGap_Localization_Conjugation`, `SKGap_Localization_CoordinateDeriv`, `SKGap_Localization_CubeApprox`, `SKGap_Localization_DiagonalHessianJoined`, `SKGap_Localization_DiagonalSqrt`, `SKGap_Localization_DivergenceIntegrand`, `SKGap_Localization_DriftSquare`, `SKGap_Localization_EmpiricalConditionalData`, `SKGap_Localization_EmpiricalGramBound`, `SKGap_Localization_EmpiricalLaw`, `SKGap_Localization_EntryLM`, `SKGap_Localization_Envelope`, `SKGap_Localization_EqualityCurve`, `SKGap_Localization_Error`, `SKGap_Localization_ExpDuhamel`, `SKGap_Localization_ExpSum`, `SKGap_Localization_ExpectedCutoff`, `SKGap_Localization_FiniteMax`, `SKGap_Localization_FiniteRankPositive`, `SKGap_Localization_FixedTimeQuenched`, `SKGap_Localization_FockSeries`, `SKGap_Localization_FrobeniusSq`, `SKGap_Localization_GeneralTemplateRegularity`, `SKGap_Localization_GramColumnBounds`, `SKGap_Localization_GramUniformRobust`, `SKGap_Localization_GridSteps`, `SKGap_Localization_Letter`, `SKGap_Localization_LinSub`, `SKGap_Localization_LiteralSeriesLiftAppend`, `SKGap_Localization_LocalCoefficient`, `SKGap_Localization_LocalRecipeClass`, `SKGap_Localization_LocalStartedDiagonal`, `SKGap_Localization_LocalUniformWeak`, `SKGap_Localization_LocalVolumeChange`, `SKGap_Localization_LocalVolumeEnergy`, `SKGap_Localization_LocalWeakBase`, `SKGap_Localization_Map`, `SKGap_Localization_MarkedErrorRate`, `SKGap_Localization_NoiseSplit`, `SKGap_Localization_Operation`, `SKGap_Localization_PhiAlgebra`, `SKGap_Localization_PhiBounds`, `SKGap_Localization_PhiCoefficient`, `SKGap_Localization_PhiFrechet`, `SKGap_Localization_PhiRatio`, `SKGap_Localization_PhiResponse`, `SKGap_Localization_PlantedFixedTime`, `SKGap_Localization_PlantedMarginalLaw`, `SKGap_Localization_PrimaryDifferentiation`, `SKGap_Localization_PrimaryLocalInput`, `SKGap_Localization_PrimaryPrediction`, `SKGap_Localization_PrimaryQuenched`, `SKGap_Localization_ProjectedMarkedIBP`, `SKGap_Localization_ProjectedReal`, `SKGap_Localization_Quadratic`, `SKGap_Localization_QuadraticCoeff`, `SKGap_Localization_QuenchedHelpers`, `SKGap_Localization_RankCovariance`, `SKGap_Localization_RareCoordinate`, `SKGap_Localization_RealParameterIncrement`, `SKGap_Localization_RealPart`, `SKGap_Localization_RealQuadratic`, `SKGap_Localization_RecipeCoefficientClosure`, `SKGap_Localization_RecipeGraph`, `SKGap_Localization_RecipeMarked`, `SKGap_Localization_Reference`, `SKGap_Localization_ResidualAdmissibility`, `SKGap_Localization_ResidualInduction`, `SKGap_Localization_SandShift`, `SKGap_Localization_ScalarEmpirical`, `SKGap_Localization_ScalarFixedPointJoined`, `SKGap_Localization_ScalarParametersJoined`, `SKGap_Localization_ScalarRelativeIsolation`, `SKGap_Localization_ScalarVariance`, `SKGap_Localization_SeparateCut`, `SKGap_Localization_SparseCubeNet`, `SKGap_Localization_StartedGraph`, `SKGap_Localization_StartedMarked`, `SKGap_Localization_StartedRecipe`, `SKGap_Localization_TAPGauge`, `SKGap_Localization_TAPVectorTaylor`, `SKGap_Localization_TapPotential`, `SKGap_Localization_TemplatePatterns`, `SKGap_Localization_TruncationGoodSet`, `SKGap_Localization_UniformRecipeClass`, `SKGap_Localization_UnitBall`, `SKGap_Localization_Vectorize`, `SKGap_Localization_WeakResidual`, `SKGap_Matrix_BufferedClosedWord`, `SKGap_Matrix_ClosedErrorTrace`, `SKGap_Matrix_ClosedTrace`, `SKGap_Matrix_ClosedTreeMatrix`, `SKGap_Matrix_DiscreteMatrixCalculus`, `SKGap_Matrix_FixedNormRecipeEvent`, `SKGap_Matrix_FockTensor`, `SKGap_Matrix_GOEBilinearCov`, `SKGap_Matrix_GOEDiagonalSquare`, `SKGap_Matrix_GOERegression`, `SKGap_Matrix_GOEResidualCov`, `SKGap_Matrix_GOESparse`, `SKGap_Matrix_GOESubmatrix`, `SKGap_Matrix_GlobalWordIncrement`, `SKGap_Matrix_InverseDiagram`, `SKGap_Matrix_InverseSeries`, `SKGap_Matrix_LiftMatrix`, `SKGap_Matrix_LogDetExpected`, `SKGap_Matrix_LogDetIntegral`, `SKGap_Matrix_LoopPrediction`, `SKGap_Matrix_MarkedWordIBP`, `SKGap_Matrix_MatrixCoordinates`, `SKGap_Matrix_MatrixEntryCLM`, `SKGap_Matrix_MatrixQuad`, `SKGap_Matrix_MatrixSeminorm`, `SKGap_Matrix_MatrixWordIncrement`, `SKGap_Matrix_MatrixWordRegularity`, `SKGap_Matrix_NormalLogConst`, `SKGap_Matrix_OpNorm`, `SKGap_Matrix_OpNormKernelMatrixSub`, `SKGap_Matrix_PrimaryMatrix`, `SKGap_Matrix_PrimitiveTrace`, `SKGap_Matrix_RecipeTraceBudget`, `SKGap_Matrix_RegularizedLogDet`, `SKGap_Matrix_StartedWordClosure`, `SKGap_Matrix_TanhMatrixBounds`, `SKGap_Matrix_Trace`, `SKGap_Matrix_Word`, `SKGap_Matrix_WordBaseBias`, `SKGap_Matrix_WordBiasInduction`, `SKGap_Matrix_WordDerivative`, `SKGap_Matrix_WordDiagUniform`, `SKGap_Matrix_WordExpectedRecursion`, `SKGap_Matrix_WordFockSeries`, `SKGap_Matrix_WordIncrement`, `SKGap_Matrix_WordLeading`, `SKGap_Matrix_WordLoop`, `SKGap_Matrix_WordLoopLeading`, `SKGap_Matrix_WordPartnerContraction`, `SKGap_Matrix_WordTemplateSurjective`, `SKGap_Posterior_BufferedPosteriorDirection`, `SKGap_Posterior_GOEObservation`, `SKGap_Posterior_GOEPointwisePosterior`, `SKGap_Posterior_GaussianChannel`, `SKGap_Posterior_History`, `SKGap_Posterior_QuenchedPosterior`, `SKGap_Posterior_StaticExperimentBridge`, `SKGap_Stability_ConditionalMean`, `SKGap_Stability_DiagonalStability`, `SKGap_Stability_FieldIntegralReduction`, `SKGap_Stability_FixedTimeAnnealed`, `SKGap_Stability_GaugeStabilityLaw`, `SKGap_Stability_ImplicitFlip`, `SKGap_Stability_ImplicitLinear`, `SKGap_Stability_ImplicitPerturb`, `SKGap_Stability_ImplicitUniformControl`, `SKGap_Stability_Ordinary`, `SKGap_Stability_OrdinaryGraph`, `SKGap_Stability_OrdinaryRecipe`, `SKGap_Stability_RootDiagonalTransfer`, `SKGap_Stability_RootGrid`, `SKGap_Stability_StabilityMatrix`, `SKGap_Stability_StableFields`, `SKGap_Stability_TapFieldE`, `SKGap_Stability_WordPredictionStability`, `SKGap_Stability_WordStableAgreement`, `SKGap_Terminal_ConsDiag`, `SKGap_Terminal_FieldGibbs`, `SKGap_Terminal_FiniteSpinCalculus`, `SKGap_Terminal_GibbsExpectation`, `SKGap_Terminal_Map`, `SKGap_Terminal_PairBoltzmann`, `SKGap_Terminal_PairConditioning`, `SKGap_Terminal_PairCrossIdentity`, `SKGap_Terminal_PairGibbsBound`, `SKGap_Terminal_PairRationalBounds`, `SKGap_Terminal_SmallFieldCount`, `SKGap_Terminal_Spin`, `SKGap_Terminal_SpinEnergy`, `SKGap_Terminal_SpinLocalField`, `SKGap_Terminal_TerminalDeterministic`, `SKGap_Terminal_TerminalMatrixTransfer`, `SKGap_Terminal_TerminalProbability`, `SKGap_Terminal_TerminalRates`.
--
--   **Imports.** It imports the published bundle `Def_SKHighTemperature`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ072A002`; the statements `OAI.SKGapCutoff.Recipe.disorder_norm_event`, `OAI.SKGap.FullMain.quenched_grid_root_stability`, `OAI.SKGap.FullMain.quenched_posterior_covariance`, `OAI.SKGap.ObservationBridge.annealed_fixed_time_root_stability`, `OAI.SKGap.actualWord_loop`, `OAI.SKGap.actual_logdet_mean`, `OAI.SKGap.actual_path_bias`, `OAI.SKGap.actual_projected_path_equivalents`, `OAI.SKGap.actual_word_simultaneous_prediction_of_cutoff`, `OAI.SKGap.all_actualWords_gaussian_chaining`, `OAI.SKGap.compact_conditional_uniform_tail`, `OAI.SKGap.conditional_bad_integral_rate`, `OAI.SKGap.conditional_empirical_simultaneous`, `OAI.SKGap.conditional_field_stability`, `OAI.SKGap.field_logdet_uniform`, `OAI.SKGap.logPathGood_exponential`, `OAI.SKGap.path_all_good_exponential`, `OAI.SKGap.path_goodSet_exponential`, `OAI.SKGap.path_self_consistency`, `OAI.SKGap.path_wk_bias`, `OAI.SKGap.positive_time_root_stability`, `OAI.SKGap.smalltime_bad_integral`, `OAI.SKGap.terminalMatrixData_actual_whp`, `OAI.SKGap.terminal_gap_high_probability` and `OAI.SKGap.zeroDiag_exact_word_source_restriction`; the proofs of `OAI.SKGapCutoff.Recipe.disorder_norm_event`, `OAI.SKGap.FullMain.quenched_grid_root_stability`, `OAI.SKGap.ObservationBridge.annealed_fixed_time_root_stability`, `OAI.SKGap.actualWord_loop`, `OAI.SKGap.actual_logdet_mean`, `OAI.SKGap.actual_path_bias`, `OAI.SKGap.actual_projected_path_equivalents`, `OAI.SKGap.actual_word_simultaneous_prediction_of_cutoff`, `OAI.SKGap.all_actualWords_gaussian_chaining`, `OAI.SKGap.compact_conditional_uniform_tail`, `OAI.SKGap.conditional_bad_integral_rate`, `OAI.SKGap.conditional_empirical_simultaneous`, `OAI.SKGap.conditional_field_stability`, `OAI.SKGap.field_logdet_uniform`, `OAI.SKGap.logPathGood_exponential`, `OAI.SKGap.path_all_good_exponential`, `OAI.SKGap.path_goodSet_exponential`, `OAI.SKGap.path_self_consistency`, `OAI.SKGap.path_wk_bias`, `OAI.SKGap.positive_time_root_stability`, `OAI.SKGap.smalltime_bad_integral`, `OAI.SKGap.terminalMatrixData_actual_whp`, `OAI.SKGap.terminal_gap_high_probability` and `OAI.SKGap.zeroDiag_exact_word_source_restriction`.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit 1581d4c

import Mathlib
import Definitions.Def_SKHighTemperature

section
-- module Solutions.OAIQ072_SK.Compat
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
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_PhiStein
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace SKGap.Stein

def weight (a u : ℝ) : ℝ := Real.exp (a*(1-u^2)/2)
def numerator (z r a : ℝ) : ℝ := ∫u in (0:ℝ)..1,weight a u*Real.cosh (u*(z-r))
def numeratorZ (z r a : ℝ) : ℝ := ∫u in (0:ℝ)..1,weight a u*u*Real.sinh (u*(z-r))
def phi (z r a : ℝ) : ℝ := ∫u in (0:ℝ)..1,
  weight a u*Real.cosh (u*(z-r))/(Real.cosh z*Real.cosh r)
def phiZ (z r a : ℝ) : ℝ := numeratorZ z r a/(Real.cosh z*Real.cosh r)-Real.tanh z*phi z r a

end SKGap.Stein

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_Spin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators

namespace SKGapCutoff

abbrev Spin (n : ℕ) := Fin n → Bool
abbrev Interaction (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def spin {n : ℕ} (x : Spin n) (i : Fin n) : ℝ := if x i then 1 else -1

def replace {n : ℕ} (x : Spin n) (i : Fin n) (b : Bool) : Spin n :=
  Function.update x i b

noncomputable def halfDiff {n : ℕ} (i : Fin n) (f : Spin n → ℝ)
    (x : Spin n) : ℝ := (f (replace x i true) - f (replace x i false)) / 2

noncomputable def field {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) : ℝ :=
  ∑ j, J i j * spin x j

@[simp] theorem replace_same {n : ℕ} (x : Spin n) (i : Fin n) (b : Bool) :
    replace x i b i = b := by
  simp [replace]

@[simp] theorem replace_replace {n : ℕ} (x : Spin n) (i : Fin n) (a b : Bool) :
    replace (replace x i a) i b = replace x i b := by
  simp [replace, Function.update_idem]

@[simp] theorem replace_self {n : ℕ} (x : Spin n) (i : Fin n) :
    replace x i (x i) = x := by
  simp [replace]

@[simp] theorem halfDiff_replace {n : ℕ} (i : Fin n) (f : Spin n → ℝ)
    (x : Spin n) (b : Bool) : halfDiff i f (replace x i b) = halfDiff i f x := by
  simp [halfDiff]

@[simp] theorem halfDiff_self {n : ℕ} (i : Fin n) (f : Spin n → ℝ)
    (x : Spin n) : halfDiff i (halfDiff i f) x = 0 := by
  simp [halfDiff]

@[simp] theorem halfDiff_const {n : ℕ} (i : Fin n) (c : ℝ) (x : Spin n) :
    halfDiff i (fun _ => c) x = 0 := by
  simp [halfDiff]

@[simp] theorem halfDiff_spin {n : ℕ} (i j : Fin n) (x : Spin n) :
    halfDiff i (fun y => spin y j) x = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    norm_num [halfDiff, spin]
  · simp [halfDiff, spin, replace, Function.update_of_ne (Ne.symm h), h]

abbrev Observables (n : ℕ) := Spin n → ℝ
abbrev VectorFields (n : ℕ) := Spin n → Fin n → ℝ

noncomputable def energy {n : ℕ} (J : Interaction n) (x : Spin n) : ℝ :=
  (∑ i, ∑ j, spin x i * J i j * spin x j) / 2

end SKGapCutoff
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Character
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
namespace SKGapCutoff

@[simp] theorem spin_sq {n : ℕ} (x : Spin n) (i : Fin n) : spin x i ^ 2 = 1 := by
  unfold spin
  cases x i <;> norm_num

@[simp] theorem spin_mul_self {n : ℕ} (x : Spin n) (i : Fin n) :
    spin x i * spin x i = 1 := by simpa only [pow_two] using spin_sq x i

@[simp] theorem field_zero {n : ℕ} (x : Spin n) (i : Fin n) :
    field (0 : Interaction n) x i = 0 := by simp [field]

@[simp] theorem energy_zero {n : ℕ} (x : Spin n) :
    energy (0 : Interaction n) x = 0 := by simp [energy]

@[simp] theorem card_spin (n : ℕ) : Fintype.card (Spin n) = 2 ^ n := by
  simp [Spin]

end SKGapCutoff
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_GibbsExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
namespace SKGapCutoff
open Filter Topology

def flip {n : ℕ} (x : Spin n) (i : Fin n) : Spin n := replace x i (!x i)

@[simp] lemma flip_flip {n : ℕ} (x : Spin n) (i : Fin n) : flip (flip x i) i = x := by
  simp [flip]

@[simp] lemma spin_flip_self {n : ℕ} (x : Spin n) (i : Fin n) :
    spin (flip x i) i = -spin x i := by
  cases h : x i <;> simp [flip, spin, h]

@[simp] lemma halfDiff_flip {n : ℕ} (i : Fin n) (f : Observables n) (x : Spin n) :
    halfDiff i f (flip x i) = halfDiff i f x := by simp [flip]

end SKGapCutoff

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ScalarVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
namespace SKGapCutoff

noncomputable def scalarVariance (y : ℝ) : ℝ := 1 - Real.tanh y ^ 2

end SKGapCutoff

open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PhiBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory
namespace SKGap.Stein

def numeratorZZ (z r a : ℝ) : ℝ := ∫u in (0:ℝ)..1,weight a u*u^2*Real.cosh (u*(z-r))

def logSlope (z r a : ℝ) : ℝ := phiZ z r a/phi z r a

def logSlopeZ (z r a : ℝ) : ℝ := numeratorZZ z r a/numerator z r a-
  (numeratorZ z r a/numerator z r a)^2-SKGapCutoff.scalarVariance z

end SKGap.Stein

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_PhiMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory
namespace SKGap.Stein

def hyper (b : Bool) (x : ℝ) : ℝ := if b then Real.sinh x else Real.cosh x

def momentNum (p q : ℕ) (b : Bool) (d a : ℝ) : ℝ :=
  ∫u in (0:ℝ)..1,weight a u*u^p*((1-u^2)/2)^q*hyper b (u*d)

def moment (p q : ℕ) (b : Bool) (z r a : ℝ) : ℝ :=
  momentNum p q b (z-r) a/(Real.cosh z*Real.cosh r)

end SKGap.Stein

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_StandardGaussianProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
namespace SKGap

theorem hasDerivAt_gaussianPDFReal (d : ℝ) {s : ℝ≥0} (hs : s ≠ 0) (y : ℝ) :
    HasDerivAt (gaussianPDFReal d s)
      (-(y - d) / (s : ℝ) * gaussianPDFReal d s y) y := by
  have hsp : 0 < (s : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hs)
  unfold gaussianPDFReal
  convert! (((((hasDerivAt_id y).sub_const d).pow 2).neg.div_const
    (2 * (s : ℝ))).exp).const_mul (1 / sqrt (2 * π * (s : ℝ))) using 1
  · ext x
    simp only [one_div, Pi.neg_apply, Pi.pow_apply, id_eq]
  · simp only [Pi.neg_apply, Pi.pow_apply, id_eq]
    norm_num
    ring

theorem integrable_gaussian_iff {d : ℝ} {s : ℝ≥0} (hs : s ≠ 0) {f : ℝ → ℝ} :
    Integrable f (gaussianReal d s) ↔ Integrable (fun y => gaussianPDFReal d s y * f y) := by
  rw [gaussianReal_of_var_ne_zero d hs,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF d s)
      (ae_of_all _ (fun _ => gaussianPDF_lt_top))]
  simp only [toReal_gaussianPDF, smul_eq_mul]

theorem gaussian_integration_by_parts {d : ℝ} {s : ℝ≥0} (hs : s ≠ 0)
    {f f' : ℝ → ℝ} (hd : ∀ y, HasDerivAt f (f' y) y)
    (hf : Integrable f (gaussianReal d s)) (hf' : Integrable f' (gaussianReal d s))
    (hyf : Integrable (fun y => (y - d) * f y) (gaussianReal d s)) :
    (∫ y, (y - d) * f y ∂gaussianReal d s) =
      (s : ℝ) * (∫ y, f' y ∂gaussianReal d s) := by
  have hsp : 0 < (s : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hs)
  have hfg := (integrable_gaussian_iff hs).mp hf
  have hf'g := (integrable_gaussian_iff hs).mp hf'
  have hyfg := (integrable_gaussian_iff hs).mp hyf
  have hder (y : ℝ) : HasDerivAt (fun y => gaussianPDFReal d s y * f y)
      (gaussianPDFReal d s y * f' y -
        (gaussianPDFReal d s y * ((y - d) * f y)) / (s : ℝ)) y := by
    convert! (hasDerivAt_gaussianPDFReal d hs y).mul (hd y) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hii : Integrable (fun y => gaussianPDFReal d s y * f' y -
      (gaussianPDFReal d s y * ((y - d) * f y)) / (s : ℝ)) :=
    hf'g.sub (hyfg.div_const _)
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hder hii hfg
  rw [integral_sub hf'g (hyfg.div_const (s : ℝ)), integral_div] at hz
  rw [integral_gaussianReal_eq_integral_smul hs,
    integral_gaussianReal_eq_integral_smul hs]
  simp only [smul_eq_mul]
  have he : (∫ y, gaussianPDFReal d s y * ((y - d) * f y)) / (s : ℝ) =
      ∫ y, gaussianPDFReal d s y * f' y := by linarith
  have hm := (div_eq_iff hsp.ne').mp he
  nlinarith only [hm]

def standardGaussianProduct (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct (n : ℕ) : IsProbabilityMeasure (standardGaussianProduct n) := by
  unfold standardGaussianProduct
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end SKGap

open Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_CoordinateDeriv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
namespace SKGap

def coordinateDeriv {n : ℕ} (i : Fin (n+1)) (f : (Fin (n+1) → ℝ) → ℝ)
    (x : Fin (n+1) → ℝ) : ℝ :=
  deriv (fun z => f (i.insertNth z (i.removeNth x))) (x i)

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def finiteCoordinateDeriv (i : κ) (f : (κ → ℝ) → ℝ) (x : κ → ℝ) : ℝ :=
  deriv (fun z => f (Function.update x i z)) (x i)

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_FiniteSpinCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter

namespace SKGap

section FiniteSpinCalculus

variable {n : ℕ}

@[simp] theorem spinValue_true : spinValue true = 1 := rfl
@[simp] theorem spinValue_false : spinValue false = -1 := rfl
@[simp] theorem spinValue_not (b : Bool) : spinValue (!b) = -spinValue b := by
  cases b <;> norm_num [spinValue]
@[simp] theorem spinValue_sq (b : Bool) : spinValue b ^ 2 = 1 := by
  cases b <;> norm_num [spinValue]

@[simp] theorem coupling_diag (g : Disorder n) (i : Fin n) : coupling g i i = 0 := by
  simp [coupling]

@[simp] theorem flip_same (i : Fin n) (x : Spin n) : flip i x i = !(x i) := by
  simp [flip]

@[simp] theorem flip_other (i k : Fin n) (x : Spin n) (h : k ≠ i) : flip i x k = x k := by
  simp [flip, h]

@[simp] theorem flip_flip (i : Fin n) (x : Spin n) : flip i (flip i x) = x := by
  ext k
  by_cases h : k = i
  · subst k; simp
  · simp [flip_other, h]

def flipEquiv (i : Fin n) : Spin n ≃ Spin n :=
  Function.Involutive.toPerm (flip i) (flip_flip i)

theorem weight_pos (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) :
    0 < weight g h x := Real.exp_pos _

theorem partition_pos (g : Disorder n) (h : Fin n → ℝ) : 0 < partition g h := by
  exact Finset.sum_pos (fun x _ => weight_pos g h x) Finset.univ_nonempty

theorem mass_pos (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) :
    0 < mass g h x := div_pos (weight_pos g h x) (partition_pos g h)

theorem mass_nonneg (g : Disorder n) (h : Fin n → ℝ) (x : Spin n) :
    0 ≤ mass g h x := (mass_pos g h x).le

@[simp] theorem sum_mass (g : Disorder n) (h : Fin n → ℝ) : ∑ x, mass g h x = 1 := by
  simp only [mass, ← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos g h))

@[simp] theorem expectation_const (g : Disorder n) (h : Fin n → ℝ) (c : ℝ) :
    expectation g h (fun _ => c) = c := by
  simp [expectation, ← Finset.sum_mul]

instance disorderLaw_probability (β : ℝ) (n : ℕ) : IsProbabilityMeasure (disorderLaw β n) := by
  unfold disorderLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end FiniteSpinCalculus

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PhiAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.Stein

inductive KernelExpr where
  | atom (p q : ℕ) (b : Bool)
  | add (f g : KernelExpr)
  | scale (c : ℝ) (f : KernelExpr)
  | tz (f : KernelExpr)
  | tr (f : KernelExpr)

namespace KernelExpr

def eval : KernelExpr → ℝ → ℝ → ℝ → ℝ
  | atom p q b,z,r,a  =>  moment p q b z r a
  | add f g,z,r,a  =>  eval f z r a+eval g z r a
  | scale c f,z,r,a  =>  c*eval f z r a
  | tz f,z,r,a  =>  Real.tanh z*eval f z r a
  | tr f,z,r,a  =>  Real.tanh r*eval f z r a

def mass : KernelExpr → ℝ
  | atom _ _ _  =>  1
  | add f g  =>  mass f+mass g
  | scale c f  =>  |c| *mass f
  | tz f  =>  mass f
  | tr f  =>  mass f

def dz : KernelExpr → KernelExpr
  | atom p q b  =>  add (atom (p+1) q (!b)) (scale (-1) (tz (atom p q b)))
  | add f g  =>  add (dz f) (dz g)
  | scale c f  =>  scale c (dz f)
  | tz f  =>  add (add f (scale (-1) (tz (tz f)))) (tz (dz f))
  | tr f  =>  tr (dz f)

def dr : KernelExpr → KernelExpr
  | atom p q b  =>  add (scale (-1) (atom (p+1) q (!b))) (scale (-1) (tr (atom p q b)))
  | add f g  =>  add (dr f) (dr g)
  | scale c f  =>  scale c (dr f)
  | tz f  =>  tz (dr f)
  | tr f  =>  add (add f (scale (-1) (tr (tr f)))) (tr (dr f))

def da : KernelExpr → KernelExpr
  | atom p q b  =>  atom p (q+1) b
  | add f g  =>  add (da f) (da g)
  | scale c f  =>  scale c (da f)
  | tz f  =>  tz (da f)
  | tr f  =>  tr (da f)

end KernelExpr

inductive Axis where | z | r | a

def coordinateDeriv (i : Axis) (F : ℝ→ℝ→ℝ→ℝ) : ℝ→ℝ→ℝ→ℝ := match i with
  | .z  =>  fun z r a => deriv (fun z => F z r a) z
  | .r  =>  fun z r a => deriv (fun r => F z r a) r
  | .a  =>  fun z r a => deriv (fun a => F z r a) a

namespace KernelExpr

def d (i : Axis) : KernelExpr → KernelExpr := match i with
  | .z  =>  dz | .r  =>  dr | .a  =>  da

end KernelExpr
end SKGap.Stein

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PhiRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.Stein

inductive RatioExpr where
  | constant (c : ℝ)
  | kernel (f : KernelExpr)
  | add (f g : RatioExpr)
  | mul (f g : RatioExpr)
namespace RatioExpr

def eval : RatioExpr → ℝ → ℝ → ℝ → ℝ
  | constant c,_,_,_  =>  c
  | kernel f,z,r,a  =>  f.eval z r a/phi z r a
  | add f g,z,r,a  =>  eval f z r a+eval g z r a
  | mul f g,z,r,a  =>  eval f z r a*eval g z r a

def mass : RatioExpr → ℝ
  | constant c  =>  |c|
  | kernel f  =>  f.mass
  | add f g  =>  mass f+mass g
  | mul f g  =>  mass f*mass g

def d (i : Axis) : RatioExpr → RatioExpr
  | constant _  =>  constant 0
  | kernel f  =>  add (kernel (f.d i))
      (mul (constant (-1)) (mul (kernel f) (kernel ((KernelExpr.atom 0 0 false).d i))))
  | add f g  =>  add (d i f) (d i g)
  | mul f g  =>  add (mul (d i f) g) (mul f (d i g))

end RatioExpr
end SKGap.Stein

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_StableFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Real Matrix
namespace SKGap

abbrev Field (n : ℕ) := Fin n → ℝ

def magnetization {n : ℕ} (y : Field n) : Field n := fun i => tanh (y i)
def overlap {n : ℕ} (y : Field n) : ℝ := (∑ i, magnetization y i ^ 2) / n
def onsager {n : ℕ} (j : ℝ) (y : Field n) : ℝ := j * (1 - overlap y)
def spinVariance {n : ℕ} (y : Field n) : Field n := fun i => 1 - magnetization y i ^ 2

def tapField {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h y : Field n) : Field n := fun i =>
  y i - h i + onsager j y * magnetization y i - ∑ k, J i k * magnetization y k

def hessianCore {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (y : Field n) : Matrix (Fin n) (Fin n) ℝ := fun i k =>
  onsager j y * (if i = k then 1 else 0) - J i k -
    (2 * j / n) * magnetization y i * magnetization y k

def fieldHessian {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (y A : Field n) : Matrix (Fin n) (Fin n) ℝ := fun i k =>
  (if i = k then 1 else 0) + sqrt (A i) * hessianCore j J y i k * sqrt (A k)

def vectorSqNorm {n : ℕ} (x : Field n) : ℝ := ∑ i, x i ^ 2

def quadraticForm {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (x : Field n) : ℝ :=
  ∑ i, ∑ k, x i * J i k * x k

def fieldJacobian {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (y : Field n) : Matrix (Fin n) (Fin n) ℝ := fun i k =>
  (if i = k then 1 else 0) + hessianCore j J y i k * spinVariance y k

theorem hasDerivAt_tanh (y : ℝ) : HasDerivAt tanh (1 - tanh y ^ 2) y := by
  convert! (Real.hasDerivAt_sinh y).div (Real.hasDerivAt_cosh y) (cosh_pos y).ne' using 1
  · ext x
    exact tanh_eq_sinh_div_cosh x
  · rw [tanh_eq_sinh_div_cosh]
    field_simp

def overlapDerivative {n : ℕ} (y : Field n) : Field n →L[ℝ] ℝ :=
  (2 / (n : ℝ)) • ∑ k, (magnetization y k * spinVariance y k) • ContinuousLinearMap.proj k

def vectorNorm {n : ℕ} (x : Field n) : ℝ :=
  ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖

def sqrtVarianceMul {n : ℕ} (y v : Field n) : Field n :=
  fun i => sqrt (spinVariance y i) * v i

attribute [local irreducible] vectorNorm

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ScalarParametersJoined
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction

namespace SKGap

def momentBall (R : ℝ) : Set (ProbabilityMeasure ℝ) :=
  {P | ∫⁻ x : ℝ, ENNReal.ofReal (x^2) ∂P ≤ ENNReal.ofReal R}

def momentCut (n : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => min (n:ℝ) (x^2))
    (by fun_prop) n (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Nat.cast_nonneg _) (sq_nonneg _))]
      exact min_le_left _ _)

def momentClip {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => max (-(n:ℝ)) (min (n:ℝ) (f x)))
    (by fun_prop) n (fun x => by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨le_max_left _ _, max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_left _ _)⟩)

end SKGap

namespace SKGap
open Filter
open scoped Topology

lemma gaussian_affine_hasLaw (d : ℝ) (s : ℝ≥0) :
    HasLaw (fun x : ℝ => d + sqrt s*x) (gaussianReal d s) (gaussianReal 0 1) := by
  have h := gaussianReal_const_add (gaussianReal_const_mul
    (HasLaw.id (μ := gaussianReal 0 1)) (sqrt s)) d
  have hv : (NNReal.mk ((sqrt (s:ℝ))^2) (sq_nonneg _) : ℝ≥0) = s := by
    ext
    exact sq_sqrt s.coe_nonneg
  simp only [id_eq, mul_zero, zero_add, mul_one] at h
  rw [hv] at h
  exact h

def gaussianAverage (f : ℝ → ℝ) (d s : ℝ) : ℝ := ∫ x, f (d + sqrt s*x) ∂gaussianReal 0 1

lemma gaussianAverage_eq_integral {f : ℝ → ℝ} (hf : Continuous f) (d : ℝ) {s : ℝ}
    (hs : 0 ≤ s) : gaussianAverage f d s = ∫ y, f y ∂gaussianReal d s.toNNReal := by
  have h := (gaussian_affine_hasLaw d s.toNNReal).integral_comp hf.aestronglyMeasurable
  simpa only [gaussianAverage, Function.comp_def, Real.coe_toNNReal s hs] using h

lemma integrable_gaussian_comp_of_bound {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (d s : ℝ) :
    Integrable (fun x => f (d+sqrt s*x)) (gaussianReal 0 1) :=
  Integrable.of_bound (by fun_prop) C (ae_of_all _ (fun x => hC _))

lemma continuous_gaussianAverage {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) : Continuous (fun p : ℝ×ℝ => gaussianAverage f p.1 p.2) := by
  apply continuous_of_dominated (bound := fun _ => C)
  · intro p
    exact (by fun_prop : Continuous (fun x : ℝ => f (p.1+sqrt p.2*x))).aestronglyMeasurable
  · intro p
    exact ae_of_all _ (fun x => hC _)
  · exact integrable_const _
  · exact ae_of_all _ (fun x => by fun_prop)
end SKGap

namespace SKGap
@[fun_prop] theorem continuous_tanh : Continuous tanh :=
  continuous_iff_continuousAt.mpr (fun y => (hasDerivAt_tanh y).continuousAt)
end SKGap

namespace SKGap

abbrev ScalarPoint := ProbabilityMeasure ℝ × (ℝ × ℝ)

def scalarM (P : ProbabilityMeasure ℝ) : ℝ := ∫ x, tanh x ∂P

def scalarQMoment (P : ProbabilityMeasure ℝ) : ℝ := ∫ x, tanh x^2 ∂P

def scalarD (j : ℝ) (p : ScalarPoint) : ℝ := p.2.1+j*scalarM p.1

def scalarS (j : ℝ) (p : ScalarPoint) : ℝ := p.2.1+p.2.2^2+j*scalarQMoment p.1

def scalarA (j : ℝ) (p : ScalarPoint) : ℝ :=
  (∫ x, x*tanh x ∂p.1) - scalarD j p*scalarM p.1

def scalarPsi (j : ℝ) (p : ScalarPoint) : ℝ :=
  j*(scalarA j p-scalarS j p*(1-scalarQMoment p.1))^2 /
    (2*scalarS j p*(scalarS j p+j*scalarQMoment p.1))

def scalarMomentDomain (R : ℝ) : Set ScalarPoint := momentBall R ×ˢ univ

def scalarLogMoment (f : ℝ →ᵇ ℝ) (d s : ℝ) : ℝ :=
  log (gaussianAverage (fun x => exp (f x)) d s)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PhiFrechet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology
namespace SKGap.Stein

abbrev Triple := ℝ × (ℝ × ℝ)
def eval3 (F : ℝ→ℝ→ℝ→ℝ) (x : Triple) : ℝ := F x.1 x.2.1 x.2.2

def grad2 (a b : ℝ) : (ℝ×ℝ)→L[ℝ]ℝ :=
  (ContinuousLinearMap.toSpanSingleton ℝ a).coprod (ContinuousLinearMap.toSpanSingleton ℝ b)
def grad3 (a b c : ℝ) : Triple→L[ℝ]ℝ :=
  (ContinuousLinearMap.toSpanSingleton ℝ a).coprod (grad2 b c)

namespace KernelExpr

def gradient (f : KernelExpr) (x : Triple) : Triple→L[ℝ]ℝ :=
  grad3 (eval3 f.dz.eval x) (eval3 f.dr.eval x) (eval3 f.da.eval x)

end KernelExpr

def strip (R : ℝ) : Set Triple := {x | |x.2.2|≤R}

namespace KernelExpr

def dBudget (f : KernelExpr) (R : ℝ) : ℝ :=
  (f.dz.mass+f.dr.mass+f.da.mass)*Real.exp (R/2)

def ddBudget (f : KernelExpr) (R : ℝ) : ℝ :=
  f.dz.dBudget R+f.dr.dBudget R+f.da.dBudget R
end KernelExpr

namespace RatioExpr

def gradient (f : RatioExpr) (x : Triple) : Triple→L[ℝ]ℝ :=
  grad3 (eval3 (f.d .z).eval x) (eval3 (f.d .r).eval x) (eval3 (f.d .a).eval x)

def dBudget (f : RatioExpr) : ℝ := (f.d .z).mass+(f.d .r).mass+(f.d .a).mass
def ddBudget (f : RatioExpr) : ℝ := (f.d .z).dBudget+(f.d .r).dBudget+(f.d .a).dBudget
end RatioExpr
end SKGap.Stein

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
namespace SKGap
abbrev MatrixCoordinates (ι : Type*) := (ι × ι) ⊕ ι

variable {ι : Type*}

def goeMatrix (r : ℝ) (g : MatrixCoordinates ι → ℝ) : Matrix ι ι ℝ :=
  fun i k => sqrt (2*r)/2 * (g (.inl (i,k)) + g (.inl (k,i)))

variable [Fintype ι]

def rawCoordinateMatrix (g : MatrixCoordinates ι → ℝ) : Matrix ι ι ℝ :=
  fun i k => g (.inl (i,k))

variable [DecidableEq ι]

def symmetricElementary (a b : ι) : Matrix ι ι ℝ :=
  Matrix.single a b 1+Matrix.single b a 1

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_OpNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def opNorm (M : Matrix ι ι ℝ) : ℝ := ‖M.toEuclideanLin.toContinuousLinearMap‖
def colVec (M : Matrix ι ι ℝ) (k : ι) : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => M i k)

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_FrobeniusSq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
namespace SKGap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma frobenius_sq (M : Matrix ι ι ℝ) : ‖M‖^2 = ∑ i,∑ k, (M i k)^2 := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two, Real.norm_eq_abs,sq_abs]
  rw [← Real.sqrt_eq_rpow,Real.sq_sqrt]
  positivity

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixEntryCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
namespace SKGap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrix_entry_le_frobenius (M : Matrix ι ι ℝ) (i k : ι) : |M i k| ≤ ‖M‖ := by
  have h₁ : (M i k)^2 ≤ ∑ j, (M i j)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ k)
  have h₂ : (∑ j, (M i j)^2) ≤ ∑ a,∑ j, (M a j)^2 :=
    Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) (Finset.mem_univ i)
  have hh : (M i k)^2 ≤ ‖M‖^2 := by rw [frobenius_sq]; exact h₁.trans h₂
  nlinarith only [hh,sq_abs (M i k),abs_nonneg (M i k),norm_nonneg M]

noncomputable def matrixEntryCLM (i k : ι) : Matrix ι ι ℝ →L[ℝ] ℝ :=
  ({ toFun := fun M => M i k
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : Matrix ι ι ℝ →ₗ[ℝ] ℝ).mkContinuous 1
      (fun M => by simpa [Real.norm_eq_abs] using! matrix_entry_le_frobenius M i k)

noncomputable def diagonalVector (M : Matrix ι ι ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => M i i)

end SKGap

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixSeminorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def offDiagonalVector (M : Matrix ι ι ℝ) : PiLp 4 (fun _ : ι×ι=>ℝ) :=
  WithLp.toLp 4 (fun p=>if p.1=p.2 then 0 else M p.1 p.2)
def diagonalSeminorm (M : Matrix ι ι ℝ) : ℝ := ‖diagonalVector M‖
def offDiagonalSeminorm (M : Matrix ι ι ℝ) : ℝ := ‖offDiagonalVector M‖

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma diagonalVector_sub (M N : Matrix ι ι ℝ) : diagonalVector (M-N)=diagonalVector M-diagonalVector N := by rfl
omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma diagonalVector_add (M N : Matrix ι ι ℝ) : diagonalVector (M+N)=diagonalVector M+diagonalVector N := by rfl
omit [Fintype ι] in
@[simp] lemma offDiagonalVector_sub (M N : Matrix ι ι ℝ) : offDiagonalVector (M-N)=offDiagonalVector M-offDiagonalVector N := by
  ext p
  simp only [offDiagonalVector,WithLp.ofLp_toLp,PiLp.sub_apply]
  split_ifs <;> simp
omit [Fintype ι] in
@[simp] lemma offDiagonalVector_add (M N : Matrix ι ι ℝ) : offDiagonalVector (M+N)=offDiagonalVector M+offDiagonalVector N := by
  ext p
  simp only [offDiagonalVector,WithLp.ofLp_toLp,PiLp.add_apply]
  split_ifs <;> simp

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_DiscreteMatrixCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Primary
open SKGap Matrix
variable {n : ℕ}

def derivativeMatrix (F : VectorFields n) (x : Spin n) : Interaction n :=
  fun i k => halfDiff k (fun y => F y i) x

def ShapeBound (M : Interaction n) (C : ℝ) : Prop :=
  SKGap.opNorm M ≤ C ∧ SKGap.diagonalSeminorm M ≤ C ∧ SKGap.offDiagonalSeminorm M ≤ C

def derivativeVector (f : Spin n→ℝ) (x : Spin n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun k => halfDiff k f x)

def siteMean (F : VectorFields n) (x : Spin n) : ℝ := (∑ i,F x i)/(n:ℝ)

end SKGapCutoff.Primary
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

abbrev Args := ι⊕κ→ℝ

def localArgs (H : ι→VectorFields n) (θ : κ→Spin n→ℝ) (x : Spin n) (i : Fin n) : Args (ι:=ι) (κ:=κ) :=
  Sum.elim (fun l=>H l x i) (fun α=>θ α x)

def partialAt (T : Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ) (l : ι⊕κ) : ℝ := T (Pi.single l 1)

def coefficient (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ) : VectorFields n :=
  fun x i=>F i (localArgs H θ x i)

def localPartial (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (l : ι⊕κ) : VectorFields n := fun x i=>partialAt (F' i (localArgs H θ x i)) l

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Quadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
namespace SKGap.ComplexSpectral
variable {ι : Type*} [Fintype ι]

def quadratic (M : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) : ℝ :=
  (dotProduct (star x.ofLp) (M *ᵥ x.ofLp)).re

def unitSphere (ι : Type*) [Fintype ι] : Set (EuclideanSpace ℂ ι) := Metric.sphere 0 1

def lowerRayleigh (M : Matrix ι ι ℂ) : ℝ := sInf (quadratic M '' unitSphere ι)

end SKGap.ComplexSpectral

end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ExpDuhamel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
open MeasureTheory Set NormedSpace
open scoped Topology

open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap
namespace ComplexMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev lin (M : Matrix ι ι ℂ) := M.toEuclideanLin.toContinuousLinearMap
noncomputable def opNorm (M : Matrix ι ι ℂ) : ℝ := ‖lin M‖
noncomputable def colVec (M : Matrix ι ι ℂ) (k : ι) : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i => M i k)

lemma frobenius_sq (M : Matrix ι ι ℂ) : ‖M‖^2 = ∑ i,∑ k, ‖M i k‖^2 := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow,Real.sq_sqrt]
  positivity

lemma frobenius_col_sq (M : Matrix ι ι ℂ) : ‖M‖^2 = ∑ k, ‖colVec M k‖^2 := by
  rw [frobenius_sq,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp [EuclideanSpace.norm_sq_eq,colVec]

lemma colVec_mul (M N : Matrix ι ι ℂ) (k : ι) :
    colVec (M*N) k = lin M (colVec N k) := by ext i; rfl

lemma lin_mul (M N : Matrix ι ι ℂ) : lin (M*N) = lin M * lin N := by
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg (fun T : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι => T x)
    (Matrix.toLpLin_mul 2 2 2 M N)

lemma lin_one : lin (1 : Matrix ι ι ℂ) = 1 := by
  ext x i
  change (Matrix.mulVec 1 (WithLp.ofLp x)) i = x i
  simp

lemma lin_adjoint (M : Matrix ι ι ℂ) : lin Mᴴ = (lin M).adjoint := by
  rw [lin,Matrix.toEuclideanLin_conjTranspose_eq_adjoint,LinearMap.adjoint_toContinuousLinearMap]

lemma lin_unitary (U : Matrix ι ι ℂ) (hU : U ∈ unitary (Matrix ι ι ℂ)) :
    lin U ∈ unitary (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) := by
  change (lin U).adjoint * lin U = 1 ∧ lin U * (lin U).adjoint = 1
  rw [← lin_adjoint,← lin_mul,← lin_mul]
  constructor
  · rw [show Uᴴ * U = 1 from Unitary.star_mul_self_of_mem hU,lin_one]
  · rw [show U * Uᴴ = 1 from Unitary.mul_star_self_of_mem hU,lin_one]

lemma frobenius_unitary_mul (U M : Matrix ι ι ℂ) (hU : U ∈ unitary (Matrix ι ι ℂ)) :
    ‖U*M‖ = ‖M‖ := by
  have hh : ‖U*M‖^2 = ‖M‖^2 := by
    rw [frobenius_col_sq,frobenius_col_sq]
    apply Finset.sum_congr rfl
    intro k _
    rw [colVec_mul,ContinuousLinearMap.norm_map_of_mem_unitary (lin_unitary U hU)]
  nlinarith [norm_nonneg (U*M),norm_nonneg M]

lemma frobenius_mul_unitary (M U : Matrix ι ι ℂ) (hU : U ∈ unitary (Matrix ι ι ℂ)) :
    ‖M*U‖ = ‖M‖ := by
  rw [← Matrix.frobenius_norm_conjTranspose (M*U),Matrix.conjTranspose_mul]
  rw [frobenius_unitary_mul Uᴴ Mᴴ (Unitary.star_mem hU),Matrix.frobenius_norm_conjTranspose]

end ComplexMatrix
end SKGap

namespace SKGap.ComplexMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def linEquiv : Matrix ι ι ℂ ≃ₗ[ℂ] (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
  Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap

def linHom : Matrix ι ι ℂ →+* (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) where
  toFun := lin
  map_one' := lin_one
  map_mul' := lin_mul
  map_zero' := linEquiv.map_zero
  map_add' := linEquiv.map_add

lemma continuous_lin : Continuous (lin : Matrix ι ι ℂ → _) :=
  (linEquiv (ι := ι)).toLinearMap.continuous_of_finiteDimensional

end SKGap.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LinSub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
open MeasureTheory Set NormedSpace
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ComplexMatrix

open MeasureTheory Set NormedSpace
open scoped Topology FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance instContinuousENormMatrixComplex_solutions : ContinuousENorm (Matrix ι ι ℂ) :=
  @SeminormedAddGroup.toContinuousENorm _ Matrix.frobeniusSeminormedAddCommGroup.toSeminormedAddGroup

noncomputable def imaginary (t : ℝ) (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ((t : ℂ)*Complex.I) • M

noncomputable def kernelMatrix (g : ℝ → ℂ) (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∫ t : ℝ, g t • exp (imaginary t M)

end SKGap.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_EntryLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
open MeasureTheory Set NormedSpace
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ComplexMatrix

section
open MeasureTheory Set NormedSpace
open scoped Topology FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance instContinuousENormMatrixComplex_solutions_1 : ContinuousENorm (Matrix ι ι ℂ) :=
  @SeminormedAddGroup.toContinuousENorm _ Matrix.frobeniusSeminormedAddCommGroup.toSeminormedAddGroup

def entryLM (i j : ι) : Matrix ι ι ℂ →ₗ[ℂ] ℂ where
  toFun := fun M => M i j
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def entryCLM (i j : ι) : Matrix ι ι ℂ →L[ℂ] ℂ := (entryLM i j).toContinuousLinearMap

def conjugate (U : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ _ U

def conjugateCLM (U : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ :=
  (conjugate U).toAlgEquiv.toLinearMap.toContinuousLinearMap

noncomputable def schwartzMatrix (f : 𝓢(ℝ, ℂ)) (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  kernelMatrix ((𝓕 f : 𝓢(ℝ,ℂ)) : ℝ → ℂ) ((2*Real.pi : ℝ) • M)

end

open MeasureTheory Set NormedSpace
open scoped Topology FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def linCLM : Matrix ι ι ℂ →L[ℂ] (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
  (linEquiv (ι := ι)).toLinearMap.toContinuousLinearMap

end SKGap.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_FourierMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
open MeasureTheory Set NormedSpace
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ComplexMatrix
open MeasureTheory NormedSpace
open scoped FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def fourierMoment (f : 𝓢(ℝ,ℂ)) (k : ℕ) : ℝ :=
  ∫ t : ℝ, ‖(𝓕 f) t‖*|t|^k

lemma fourierMoment_nonneg (f : 𝓢(ℝ,ℂ)) (k : ℕ) : 0 ≤ fourierMoment f k := by
  apply integral_nonneg
  intro t
  positivity

end SKGap.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_OpNormKernelMatrixSub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
open MeasureTheory Set NormedSpace
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ComplexMatrix

section
open MeasureTheory NormedSpace
open scoped FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance instContinuousENormMatrixComplex_solutions_3 : ContinuousENorm (Matrix ι ι ℂ) :=
  @SeminormedAddGroup.toContinuousENorm _ Matrix.frobeniusSeminormedAddCommGroup.toSeminormedAddGroup

end

end SKGap.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SandShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ComplexMatrix
open scoped FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sandShift (B D M : Matrix ι ι ℂ) : Matrix ι ι ℂ := B-D*M*D

omit [DecidableEq ι] in
lemma sandShift_hermitian (B D M : Matrix ι ι ℂ) (hB : Bᴴ = B) (hD : Dᴴ = D) (hM : Mᴴ = M) :
    (sandShift B D M)ᴴ = sandShift B D M := by
  simp [sandShift,Matrix.conjTranspose_mul,hB,hD,hM,mul_assoc]

end SKGap.ComplexMatrix

noncomputable section
open Set Real
open scoped Topology
namespace SKGap
section Projection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure ClosedConvexNonempty (K : Set E) : Prop where
  nonempty : K.Nonempty
  complete : IsComplete K
  convex : Convex ℝ K

noncomputable def convexProject {K : Set E} (hK : ClosedConvexNonempty K) (x : E) : E :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex hK.nonempty hK.complete hK.convex x)

end Projection
end SKGap

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Vectorize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
namespace SKGap.ComplexMatrix
open Set
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def vectorize : Matrix ι ι ℂ →ₗ[ℝ] EuclideanSpace ℂ (ι × ι) where
  toFun M := WithLp.toLp 2 (fun p => M p.1 p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma vectorize_norm (M : Matrix ι ι ℂ) : ‖vectorize M‖ = ‖M‖ := by
  have hh : ‖vectorize M‖^2 = ‖M‖^2 := by
    rw [EuclideanSpace.norm_sq_eq,frobenius_sq]
    change (∑ p : ι × ι, ‖M p.1 p.2‖^2) = ∑ i, ∑ k, ‖M i k‖^2
    exact Fintype.sum_prod_type _
  nlinarith [norm_nonneg (vectorize M),norm_nonneg M]

noncomputable instance frobeniusInnerProduct : InnerProductSpace ℝ (Matrix ι ι ℂ) where
  inner M N := inner ℝ (vectorize M) (vectorize N)
  norm_sq_eq_re_inner M := by
    change ‖M‖^2 = inner ℝ (vectorize M) (vectorize M)
    rw [real_inner_self_eq_norm_sq,vectorize_norm]
  conj_inner_symm M N := by simp only [conj_trivial]; exact real_inner_comm _ _
  add_left M N P := by rw [map_add,inner_add_left]
  smul_left M N r := by rw [map_smul,inner_smul_left]

noncomputable def hermitianBall (R : ℝ) : Set (Matrix ι ι ℂ) :=
  {M | Mᴴ = M ∧ opNorm M ≤ R}

lemma hermitianBall_closed (R : ℝ) : IsClosed (hermitianBall (ι := ι) R) := by
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop : Continuous (fun M : Matrix ι ι ℂ => Mᴴ)) continuous_id
  · exact isClosed_le continuous_lin.norm continuous_const

lemma hermitianBall_convex (R : ℝ) : Convex ℝ (hermitianBall (ι := ι) R) := by
  intro M hM N hN a b ha hb hab
  constructor
  · simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_smul,hM.1,hN.1,star_trivial]
  · have he : lin (a • M+b • N) = a • lin M+b • lin N := by
      exact (linEquiv (ι := ι)).toLinearMap.restrictScalars ℝ |>.map_add _ _ |>.trans
        (by rw [LinearMap.map_smul,LinearMap.map_smul]; rfl)
    change ‖lin (a • M+b • N)‖ ≤ R
    rw [he]
    calc
      _ ≤ ‖a • lin M‖+‖b • lin N‖ := norm_add_le _ _
      _ = a*opNorm M+b*opNorm N := by simp [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb,opNorm]
      _ ≤ a*R+b*R := add_le_add (mul_le_mul_of_nonneg_left hM.2 ha) (mul_le_mul_of_nonneg_left hN.2 hb)
      _ = R := by rw [← add_mul,hab,one_mul]

lemma hermitianBall_good {R : ℝ} (hR : 0 ≤ R) : SKGap.ClosedConvexNonempty (hermitianBall (ι := ι) R) where
  nonempty := ⟨0,by simp [hermitianBall,opNorm,lin,hR]⟩
  complete := (hermitianBall_closed R).isComplete
  convex := by convert hermitianBall_convex (ι := ι) R using 0

noncomputable def matrixProject (R : ℝ) (hR : 0 ≤ R) : Matrix ι ι ℂ → Matrix ι ι ℂ :=
  SKGap.convexProject (hermitianBall_good hR)

end SKGap.ComplexMatrix

namespace SKGap.ComplexMatrix
open scoped FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def truncatedG (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R)
    (B D M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  D*schwartzMatrix f (sandShift B D (matrixProject R hR M))*D

end SKGap.ComplexMatrix

namespace SKGap.ComplexMatrix
open scoped SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fl1 (f : 𝓢(ℝ,ℂ)) : ℝ := 2*Real.pi*fourierMoment f 1
def fl2 (f : 𝓢(ℝ,ℂ)) : ℝ := (2*Real.pi)^2*fourierMoment f 2
lemma fl_nonneg (f : 𝓢(ℝ,ℂ)) : 0 ≤ fl1 f ∧ 0 ≤ fl2 f := by
  have h₁ := fourierMoment_nonneg f 1
  have h₂ := fourierMoment_nonneg f 2
  unfold fl1 fl2
  constructor <;> positivity

def diagonalChange (D D' : Matrix ι ι ℂ) : ℝ :=
  (opNorm D+opNorm D')*opNorm (D-D')
def shiftChange (R : ℝ) (B B' D D' : Matrix ι ι ℂ) : ℝ :=
  opNorm (B-B')+diagonalChange D D'*R
def gBound (f : 𝓢(ℝ,ℂ)) (D : Matrix ι ι ℂ) : ℝ :=
  opNorm D^2*fourierMoment f 0
def gLip (f : 𝓢(ℝ,ℂ)) (D : Matrix ι ι ℂ) : ℝ :=
  fl1 f*opNorm D^4
def gChange (f : 𝓢(ℝ,ℂ)) (R : ℝ) (B B' D D' : Matrix ι ι ℂ) : ℝ :=
  diagonalChange D D'*fourierMoment f 0+opNorm D'^2*fl1 f*shiftChange R B B' D D'
def gMixed (f : 𝓢(ℝ,ℂ)) (R : ℝ) (B B' D D' : Matrix ι ι ℂ) : ℝ :=
  diagonalChange D D'*fl1 f*opNorm D^2+
  opNorm D'^2*(fl1 f*diagonalChange D D'+fl2 f*(2*shiftChange R B B' D D')*opNorm D'^2)

noncomputable def truncatedK (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R)
    (B D C M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  1+truncatedG f R hR B D M*(matrixProject R hR M-C)

def kBound (f : 𝓢(ℝ,ℂ)) (R : ℝ) (D C : Matrix ι ι ℂ) : ℝ :=
  1+gBound f D*(R+opNorm C)
def kLip (f : 𝓢(ℝ,ℂ)) (R : ℝ) (D C : Matrix ι ι ℂ) : ℝ :=
  gLip f D*(R+opNorm C)+gBound f D
def kMixed (f : 𝓢(ℝ,ℂ)) (R : ℝ) (B B' D D' C C' : Matrix ι ι ℂ) : ℝ :=
  gMixed f R B B' D D'*(R+opNorm C)+gLip f D'*opNorm (C-C')+gChange f R B B' D D'

end SKGap.ComplexMatrix

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_LiftMatrix
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
namespace SKGap.RealComplex
open scoped Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def liftMatrix (M : Matrix ι ι ℝ) : Matrix ι ι ℂ := M.map Complex.ofReal
abbrev clin (M : Matrix ι ι ℂ) := M.toEuclideanLin.toContinuousLinearMap
abbrev rlin (M : Matrix ι ι ℝ) := M.toEuclideanLin.toContinuousLinearMap

def reVec (x : EuclideanSpace ℂ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => (x i).re)
def imVec (x : EuclideanSpace ℂ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => (x i).im)
def liftVec (x : EuclideanSpace ℝ ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => (x i : ℂ))

end SKGap.RealComplex

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RealPart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
namespace SKGap.RealComplex
open scoped Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def realPart (M : Matrix ι ι ℂ) : Matrix ι ι ℝ := M.map Complex.re

end SKGap.RealComplex

namespace SKGap.RealComplex
open scoped Matrix.Norms.Frobenius SchwartzMap ComplexOrder
open SKGap.ComplexMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def realTruncatedK (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R)
    (D C M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  realPart (truncatedK f R hR (1+liftMatrix D*liftMatrix C*liftMatrix D)
    (liftMatrix D) (liftMatrix C) (liftMatrix M))

end SKGap.RealComplex

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Conjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap.ComplexMatrix
open Matrix
open scoped Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma conjugate_frobenius (U : unitary (Matrix ι ι ℂ)) (M : Matrix ι ι ℂ) :
    ‖conjugate U M‖ = ‖M‖ := by
  change ‖(U : Matrix ι ι ℂ)*M*(U : Matrix ι ι ℂ)ᴴ‖ = _
  rw [frobenius_mul_unitary ((U : Matrix ι ι ℂ)*M) ((U : Matrix ι ι ℂ)ᴴ) (Unitary.star_mem U.property),
    frobenius_unitary_mul _ _ U.property]

noncomputable def conjugateIsometry (U : unitary (Matrix ι ι ℂ)) :
    Matrix ι ι ℂ ≃ₗᵢ[ℝ] Matrix ι ι ℂ where
  toLinearEquiv := (conjugate U).toAlgEquiv.toLinearEquiv.restrictScalars ℝ
  norm_map' := conjugate_frobenius U

end SKGap.ComplexMatrix
end
end

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory
open RealComplex ComplexMatrix
open scoped Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def signConjugate (s : ι → ℝ) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i k => s i*s k*M i k

noncomputable def signUnitary (s : ι → ℝ) (hs : ∀ i, s i^2=1) :
    unitary (Matrix ι ι ℂ) :=
  ⟨diagonal (fun i => (s i : ℂ)), by
    have hh : ∀ i, (s i : ℂ)*(s i : ℂ)=1 := by
      intro i
      exact_mod_cast (show s i*s i=1 by nlinarith [hs i])
    change (diagonal (fun i => (s i : ℂ)))ᴴ*diagonal (fun i => (s i : ℂ))=1 ∧
      diagonal (fun i => (s i : ℂ))*(diagonal (fun i => (s i : ℂ)))ᴴ=1
    simp only [diagonal_conjTranspose,Pi.star_apply,Complex.star_def,Complex.conj_ofReal,
      diagonal_mul_diagonal,hh,diagonal_one,and_self]⟩

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianSign
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable def gaussianSignEquiv {κ : Type*} (q : κ → ℝ) (hq : ∀ b, q b^2=1) :
    (κ → ℝ) ≃ᵐ (κ → ℝ) where
  toFun g b := q b*g b
  invFun g b := q b*g b
  left_inv g := by ext b; dsimp; rw [← mul_assoc,← sq,hq b,one_mul]
  right_inv g := by ext b; dsimp; rw [← mul_assoc,← sq,hq b,one_mul]
  measurable_toFun := by change Measurable (fun g : κ → ℝ => fun b => q b*g b); fun_prop
  measurable_invFun := by change Measurable (fun g : κ → ℝ => fun b => q b*g b); fun_prop

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def goeSign (s : ι → ℝ) : MatrixCoordinates ι → ℝ :=
  Sum.elim (fun p => s p.1*s p.2) (fun _ => 1)

omit [Fintype ι] [DecidableEq ι] in
lemma goeSign_sq (s : ι → ℝ) (hs : ∀ i, s i^2=1) (b : MatrixCoordinates ι) :
    goeSign s b^2=1 := by
  rcases b with ⟨i,k⟩|i
  · simp only [goeSign,Sum.elim_inl,mul_pow,hs,one_mul]
  · norm_num [goeSign]

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Bilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixBilinear (M : Matrix ι ι ℝ) (u v : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, ∑ k, u i*M i k*v k

end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Error
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.SourceError
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def traceAbsolute (P E : Matrix ι ι ℝ) : ℝ := ∑i,∑k,|P k i| * |E i k|

end SKGap.SourceError

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Operation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

def vectorNorm (u : Fin n→ℝ) : ℝ := ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_Trace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.SourceError
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

structure SegmentRegular (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (x : Spin n) (C : ℝ) : Prop where
  nonneg : 0≤C
  deriv : ∀i k t, t∈Set.Icc (0:ℝ) 1→HasFDerivAt (F i)
    (F' i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)))
    (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))
  bound : ∀i k t, t∈Set.Icc (0:ℝ) 1→
    ‖F' i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))‖≤C
  lip : ∀i k t, t∈Set.Icc (0:ℝ) 1→
    ‖F' i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))-
      F' i (localArgs H θ x i)‖≤C*‖t • (localArgs H θ (flip x k) i-localArgs H θ x i)‖

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Letter
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.Noncrossing
universe u v

inductive Letter (D : Type*) where
  | diag : D → Letter D
  | noise : Letter D
  deriving DecidableEq

inductive Diagram (D : Type*) where
  | nil : Diagram D
  | diag : D → Diagram D → Diagram D
  | arch : Diagram D → Diagram D → Diagram D
  deriving DecidableEq

namespace Diagram
variable {D : Type*}

def word : Diagram D → List (Letter D)
  | nil => []
  | diag a d => .diag a :: d.word
  | arch a b => .noise :: (a.word ++ (.noise :: b.word))

def size : Diagram D → ℕ
  | nil => 0
  | diag _ d => d.size+1
  | arch a b => a.size+b.size+2

@[simp] lemma word_length (d : Diagram D) : d.word.length = d.size := by
  induction d with
  | nil => rfl
  | diag a d ih => simp [word, size, ih]
  | arch a b ia ib => simp [word, size, ia, ib]; omega

def insert (outer : Diagram D) (p : ℕ) (inside : Diagram D) : Diagram D :=
  if p=0 then .arch inside outer else
    match outer with
    | nil => .arch inside .nil
    | diag a d => .diag a (d.insert (p-1) inside)
    | arch a b =>
      if p ≤ a.size+1 then .arch (a.insert (p-1) inside) b
      else .arch a (b.insert (p-(a.size+2)) inside)

@[simp] lemma insert_zero (d e : Diagram D) : d.insert 0 e = .arch e d := by
  cases d <;> simp [insert]

lemma insert_size (d e : Diagram D) (p : ℕ) :
    (d.insert p e).size = d.size+e.size+2 := by
  induction d generalizing p with
  | nil => simp [insert, size]
  | diag a d ih =>
    by_cases hp : p=0
    · simp [insert, hp, size]; omega
    · simp [insert, hp, size, ih]; omega
  | arch a b ia ib =>
    by_cases hp : p=0
    · simp [insert, hp, size]; omega
    · simp only [insert, hp, ↓reduceIte]
      split_ifs <;> simp only [size, ia, ib] <;> omega

lemma insert_word (d e : Diagram D) (p : ℕ) (hp : p≤d.size) :
    (d.insert p e).word = d.word.take p ++
      (.noise :: (e.word ++ (.noise :: d.word.drop p))) := by
  induction d generalizing p with
  | nil => have : p=0 := by simpa [size] using hp
           subst p; simp [insert, word]
  | diag a d ih =>
    cases p with
    | zero => simp [word]
    | succ p =>
      have h : p≤d.size := by simpa [size] using hp
      simpa [insert, word, List.take_succ_cons, List.drop_succ_cons] using
        congrArg (List.cons (.diag a)) (ih p h)
  | arch a b ia ib =>
    cases p with
    | zero => simp [word]
    | succ p =>
      by_cases h : p≤a.size
      · have he := ia p h
        simp only [insert, Nat.succ_ne_zero, ↓reduceIte, Nat.add_one_sub_one]
        rw [ite_eq_left (by omega), word, he]
        simp [word, List.take_append_of_le_length (l₁ := a.word) (i := p) (by simpa using h),
          List.drop_append_of_le_length (l₁ := a.word) (i := p) (by simpa using h), List.append_assoc]
      · have h' : p-(a.size+1)≤b.size := by simp only [size] at hp; omega
        have he := ib (p-(a.size+1)) h'
        simp only [insert, Nat.succ_ne_zero, ↓reduceIte]
        rw [ite_eq_right (by omega)]
        have hh : p+1-(a.size+2)=p-(a.size+1) := by omega
        rw [hh, word, he]
        simp only [word, List.take_succ_cons, List.drop_succ_cons]
        rw [List.take_append, List.drop_append]
        have hle : a.word.length≤p := by simp; omega
        rw [List.take_of_length_le hle, List.drop_eq_nil_of_le hle]
        simp only [List.nil_append, word_length]
        have hk : p-a.size = (p-(a.size+1))+1 := by omega
        rw [hk]
        simp [List.append_assoc]

structure Cut (D : Type*) where
  start : ℕ
  inside : Diagram D
  outside : Diagram D
  closing : Bool
  deriving DecidableEq

def Cut.diag (a : D) (c : Cut D) : Cut D :=
  ⟨c.start+1,c.inside,.diag a c.outside,c.closing⟩
def Cut.inner (b : Diagram D) (c : Cut D) : Cut D :=
  ⟨c.start+1,c.inside,.arch c.outside b,c.closing⟩
def Cut.tail (a : Diagram D) (c : Cut D) : Cut D :=
  ⟨a.size+2+c.start,c.inside,.arch a c.outside,c.closing⟩

def cut : Diagram D → ℕ → Option (Cut D)
  | nil, _ => none
  | diag _ _, 0 => none
  | diag a d, i+1 => (d.cut i).map (Cut.diag a)
  | arch a b, 0 => some ⟨0,a,b,false⟩
  | arch a b, i+1 =>
      if i<a.size then (a.cut i).map (Cut.inner b)
      else if i=a.size then some ⟨0,a,b,true⟩
      else (b.cut (i-(a.size+1))).map (Cut.tail a)

lemma cut_spec (d : Diagram D) (i : ℕ) (c : Cut D) (hc : d.cut i=some c) :
    c.start ≤ c.outside.size ∧
    i=c.start+(if c.closing then c.inside.size+1 else 0) ∧
    c.outside.insert c.start c.inside = d := by
  induction d generalizing i c with
  | nil => simp [cut] at hc
  | diag a d ih =>
    cases i with
    | zero => simp [cut] at hc
    | succ i =>
      simp only [cut, Option.map_eq_some_iff] at hc
      obtain ⟨e,he,rfl⟩ := hc
      obtain ⟨h1,h2,h3⟩ := ih i e he
      refine ⟨by simpa [Cut.diag,size] using h1, ?_, ?_⟩
      · cases hcl : e.closing <;>
          simp only [Cut.diag, hcl, Bool.false_eq_true, ↓reduceIte] at h2 ⊢ <;> omega
      · simpa [Cut.diag,insert] using congrArg (Diagram.diag a) h3
  | arch a b ia ib =>
    cases i with
    | zero =>
      simp only [cut,Option.some.injEq] at hc
      subst c; simp
    | succ i =>
      simp only [cut] at hc
      split_ifs at hc with hi he
      · obtain ⟨e,he,rfl⟩ := Option.map_eq_some_iff.mp hc
        obtain ⟨h1,h2,h3⟩ := ia i e he
        refine ⟨by simp only [Cut.inner,size]; omega, ?_, ?_⟩
        · cases hcl : e.closing <;>
          simp only [Cut.inner, hcl, Bool.false_eq_true, ↓reduceIte] at h2 ⊢ <;> omega
        · simp only [Cut.inner,insert,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,
            ↓reduceIte,Nat.add_one_sub_one]
          rw [ite_eq_left (by omega),h3]
      · simp only [Option.some.injEq] at hc
        subst c; simp [he]
      · obtain ⟨e,he',rfl⟩ := Option.map_eq_some_iff.mp hc
        obtain ⟨h1,h2,h3⟩ := ib (i-(a.size+1)) e he'
        refine ⟨by simp only [Cut.tail,size]; omega, ?_, ?_⟩
        · cases hcl : e.closing <;>
          simp only [Cut.tail, hcl, Bool.false_eq_true, ↓reduceIte] at h2 ⊢ <;> omega
        · simp only [Cut.tail,insert]
          rw [ite_eq_right (by omega), ite_eq_right (by omega)]
          rw [show a.size+2+e.start-(a.size+2)=e.start by omega, h3]

lemma cut_insert (d e : Diagram D) (p : ℕ) (hp : p≤d.size) (cl : Bool) :
    (d.insert p e).cut (p+(if cl then e.size+1 else 0)) =
      some ⟨p,e,d,cl⟩ := by
  induction d generalizing p with
  | nil =>
    have hh : p=0 := by simpa [size] using hp
    subst p
    cases cl <;> simp [insert,cut]
  | diag a d ih =>
    cases p with
    | zero => cases cl <;> simp [cut]
    | succ p =>
      have h : p≤d.size := by simpa [size] using hp
      have he := ih p h
      rw [show (Diagram.diag a d).insert (p+1) e = .diag a (d.insert p e) by simp [insert]]
      have hi : p+1+(if cl then e.size+1 else 0) = (p+(if cl then e.size+1 else 0))+1 := by omega
      rw [hi, cut, he]
      simp [Cut.diag]
  | arch a b ia ib =>
    cases p with
    | zero => cases cl <;> simp [cut]
    | succ p =>
      by_cases h : p≤a.size
      · have he := ia p h
        rw [show (a.arch b).insert (p+1) e = .arch (a.insert p e) b by
          simp [insert, show p+1≤a.size+1 by omega]]
        have hi : p+1+(if cl then e.size+1 else 0) = (p+(if cl then e.size+1 else 0))+1 := by omega
        rw [hi,cut,ite_eq_left]
        · rw [he]; simp [Cut.inner]
        · rw [insert_size]; cases cl <;> simp <;> omega
      · have hp' : p-(a.size+1)≤b.size := by simp only [size] at hp; omega
        have he := ib (p-(a.size+1)) hp'
        rw [show (a.arch b).insert (p+1) e = .arch a (b.insert (p-(a.size+1)) e) by
          simp [insert, show ¬p+1≤a.size+1 by omega,
            show p+1-(a.size+2)=p-(a.size+1) by omega]]
        have hi : p+1+(if cl then e.size+1 else 0) = (p+(if cl then e.size+1 else 0))+1 := by omega
        rw [hi,cut,ite_eq_right (by omega),ite_eq_right (by omega)]
        have hh : p+(if cl then e.size+1 else 0)-(a.size+1) =
            p-(a.size+1)+(if cl then e.size+1 else 0) := by omega
        rw [hh,he]
        simp only [Option.map_some,Cut.tail]
        congr 2
        omega

lemma cut_exists_iff (d : Diagram D) (i : ℕ) :
    (∃ c, d.cut i=some c) ↔ d.word[i]?=some .noise := by
  induction d generalizing i with
  | nil => simp [cut, word]
  | diag a d ih =>
    cases i with
    | zero => simp [cut,word]
    | succ i => simpa [cut,word,Option.map_eq_some_iff] using ih i
  | arch a b ia ib =>
    cases i with
    | zero => simp [cut,word]
    | succ i =>
      by_cases hi : i<a.size
      · have hi' : i<a.word.length := by simpa using hi
        simp only [cut,hi,↓reduceIte,word,List.getElem?_cons_succ]
        rw [List.getElem?_append_left hi']
        simpa [Option.map_eq_some_iff] using ia i
      · by_cases he : i=a.size
        · subst i
          simp [cut,word]
        · have hr : a.word.length ≤ i := by simp; omega
          have hh : i-a.size = (i-(a.size+1))+1 := by omega
          simp [cut,hi,he,word,List.getElem?_append_right hr,hh,ib,
            Option.map_eq_some_iff]

def labels (F : List (Letter D)) : Finset D := by
  classical
  exact (F.filterMap (fun l => match l with | .diag a => some a | .noise => none)).toFinset

@[simp] lemma labels_nil : labels ([] : List (Letter D)) = ∅ := rfl
@[simp] lemma labels_diag [DecidableEq D] (a : D) (F : List (Letter D)) :
    labels (.diag a::F) = Insert.insert a (labels F) := by
  ext x
  simp [labels]
@[simp] lemma labels_noise (F : List (Letter D)) : labels (.noise::F)=labels F := by
  simp [labels]
@[simp] lemma labels_append [DecidableEq D] (F G : List (Letter D)) : labels (F++G)=labels F∪labels G := by
  ext x
  simp [labels,List.filterMap_append]

def supply (A : Finset D) : ℕ → Finset (Diagram D)
  | 0 => {.nil}
  | n+1 => by
      classical
      exact {.nil} ∪ A.biUnion (fun a => (supply A n).image (.diag a)) ∪
        (supply A n).biUnion (fun a => (supply A n).image (.arch a))

lemma mem_supply (A : Finset D) (n : ℕ) (d : Diagram D)
    (hn : d.size≤n) (hA : labels d.word⊆A) : d∈supply A n := by
  classical
  induction n generalizing d with
  | zero =>
    cases d with
    | nil => simp [supply]
    | diag a d => simp [size] at hn
    | arch a b => simp [size] at hn
  | succ n ih =>
    cases d with
    | nil => simp [supply]
    | diag a d =>
      have ha : a∈A := hA (by simp [word])
      have hd : labels d.word⊆A := by
        intro x hx; apply hA; simp [word,hx]
      have hs : d.size≤n := by simpa [size] using hn
      simp only [supply,Finset.mem_union,Finset.mem_singleton,Finset.mem_biUnion,Finset.mem_image]
      exact Or.inl (Or.inr ⟨a,ha,d,ih d hs hd,rfl⟩)
    | arch a b =>
      have ha : labels a.word⊆A := by
        intro x hx; apply hA; simp [word,hx]
      have hb : labels b.word⊆A := by
        intro x hx; apply hA; simp [word,hx]
      have hs : a.size≤n ∧ b.size≤n := by simp only [size] at hn; omega
      simp only [supply,Finset.mem_union,Finset.mem_biUnion,Finset.mem_image]
      exact Or.inr ⟨a,ih a hs.1 ha,b,ih b hs.2 hb,rfl⟩

def enumerate (F : List (Letter D)) : Finset (Diagram D) := by
  classical
  exact (supply (labels F) F.length).filter (fun d => d.word=F)

@[simp] theorem mem_enumerate (F : List (Letter D)) (d : Diagram D) :
    d∈enumerate F ↔ d.word=F := by
  classical
  simp only [enumerate,Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨mem_supply _ _ d (by rw [← word_length,h]) (by rw [h]),h⟩⟩

def Paired (F : List (Letter D)) := {d : Diagram D // d.word=F}

instance pairedFintype (F : List (Letter D)) : Fintype (Paired F) :=
  Fintype.ofFinset (enumerate F) (fun d => mem_enumerate F d)

def CutAt (F : List (Letter D)) (k : ℕ) :=
  {c : Cut D // c.start ≤ c.outside.size ∧
    k=c.start+(if c.closing then c.inside.size+1 else 0) ∧
    (c.outside.insert c.start c.inside).word=F}

def markedCut (d : Diagram D) (k : ℕ) (hk : d.word[k]?=some .noise) : Cut D :=
  Classical.choose ((cut_exists_iff d k).mpr hk)
lemma cut_markedCut (d : Diagram D) (k : ℕ) (hk : d.word[k]?=some .noise) :
    d.cut k=some (d.markedCut k hk) :=
  Classical.choose_spec ((cut_exists_iff d k).mpr hk)

def cutEquiv (F : List (Letter D)) (k : ℕ) (hk : F[k]?=some .noise) :
    Paired F ≃ CutAt F k where
  toFun d := by
    have hd : d.val.word[k]?=some .noise := by rw [d.property]; exact hk
    let c := d.val.markedCut k hd
    have hs := cut_spec d.val k c (cut_markedCut _ _ _)
    exact ⟨c,hs.1,hs.2.1,by rw [hs.2.2]; exact d.property⟩
  invFun c := ⟨c.val.outside.insert c.val.start c.val.inside,c.property.2.2⟩
  left_inv d := by
    apply Subtype.ext
    have hd : d.val.word[k]?=some .noise := by rw [d.property]; exact hk
    exact (cut_spec d.val k _ (cut_markedCut d.val k hd)).2.2
  right_inv c := by
    apply Subtype.ext
    have hc := cut_insert c.val.outside c.val.inside c.val.start c.property.1 c.val.closing
    rw [← c.property.2.1] at hc
    have hd : (c.val.outside.insert c.val.start c.val.inside).word[k]?=some .noise := by
      rw [c.property.2.2]; exact hk
    exact Option.some.inj ((cut_markedCut _ k hd).symm.trans hc)

@[ext]
structure PairShape (F : List (Letter D)) (k : ℕ) where
  before : List (Letter D)
  between : List (Letter D)
  after : List (Letter D)
  closing : Bool
  word_eq : F = before ++ (.noise :: (between ++ (.noise :: after)))
  mark_eq : k = before.length+(if closing then between.length+1 else 0)

lemma PairShape.length_bound {F : List (Letter D)} {k : ℕ} (s : PairShape F k) :
    s.before.length<F.length ∧ s.between.length<F.length := by
  rcases s with ⟨U,V,Q,cl,hF,hk⟩
  subst F
  simp only [List.length_append,List.length_cons]
  omega

lemma PairShape.before_eq_take {F : List (Letter D)} {k : ℕ} (s : PairShape F k) :
    s.before=F.take s.before.length := by
  rcases s with ⟨U,V,Q,cl,hF,hk⟩
  subst F
  simp
lemma PairShape.between_eq_take {F : List (Letter D)} {k : ℕ} (s : PairShape F k) :
    s.between=(F.drop (s.before.length+1)).take s.between.length := by
  rcases s with ⟨U,V,Q,cl,hF,hk⟩
  subst F
  simp
lemma PairShape.after_eq_drop {F : List (Letter D)} {k : ℕ} (s : PairShape F k) :
    s.after=F.drop (s.before.length+s.between.length+2) := by
  rcases s with ⟨U,V,Q,cl,hF,hk⟩
  subst F
  dsimp
  simp [show U.length+V.length+2=U.length+(V.length+2) by omega]

def PairShape.code {F : List (Letter D)} {k : ℕ} (s : PairShape F k) :
    Fin F.length × Fin F.length × Bool :=
  (⟨s.before.length,s.length_bound.1⟩,⟨s.between.length,s.length_bound.2⟩,s.closing)

lemma PairShape.code_injective (F : List (Letter D)) (k : ℕ) :
    Function.Injective (PairShape.code (F := F) (k := k)) := by
  intro a b h
  have h1 : a.before.length=b.before.length := congrArg (fun x => x.1.val) h
  have h2 : a.between.length=b.between.length := congrArg (fun x => x.2.1.val) h
  have h3 : a.closing=b.closing := congrArg (fun x => x.2.2) h
  apply PairShape.ext
  · rw [a.before_eq_take,b.before_eq_take,h1]
  · rw [a.between_eq_take,b.between_eq_take,h1,h2]
  · rw [a.after_eq_drop,b.after_eq_drop,h1,h2]
  · exact h3

instance pairShapeFinite (F : List (Letter D)) (k : ℕ) : Finite (PairShape F k) :=
  Finite.of_injective _ (PairShape.code_injective F k)
instance pairShapeFintype (F : List (Letter D)) (k : ℕ) : Fintype (PairShape F k) :=
  Fintype.ofFinite _

def Separated (F : List (Letter D)) (k : ℕ) :=
  Σ s : PairShape F k, Paired s.between × Paired (s.before++s.after)

instance separatedFintype (F : List (Letter D)) (k : ℕ) : Fintype (Separated F k) :=
  inferInstanceAs (Fintype (Σ s : PairShape F k, Paired s.between × Paired (s.before++s.after)))

def shapeOfCut {F : List (Letter D)} {k : ℕ} (c : CutAt F k) : PairShape F k where
  before := c.val.outside.word.take c.val.start
  between := c.val.inside.word
  after := c.val.outside.word.drop c.val.start
  closing := c.val.closing
  word_eq := c.property.2.2.symm.trans (insert_word _ _ _ c.property.1)
  mark_eq := by
    simp only [List.length_take,word_length,Nat.min_eq_left c.property.1]
    exact c.property.2.1

end Diagram
end SKGap.Noncrossing
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SeparateCut
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap.Noncrossing
universe u v
namespace Diagram
variable {D : Type*}

def separateCut {F : List (Letter D)} {k : ℕ} (c : CutAt F k) : Separated F k :=
  ⟨shapeOfCut c,⟨c.val.inside,rfl⟩,
    ⟨c.val.outside,(List.take_append_drop _ _).symm⟩⟩

def joinCut {F : List (Letter D)} {k : ℕ} (z : Separated F k) : CutAt F k := by
  have hb : z.1.before.length≤z.2.2.val.size := by
    rw [← word_length,z.2.2.property,List.length_append]
    omega
  refine ⟨⟨z.1.before.length,z.2.1.val,z.2.2.val,z.1.closing⟩,hb,?_,?_⟩
  · have hs : z.2.1.val.size=z.1.between.length := by rw [← word_length,z.2.1.property]
    simpa only [hs] using z.1.mark_eq
  · rw [insert_word _ _ _ hb,z.2.2.property,z.2.1.property]
    simpa using z.1.word_eq.symm

@[simp] lemma join_separate {F : List (Letter D)} {k : ℕ} (c : CutAt F k) :
    joinCut (separateCut c) = c := by
  apply Subtype.ext
  rcases c with ⟨⟨p,a,b,cl⟩,hp,hk,hF⟩
  dsimp [joinCut,separateCut,shapeOfCut]
  simp only [List.length_take,word_length,Nat.min_eq_left hp]

lemma pair_heq {α γ : Type u} {β δ : Type v} {a : α} {b : β} {c : γ} {d : δ}
    (ha : a ≍ c) (hb : b ≍ d) : (a,b) ≍ (c,d) := by
  cases ha
  cases hb
  rfl

@[simp] lemma separate_join {F : List (Letter D)} {k : ℕ} (z : Separated F k) :
    separateCut (joinCut z) = z := by
  rcases z with ⟨s,a,b⟩
  have hs : shapeOfCut (joinCut (⟨s,a,b⟩ : Separated F k)) = s := by
    apply PairShape.ext <;>
      simp [shapeOfCut,joinCut,a.property,b.property]
  apply Sigma.ext hs
  apply pair_heq
  · refine (Subtype.heq_iff_coe_eq (fun d => ?_)).mpr ?_
    · rw [hs]
    · rfl
  · refine (Subtype.heq_iff_coe_eq (fun d => ?_)).mpr ?_
    · rw [hs]
    · rfl

def separateEquiv (F : List (Letter D)) (k : ℕ) : CutAt F k ≃ Separated F k where
  toFun := separateCut
  invFun := joinCut
  left_inv := join_separate
  right_inv := separate_join

section Value
variable {ι : Type*} [Fintype ι]

def mean (a : ι→ℝ) : ℝ := (∑ i,a i)/(Fintype.card ι:ℝ)

def value (j : ℝ) : Diagram (ι→ℝ) → ι→ℝ
  | nil => fun _ => 1
  | diag a d => fun i => a i * d.value j i
  | arch a b => fun i => j * mean (a.value j) * b.value j i

def prediction (j : ℝ) (F : List (Letter (ι→ℝ))) (i : ι) : ℝ :=
  ∑ d : Paired F, d.val.value j i

end Value

end Diagram
end SKGap.Noncrossing

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_InverseDiagram
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing

inductive InverseDiagram where
  | empty
  | counterterm (rest : InverseDiagram)
  | arch (inside rest : InverseDiagram)
  deriving DecidableEq

namespace InverseDiagram

def degree : InverseDiagram → ℕ
  | .empty => 0
  | .counterterm d => d.degree + 1
  | .arch d e => d.degree + e.degree + 1

def blocks : InverseDiagram → List Bool
  | .empty => []
  | .counterterm d => false :: d.blocks
  | .arch d e => true :: (d.blocks ++ true :: e.blocks)

theorem blocks_degree (d : InverseDiagram) :
    ((d.blocks.map (fun b => if b then 1 else 2)).sum : ℕ) = 2 * d.degree := by
  induction d with
  | empty => rfl
  | counterterm d ih => simp only [blocks, List.map_cons, List.sum_cons, Bool.false_eq_true,
      ↓reduceIte, ih, degree]; omega
  | arch d e ihd ihe => simp only [blocks, List.map_cons, List.map_append, List.sum_cons,
      List.sum_append, ↓reduceIte, ihd, ihe, degree]; omega

def enumerate : ℕ → List InverseDiagram
  | 0 => [.empty]
  | n + 1 => (enumerate n).map .counterterm ++
      (List.finRange (n+1)).flatMap fun k =>
        (enumerate k.val).flatMap fun u =>
          (enumerate (n-k.val)).map (fun v => .arch u v)
termination_by n => n
decreasing_by all_goals omega

lemma mem_enumerate (d : InverseDiagram) (n : ℕ) : d ∈ enumerate n ↔ d.degree = n := by
  induction n using Nat.strong_induction_on generalizing d with
  | h n ih =>
    cases n with
    | zero =>
      cases d <;> simp [enumerate, degree]
    | succ n =>
      rw [enumerate]
      cases d with
      | empty => simp [degree]
      | counterterm d =>
        simpa [degree] using ih n (by omega) d
      | arch u v =>
        simp only [List.mem_append, List.mem_map, List.mem_flatMap]
        constructor
        · rintro (⟨d, -, he⟩ | ⟨k, -, u', hu', v', hv', he⟩)
          · cases he
          · cases he
            have hu := (ih k.val (by omega) u).mp hu'
            have hv := (ih (n-k.val) (by omega) v).mp hv'
            simp only [degree]
            omega
        · intro hd
          have hu : u.degree < n+1 := by simp only [degree] at hd; omega
          refine Or.inr ⟨⟨u.degree, hu⟩, List.mem_finRange _, u, (ih _ hu u).mpr rfl,
            v, (ih _ (by omega) v).mpr ?_, rfl⟩
          change v.degree = n - u.degree
          simp only [degree] at hd
          omega

variable {ι : Type*} [Fintype ι]

def average (x : ι → ℝ) : ℝ := (∑ i, x i) / Fintype.card ι

def value (j : ℝ) (a : ι → ℝ) : InverseDiagram → ι → ℝ
  | .empty, _ => 1
  | .counterterm d, i => -(j * average a) * a i * value j a d i
  | .arch u v, i => j * a i * average (fun k => a k * value j a u k) * value j a v i

def coefficient (j : ℝ) (a : ι → ℝ) (n : ℕ) (i : ι) : ℝ :=
  ((enumerate n).map (fun d => value j a d i)).sum

@[simp] lemma coefficient_zero (j : ℝ) (a : ι → ℝ) (i : ι) :
    coefficient j a 0 i = 1 := by simp [coefficient, enumerate, value]

@[simp] lemma average_zero : average (0 : ι → ℝ) = 0 := by simp [average]

end InverseDiagram
end SKGap.Noncrossing

end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Append
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
namespace SKGap.Noncrossing
namespace Diagram
variable {D E : Type*}

def append : Diagram D → Diagram D → Diagram D
  | .nil, e => e
  | .diag a d, e => .diag a (d.append e)
  | .arch a b, e => .arch a (b.append e)

@[simp] lemma append_word (d e : Diagram D) : (d.append e).word = d.word ++ e.word := by
  induction d with
  | nil => rfl
  | diag a d ih => simp [append,word,ih]
  | arch a b ia ib => simp [append,word,ib,List.append_assoc]

@[simp] lemma append_nil (d : Diagram D) : d.append .nil = d := by
  induction d with
  | nil => rfl
  | diag a d ih => simp [append,ih]
  | arch a b ia ib => simp [append,ib]

def map (f : D → E) : Diagram D → Diagram E
  | .nil => .nil
  | .diag a d => .diag (f a) (d.map f)
  | .arch a b => .arch (a.map f) (b.map f)

def Letter.map (f : D → E) : Letter D → Letter E
  | .diag a => .diag (f a)
  | .noise => .noise

@[simp] lemma map_word (f : D → E) (d : Diagram D) :
    (d.map f).word = d.word.map (Letter.map f) := by
  induction d with
  | nil => rfl
  | diag a d ih => simp [map,word,ih,Letter.map]
  | arch a b ia ib => simp [map,word,ia,ib,Letter.map]

@[simp] lemma map_append (f : D → E) (d e : Diagram D) :
    (d.append e).map f = (d.map f).append (e.map f) := by
  induction d with
  | nil => rfl
  | diag a d ih => simp [map,append,ih]
  | arch a b ia ib => simp [map,append,ib]

lemma remove_last_diag (d : Diagram D) (F : List (Letter D)) (a : D)
    (h : d.word = F ++ [.diag a]) :
    ∃ e : Diagram D, e.word=F ∧ d=e.append (.diag a .nil) := by
  induction d generalizing F with
  | nil => simp [word] at h
  | diag b d ih =>
    cases F with
    | nil =>
      simp only [List.nil_append,word,List.cons.injEq] at h
      obtain ⟨hb,hd⟩ := h
      have hab : b=a := Letter.diag.inj hb
      subst b
      have he : d=.nil := by cases d <;> simp [word] at hd ⊢
      subst d
      exact ⟨.nil,rfl,rfl⟩
    | cons c F =>
      simp only [List.cons_append,word,List.cons.injEq] at h
      obtain ⟨rfl,hd⟩ := h
      obtain ⟨e,he,hd⟩ := ih F hd
      refine ⟨.diag b e,?_,?_⟩
      · simp [word,he]
      · simp [append,hd]
  | arch b d ib ih =>
    cases F with
    | nil => simp [word] at h
    | cons c F =>
      simp only [List.cons_append,word,List.cons.injEq] at h
      obtain ⟨rfl,hd⟩ := h
      have hdlen : b.word.length+1≤F.length := by
        have hh := congrArg List.length hd
        simp only [List.length_append,List.length_cons,List.length_nil] at hh
        by_contra hc
        have hef : d.word=[] := by
          apply List.length_eq_zero_iff.mp
          omega
        rw [hef] at hd
        have hlast := congrArg List.getLast? hd
        simp at hlast
      have he : F = b.word ++ (.noise :: F.drop (b.word.length+1)) := by
        have hh := congrArg (List.take (b.word.length+1)) hd
        rw [List.take_append_of_le_length (l₁ := F) (l₂ := [.diag a]) hdlen] at hh
        simp only [List.take_append,
          List.take_of_length_le (show b.word.length ≤ b.word.length+1 by omega),
          Nat.add_sub_cancel_left, List.take_succ_cons,List.take_zero] at hh
        have hb : F.take (b.word.length+1)=b.word++[.noise] := hh.symm
        calc
          F = F.take (b.word.length+1) ++ F.drop (b.word.length+1) :=
            (List.take_append_drop _ _).symm
          _ = _ := by rw [hb]; simp
      rw [he,List.append_assoc,List.cons_append,List.append_cancel_left_eq,
        List.cons.injEq] at hd
      obtain ⟨_,ht⟩ := hd
      obtain ⟨e,he',hde⟩ := ih _ ht
      refine ⟨.arch b e,?_,?_⟩
      · simpa [word,he'] using he.symm
      · simp [append,hde]

end Diagram
end SKGap.Noncrossing

noncomputable section
namespace SKGap.Noncrossing
namespace Diagram
variable {D : Type*}

@[simp] lemma append_size (d e : Diagram D) : (d.append e).size = d.size+e.size := by
  induction d with
  | nil => simp [append,size]
  | diag a d ih => simp [append,size,ih]; omega
  | arch a b ia ib => simp [append,size,ib]; omega

lemma append_last_diag_injective (a : D) :
    Function.Injective (fun d : Diagram D => d.append (.diag a .nil)) := by
  intro d
  induction d with
  | nil =>
    intro e he
    cases e with
    | nil => rfl
    | diag b e =>
      have ht : Diagram.nil = e.append (.diag a .nil) := (Diagram.diag.inj he).2
      have hs := congrArg size ht
      simp [size] at hs
    | arch b e => cases he
  | diag b d ih =>
    intro e he
    cases e with
    | nil =>
      have ht : d.append (.diag a .nil) = Diagram.nil := (Diagram.diag.inj he).2
      have hs := congrArg size ht
      simp [size] at hs
    | diag c e =>
      obtain ⟨rfl,ht⟩ := Diagram.diag.inj he
      rw [ih ht]
    | arch c e => cases he
  | arch b d ib ih =>
    intro e he
    cases e with
    | nil => cases he
    | diag c e => cases he
    | arch c e =>
      obtain ⟨rfl,ht⟩ := Diagram.arch.inj he
      rw [ih ht]

end Diagram
namespace InverseDiagram

def expandBlocks (bs : List Bool) : List (Letter Bool) :=
  bs.flatMap (fun b => if b then [.diag true,.noise] else [.diag false])

@[simp] lemma expandBlocks_nil : expandBlocks [] = [] := rfl
@[simp] lemma expandBlocks_false (bs : List Bool) :
    expandBlocks (false::bs) = .diag false :: expandBlocks bs := rfl
@[simp] lemma expandBlocks_true (bs : List Bool) :
    expandBlocks (true::bs) = .diag true :: .noise :: expandBlocks bs := rfl
@[simp] lemma expandBlocks_append (bs cs : List Bool) :
    expandBlocks (bs++cs) = expandBlocks bs ++ expandBlocks cs := by
  simp [expandBlocks]

lemma split_noise (bs : List Bool) (U V : List (Letter Bool))
    (h : expandBlocks bs = U ++ (.noise::V)) :
    ∃ p q : List Bool, bs=p++(true::q) ∧
      U=expandBlocks p++[.diag true] ∧ V=expandBlocks q := by
  induction bs generalizing U with
  | nil => simp at h
  | cons b bs ih =>
    cases b with
    | false =>
      cases U with
      | nil => simp at h
      | cons c U =>
        simp only [expandBlocks_false,List.cons_append,List.cons.injEq] at h
        obtain ⟨rfl,ht⟩ := h
        obtain ⟨p,q,hpq,hU,hV⟩ := ih U ht
        exact ⟨false::p,q,by simp [hpq],by simp [hU],hV⟩
    | true =>
      cases U with
      | nil => simp at h
      | cons c U =>
        simp only [expandBlocks_true,List.cons_append,List.cons.injEq] at h
        obtain ⟨rfl,ht⟩ := h
        cases U with
        | nil =>
          simp only [List.nil_append,List.cons.injEq,true_and] at ht
          exact ⟨[],bs,rfl,rfl,ht.symm⟩
        | cons c U =>
          simp only [List.cons_append,List.cons.injEq] at ht
          obtain ⟨rfl,ht⟩ := ht
          obtain ⟨p,q,hpq,hU,hV⟩ := ih U ht
          exact ⟨true::p,q,by simp [hpq],by simp [hU],hV⟩

def toDiagram : InverseDiagram → Diagram Bool
  | .empty => .nil
  | .counterterm d => .diag false (toDiagram d)
  | .arch u v => .diag true
      (.arch ((toDiagram u).append (.diag true .nil)) (toDiagram v))

@[simp] lemma toDiagram_word (d : InverseDiagram) :
    d.toDiagram.word = expandBlocks d.blocks := by
  induction d with
  | empty => rfl
  | counterterm d ih => simp [toDiagram,Diagram.word,blocks,ih]
  | arch u v iu iv => simp [toDiagram,Diagram.word,blocks,iu,iv,List.append_assoc]

lemma toDiagram_injective : Function.Injective toDiagram := by
  intro d
  induction d with
  | empty => intro e he; cases e <;> cases he; rfl
  | counterterm d ih =>
    intro e he
    cases e with
    | empty => cases he
    | counterterm e => exact congrArg counterterm (ih (Diagram.diag.inj he).2)
    | arch u v => cases he
  | arch u v iu iv =>
    intro e he
    cases e with
    | empty => cases he
    | counterterm e => cases he
    | arch x y =>
      have ht := Diagram.arch.inj (Diagram.diag.inj he).2
      rw [iu (Diagram.append_last_diag_injective true ht.1),iv ht.2]

lemma toDiagram_surjective (d : Diagram Bool) (bs : List Bool)
    (h : d.word=expandBlocks bs) :
    ∃ e : InverseDiagram, e.blocks=bs ∧ e.toDiagram=d := by
  induction hs : d.size using Nat.strong_induction_on generalizing d bs with
  | h n ih =>
    cases bs with
    | nil =>
      have hd : d=.nil := by cases d <;> simp [Diagram.word] at h ⊢
      subst d
      exact ⟨.empty,rfl,rfl⟩
    | cons b bs =>
      cases b with
      | false =>
        cases d with
        | nil => simp [Diagram.word] at h
        | arch u v => simp [Diagram.word] at h
        | diag a d =>
          simp only [Diagram.word,expandBlocks_false,List.cons.injEq,Letter.diag.injEq] at h
          obtain ⟨rfl,hd⟩ := h
          obtain ⟨e,he,hed⟩ := ih d.size (by simp [Diagram.size] at hs; omega) d bs hd rfl
          exact ⟨.counterterm e,by simp [blocks,he],by simp [toDiagram,hed]⟩
      | true =>
        cases d with
        | nil => simp [Diagram.word] at h
        | arch u v => simp [Diagram.word] at h
        | diag a d =>
          simp only [Diagram.word,expandBlocks_true,List.cons.injEq,Letter.diag.injEq] at h
          obtain ⟨rfl,hd⟩ := h
          cases d with
          | nil => simp [Diagram.word] at hd
          | diag a d => simp [Diagram.word] at hd
          | arch u v =>
            simp only [Diagram.word,List.cons.injEq,true_and] at hd
            obtain ⟨p,q,hbs,hu,hv⟩ := split_noise bs u.word v.word hd.symm
            obtain ⟨u',hu',huu⟩ := u.remove_last_diag (expandBlocks p) true hu
            have hnu : u'.size<n := by
              rw [huu] at hs
              simp only [Diagram.size,Diagram.append_size] at hs
              omega
            have hnv : v.size<n := by simp only [Diagram.size] at hs; omega
            obtain ⟨e,he,heu⟩ := ih u'.size hnu u' p hu' rfl
            obtain ⟨f,hf,hfv⟩ := ih v.size hnv v q hv rfl
            refine ⟨.arch e f,?_,?_⟩
            · simp [blocks,he,hf,hbs]
            · simp [toDiagram,heu,hfv,huu]

end InverseDiagram
end SKGap.Noncrossing

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PrimaryPrediction
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary
open Diagram

inductive Partial (D : Type*) where
  | done : Diagram D → Partial D
  | more : Diagram D → Partial D → Partial D
  deriving DecidableEq
namespace Partial
variable {D : Type*}
def word : Partial D → List (Letter D)
  | .done d => d.word
  | .more d p => d.word ++ (.noise :: p.word)
def diag (a : D) : Partial D → Partial D
  | .done d => .done (.diag a d)
  | .more d p => .more (.diag a d) p
def create (p : Partial D) : Partial D := .more .nil p
def contract : Partial D → Option (Partial D)
  | .done _ => none
  | .more d (.done e) => some (.done (.arch d e))
  | .more d (.more e p) => some (.more (.arch d e) p)
def noise (p : Partial D) : List (Partial D) := create p :: (contract p).toList

@[simp] lemma word_diag (a : D) (p : Partial D) : (p.diag a).word = .diag a :: p.word := by
  cases p <;> rfl
@[simp] lemma word_create (p : Partial D) : p.create.word = .noise :: p.word := rfl

def enumerate : List (Letter D) → List (Partial D)
  | [] => [.done .nil]
  | .diag a :: F => (enumerate F).map (diag a)
  | .noise :: F => (enumerate F).flatMap noise

end Partial

section Fock
variable {ι : Type*} [Fintype ι]
abbrev D := ι → ℝ
abbrev Stack := D (ι:=ι) × List (D (ι:=ι))
abbrev Space := Stack (ι:=ι) →₀ ℝ

def ket (s : Stack (ι:=ι)) : Space (ι:=ι) := Finsupp.single s 1

def diagonal (a : D (ι:=ι)) : Space (ι:=ι) →ₗ[ℝ] Space (ι:=ι) :=
  Finsupp.linearCombination ℝ (fun s => ket (a*s.1,s.2))
def creation : Space (ι:=ι) →ₗ[ℝ] Space (ι:=ι) :=
  Finsupp.linearCombination ℝ (fun s => ket (1,s.1::s.2))
def annihilation : Space (ι:=ι) →ₗ[ℝ] Space (ι:=ι) :=
  Finsupp.linearCombination ℝ (fun s => match s.2 with
    | [] => 0
    | a::L => Diagram.mean s.1 • ket (a,L))
def noise (j : ℝ) : Space (ι:=ι) →ₗ[ℝ] Space (ι:=ι) := creation + j • annihilation

def vacuum : Space (ι:=ι) := ket (1,[])
def project : Space (ι:=ι) →ₗ[ℝ] D (ι:=ι) :=
  Finsupp.linearCombination ℝ (fun s => if s.2=[] then s.1 else 0)

omit [Fintype ι] in
@[simp] lemma diagonal_ket (a : D (ι:=ι)) (s : Stack (ι:=ι)) :
    diagonal a (ket s)=ket (a*s.1,s.2) := by simp [diagonal,ket]
omit [Fintype ι] in
@[simp] lemma creation_ket (s : Stack (ι:=ι)) :
    creation (ket s)=ket (1,s.1::s.2) := by simp [creation,ket]
@[simp] lemma annihilation_ket_nil (a : D (ι:=ι)) :
    annihilation (ket (a,[]))=0 := by simp [annihilation,ket]
@[simp] lemma annihilation_ket_cons (a b : D (ι:=ι)) (L : List (D (ι:=ι))) :
    annihilation (ket (a,b::L))=Diagram.mean a • ket (b,L) := by simp [annihilation,ket]
omit [Fintype ι] in
@[simp] lemma project_ket_nil (a : D (ι:=ι)) : project (ket (a,[])) = a := by
  simp [project,ket]
omit [Fintype ι] in
@[simp] lemma project_ket_cons (a b : D (ι:=ι)) (L : List (D (ι:=ι))) :
    project (ket (a,b::L)) = 0 := by simp [project,ket]

def letter (j : ℝ) : Letter (D (ι:=ι)) → Space (ι:=ι) →ₗ[ℝ] Space (ι:=ι)
  | .diag a => diagonal a
  | .noise => noise j

def word (j : ℝ) : List (Letter (D (ι:=ι))) → Space (ι:=ι) →ₗ[ℝ] Space (ι:=ι)
  | [] => LinearMap.id
  | a::F => (letter j a).comp (word j F)

def outer : Diagram (D (ι:=ι)) → D (ι:=ι)
  | .nil => 1
  | .diag a d => a * outer d
  | .arch _ d => outer d

def coefficient (j : ℝ) : Diagram (D (ι:=ι)) → ℝ
  | .nil => 1
  | .diag _ d => coefficient j d
  | .arch a b => j * Diagram.mean (a.value j) * coefficient j b

def Partial.stack : Partial (D (ι:=ι)) → Stack (ι:=ι)
  | .done d => (outer d,[])
  | .more d p => (outer d,p.stack.1::p.stack.2)
def Partial.coefficient (j : ℝ) : Partial (D (ι:=ι)) → ℝ
  | .done d => Primary.coefficient j d
  | .more d p => Primary.coefficient j d * p.coefficient j

def Partial.state (j : ℝ) (p : Partial (D (ι:=ι))) : Space (ι:=ι) :=
  p.coefficient j • ket p.stack

def previousDiagonal (a : ℕ → D (ι:=ι)) : ℕ → D (ι:=ι)
  | 0 => 1
  | n+1 => a n

def creationLabels (a : ℕ → D (ι:=ι)) : ℕ → List (D (ι:=ι))
  | 0 => []
  | n+1 => previousDiagonal a n :: creationLabels a n

def primaryOperator (j : ℝ) (a : ℕ → D (ι:=ι)) :
    ℕ → Space (ι:=ι) →ₗ[ℝ] Space (ι:=ι)
  | 0 => LinearMap.id
  | 1 => noise j
  | n+2 => (noise j).comp ((diagonal (a n)).comp (primaryOperator j a (n+1))) -
      (j*Diagram.mean (a n)) •
        (diagonal (previousDiagonal a n)).comp (primaryOperator j a n)

abbrev WordPolynomial := List (ℝ × List (Letter (D (ι:=ι))))

def prependWords (F : List (Letter (D (ι:=ι)))) (P : WordPolynomial (ι:=ι)) :
    WordPolynomial (ι:=ι) := P.map (fun p => (p.1,F++p.2))
def scale (c : ℝ) (P : WordPolynomial (ι:=ι)) : WordPolynomial (ι:=ι) :=
  P.map (fun p => (c*p.1,p.2))

def polynomialOperator (j : ℝ) (P : WordPolynomial (ι:=ι)) :
    Space (ι:=ι) →ₗ[ℝ] Space (ι:=ι) :=
  (P.map (fun p => p.1 • word j p.2)).sum

def polynomialPrediction (j : ℝ) (P : WordPolynomial (ι:=ι)) (i : ι) : ℝ :=
  (P.map (fun p => p.1 * Diagram.prediction j p.2 i)).sum

def primaryPolynomial (j : ℝ) (a : ℕ → D (ι:=ι)) : ℕ → WordPolynomial (ι:=ι)
  | 0 => [(1,[])]
  | 1 => [(1,[.noise])]
  | n+2 => prependWords [.noise,.diag (a n)] (primaryPolynomial j a (n+1)) ++
      scale (-(j*Diagram.mean (a n)))
        (prependWords [.diag (previousDiagonal a n)] (primaryPolynomial j a n))

end Fock
end SKGap.Noncrossing.Primary
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixWordRegularity
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X]

def matrixFactorProduct (F : List (X→Matrix ι ι ℝ)) (x : X) : Matrix ι ι ℝ :=
  (F.map (fun f=>f x)).prod

omit [PseudoMetricSpace X] in
@[simp] lemma matrixFactorProduct_nil (x : X) : matrixFactorProduct ([] : List (X→Matrix ι ι ℝ)) x=1 := rfl
omit [PseudoMetricSpace X] in
@[simp] lemma matrixFactorProduct_cons (f : X→Matrix ι ι ℝ) (F : List (X→Matrix ι ι ℝ)) (x : X) :
    matrixFactorProduct (f::F) x=f x*matrixFactorProduct F x := rfl

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixWordIncrement
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X]

structure MatrixFactorPairBounds (B Δ : NNReal) (f g : X→Matrix ι ι ℝ) : Prop where
  leftBound : ∀ x,opNorm (f x)≤B
  rightBound : ∀ x,opNorm (g x)≤B
  leftLip : LipschitzWith B f
  rightLip : LipschitzWith B g
  parameter : ∀ x,opNorm (f x-g x)≤Δ
  increment : LipschitzWith Δ (fun x=>f x-g x)

def wordParameterCoeff (B : NNReal) : ℕ→NNReal
  | 0 => 0
  | r+1 => B^r+B*wordParameterCoeff B r

def wordMixedCoeff (B : NNReal) : ℕ→NNReal
  | 0 => 0
  | r+1 => B^r+B*wordParameterCoeff B r+(r:NNReal)*B^r+B*wordMixedCoeff B r

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_TruncationGoodSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory
open SKGap.RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def truncationGoodSet (r R lo hi : ℝ) (D C : Matrix ι ι ℝ) : Set (MatrixCoordinates ι → ℝ) :=
  {g | opNorm (goeMatrix r g) < R ∧
    lo < ComplexSpectral.lowerRayleigh (liftMatrix (1-D*(goeMatrix r g-C)*D)) ∧
    -hi < ComplexSpectral.lowerRayleigh (-liftMatrix (1-D*(goeMatrix r g-C)*D))}

end SKGap

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_PathBiasBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

noncomputable section
open Real

namespace SKGap
open Real

def loopErrorConstantOne (j A B L rate : ℝ) : ℝ :=
  2*j*L*(36/rate^3)+2*j*B*A*B*(3/rate)+
    j*(B*(2*Real.exp (π^2/8))*(A*L*sqrt (2*j)+1)+B*A*B)
def loopErrorConstantTwo (j A B rate : ℝ) : ℝ :=
  (B+1+A*(j*A)*B)*(3/rate)+A*B*sqrt (2*j)*(8*sqrt 3/rate^2)

end SKGap

end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RealQuadratic
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
noncomputable section
open scoped BigOperators Topology
open Filter Real
namespace SKGap.RealComplex
open SKGap.ComplexSpectral
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def realQuadratic (M : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, ∑ k, x i * M i k * x k

end SKGap.RealComplex

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianQuadratic
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
namespace SKGap
open scoped BigOperators

section Quadratic
variable {ι : Type*} [Fintype ι]

def gaussianQuadratic (a : ι → ℝ) (x : ι → ℝ) : ℝ := ∑ i, a i * (x i)^2

end Quadratic

end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ExpSum
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
namespace SKGap

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct_1 (n : ℕ) : IsProbabilityMeasure (standardGaussianProduct n) := by
  unfold standardGaussianProduct
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def expSum (κ : ℝ) (x : ι → ℝ) : ℝ := ∑ i, Real.exp (κ * x i)
def softWeight (κ : ℝ) (x : ι → ℝ) (i : ι) : ℝ := Real.exp (κ * x i) / expSum κ x
def smoothMax (κ : ℝ) (x : ι → ℝ) : ℝ := log (expSum κ x) / κ

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def affineProcess {n : ℕ} (m : ι → ℝ) (a : ι → Fin n → ℝ) (z : Fin n → ℝ) (i : ι) : ℝ :=
  m i + ∑ k, a i k * z k

def interpolatedCoeff {n : ℕ} (a b : ι → Fin n → ℝ) (t : ℝ) (i : ι) (k : Fin n) : ℝ :=
  sin t * a i k + cos t * b i k

def interpolatedCoeffDeriv {n : ℕ} (a b : ι → Fin n → ℝ) (t : ℝ) (i : ι) (k : Fin n) : ℝ :=
  cos t * a i k - sin t * b i k

def processBound {n : ℕ} (a b : ι → Fin n → ℝ) (z : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ k, (|a i k| + |b i k|) * |z k|

def interpolationDerivative {n : ℕ} (κ : ℝ) (m : ι → ℝ) (a b : ι → Fin n → ℝ)
    (t : ℝ) (z : Fin n → ℝ) : ℝ :=
  ∑ i, softWeight κ (affineProcess m (interpolatedCoeff a b t) z) i *
    ∑ k, interpolatedCoeffDeriv a b t i k * z k

end SKGap
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_FiniteMax
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
namespace SKGap
variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def finiteMax (x : ι → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty x

section CompactIndex
variable {I : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I]

def supProcess {n : ℕ} (m : I → ℝ) (a : I → Fin n → ℝ) (z : Fin n → ℝ) : ℝ :=
  sSup (Set.range (affineProcess m a z))

end CompactIndex
end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianCoordinates
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
namespace SKGap
section ArbitraryCoordinates
variable {I κ : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I]
  [Fintype κ]

def gaussianCoordinates (κ : Type*) [Fintype κ] : Measure (κ → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance instIsProbabilityMeasureForallRealGaussianCoordinates : IsProbabilityMeasure (gaussianCoordinates κ) := by
  unfold gaussianCoordinates
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def gaussianAffine (m : I → ℝ) (a : I → κ → ℝ) (z : κ → ℝ) (i : I) : ℝ :=
  m i + ∑ k, a i k * z k

def gaussianSup (m : I → ℝ) (a : I → κ → ℝ) (z : κ → ℝ) : ℝ :=
  sSup (Set.range (gaussianAffine m a z))

end ArbitraryCoordinates
end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_QuadraticCoeff
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace SKGap
section GaussianQuadratic
variable {ι : Type*} [Fintype ι]

def quadraticCoeff (r : ℝ) (w : EuclideanSpace ℝ ι) : MatrixCoordinates ι → ℝ
  | Sum.inl (i, k) => Real.sqrt (2 * r) * w i * w k
  | Sum.inr _ => 0

def linearCoeff (r : ℝ) (w : EuclideanSpace ℝ ι) : MatrixCoordinates ι → ℝ
  | Sum.inl _ => 0
  | Sum.inr i => 2 * Real.sqrt r * ‖w‖ * w i

end GaussianQuadratic
end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_DiagonalSqrt
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace SKGap
section DiagonalGeometry
variable {ι : Type*} [Fintype ι]

def diagonalSqrt (a : ι → ℝ) (p : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => Real.sqrt (a i) * p i)

end DiagonalGeometry

end SKGap

open Real

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_UnitBall
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
namespace SKGap

section DiagonalProcess
variable {ι : Type*} [Fintype ι]

abbrev UnitBall (ι : Type*) [Fintype ι] :=
  ↥(Metric.closedBall (0 : EuclideanSpace ℝ ι) 1)

instance instNonemptyUnitBall : Nonempty (UnitBall ι) := ⟨⟨0, by simp⟩⟩

def diagonalOffset (a : ι → ℝ) (z q : ℝ) (p : UnitBall ι) : ℝ :=
  -z^2 * q * ‖diagonalSqrt a p‖^2

def diagonalProcess (r : ℝ) (a : ι → ℝ) (z q : ℝ)
    (g : MatrixCoordinates ι → ℝ) : ℝ :=
  gaussianSup (diagonalOffset a z q)
    (fun p k => z * quadraticCoeff r (diagonalSqrt a p) k) g

def diagonalLinearProcess (r : ℝ) (a : ι → ℝ) (z q : ℝ)
    (g : MatrixCoordinates ι → ℝ) : ℝ :=
  gaussianSup (diagonalOffset a z q)
    (fun p k => z * linearCoeff r (diagonalSqrt a p) k) g

def diagonalWeights (r : ℝ) (a : ι → ℝ) : MatrixCoordinates ι → ℝ
  | Sum.inl _ => 0
  | Sum.inr i => r * a i

def diagonalT (r : ℝ) (a : ι → ℝ) (g : MatrixCoordinates ι → ℝ) : ℝ :=
  sqrt (gaussianQuadratic (diagonalWeights r a) g)

end DiagonalProcess
end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixQuad
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
noncomputable section
open scoped BigOperators Topology
open Filter Real
namespace SKGap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def matrixQuad (M : Matrix ι ι ℝ) (p : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, ∑ k, p i * M i k * p k

def matrixOperator (M : Matrix ι ι ℝ) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  M.toEuclideanLin.toContinuousLinearMap

end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_StabilityMatrix
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
noncomputable section
open scoped BigOperators Topology
open Filter Real
namespace SKGap
section GOEPath
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def stabilityMatrix (a : ι → ℝ) (z q : ℝ) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i k => (if i = k then 1 + z^2*q*a i else 0) - z*sqrt (a i)*M i k*sqrt (a k)

end GOEPath
end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_PathDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
noncomputable section
open scoped BigOperators Topology
open Filter Real
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex ComplexSpectral
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pathDiagonal (a : ι → ℝ) (z : ℝ) : Matrix ι ι ℝ :=
  diagonal (fun i => sqrt z*sqrt (a i))
def pathShift (z q : ℝ) : Matrix ι ι ℝ := diagonal (fun _ => z*q)

end SKGap

namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pathBound (f : 𝓢(ℝ,ℂ)) (R j A : ℝ) : ℝ :=
  1+A*ComplexMatrix.fourierMoment f 0*(R+j*A)
def pathLip (f : 𝓢(ℝ,ℂ)) (R j A : ℝ) : ℝ :=
  ComplexMatrix.fl1 f*A^2*(R+j*A)+A*ComplexMatrix.fourierMoment f 0

lemma path_constants_nonneg (f : 𝓢(ℝ,ℂ)) {R j A : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) :
    0 ≤ pathBound f R j A ∧ 0 ≤ pathLip f R j A := by
  have h₀ := ComplexMatrix.fourierMoment_nonneg f 0
  have h₁ := (ComplexMatrix.fl_nonneg f).1
  unfold pathBound pathLip
  exact ⟨by positivity,by positivity⟩

end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ExpectedCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
noncomputable section
open scoped BigOperators Topology
open Filter Real
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def expectedCutoff (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R)
    (D C : Matrix ι ι ℝ) (r : ℝ) (i : ι) : ℝ :=
  ∫ g, realTruncatedK f R hR D C (goeMatrix r g) i i
    ∂(Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))

noncomputable def cutoffErrorOne (f : 𝓢(ℝ,ℂ)) (r R lo hi : ℝ)
    (D C : Matrix ι ι ℝ) : ℝ :=
  let b := ComplexMatrix.kBound f R (liftMatrix D) (liftMatrix C)
  let L := Real.toNNReal (ComplexMatrix.kLip f R (liftMatrix D) (liftMatrix C))
  let Lπ : ℝ≥0 := L*(⟨sqrt (2*r),sqrt_nonneg _⟩ *
    (Fintype.card (MatrixCoordinates ι) : ℝ≥0) ^ (1/(2:ℝ≥0∞)).toReal)
  let T : ℝ≥0 := (⟨sqrt (Fintype.card ι)*opNorm (D*D),
    mul_nonneg (sqrt_nonneg _) (norm_nonneg _)⟩*L)*⟨sqrt (2*r),sqrt_nonneg _⟩+1
  (Fintype.card ι:ℝ)*(sqrt (2*r)*(Lπ:ℝ)+r*(2*b*opNorm (D*D)*b))*
    (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      (truncationGoodSet r R lo hi D C)ᶜ+
    r*(b*((2*Real.exp (π^2/8))*(T:ℝ))+b*opNorm (D*D)*b)

noncomputable def cutoffErrorTwo (f : 𝓢(ℝ,ℂ)) (r R lo hi : ℝ)
    (d c : ι → ℝ) (i : ι) : ℝ :=
  let b := ComplexMatrix.kBound f R (liftMatrix (diagonal d)) (liftMatrix (diagonal c))
  let p := (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
    (truncationGoodSet r R lo hi (diagonal d) (diagonal c))ᶜ
  (b+1+|(d i)^2*c i| *b)*p+
    (|(d i)^2| *b)*(Fintype.card ι:ℝ)*sqrt (2*r)*sqrt p

end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_PathExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def pathExpected (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (j : ℝ) (a : ι → ℝ)
    (z : ℝ) (i : ι) : ℝ :=
  expectedCutoff f R hR (pathDiagonal a z)
    (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b, a b)) (j/(Fintype.card ι:ℝ)) i

end SKGap
end
end

section
noncomputable section

namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap Topology

def pathRate (j A : ℝ) : ℝ :=
  min (1/(π^2*j)) (((1-sqrt j*A)^2)^2/(16*π^2*j*A^2))

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_PathBias
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def pathExpectedWK (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (j : ℝ) (a : ι → ℝ)
    (z : ℝ) (i : ι) : ℝ :=
  ∫ g, (goeMatrix (j/(Fintype.card ι:ℝ)) g * realTruncatedK f R hR (pathDiagonal a z)
    (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b, a b)) (goeMatrix (j/(Fintype.card ι:ℝ)) g)) i i
      ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ProjectedReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def realProject (R : ℝ) (hR : 0 ≤ R) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  RealComplex.realPart (ComplexMatrix.matrixProject R hR (liftMatrix M))

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Real

def projectedErrorConstant (j R B rate : ℝ) : ℝ :=
  R*B*(3/rate)+B*sqrt (2*j)*(8*sqrt 3/rate^2)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_PathCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pathK (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (j : ℝ) (a : ι → ℝ)
    (z : ℝ) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  realTruncatedK f R hR (pathDiagonal a z)
    (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b, a b)) M

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_Word
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap

inductive WordLetter (ι : Type*)
  | diag : (ι→ℝ)→WordLetter ι
  | noise : WordLetter ι
  | inverse : WordLetter ι

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def WordLetter.bounded (D : ℝ) : WordLetter ι→Prop
  | .diag d => ∀ i,|d i| ≤ D
  | .noise => True
  | .inverse => True

def WordLetter.eval (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ) :
    WordLetter ι→Matrix ι ι ℝ→Matrix ι ι ℝ
  | .diag d,_ => diagonal d
  | .noise,M => realProject R hR M
  | .inverse,M => pathK f R hR j a z M

def actualWord (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (F : List (WordLetter ι)) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  matrixFactorProduct (F.map (WordLetter.eval f R hR j a z)) M

def actualWordBound (f : 𝓢(ℝ,ℂ)) (R j A D : ℝ) : ℝ :=
  1+R+D+pathBound f R j A+pathLip f R j A

lemma actualWordBound_pos (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) : 0<actualWordBound f R j A D := by
  have hh := path_constants_nonneg f hR hj hA
  unfold actualWordBound
  linarith

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def WordLetter.direction (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0≤R) (j : ℝ) (a : ι→ℝ)
    (z : ℝ) (M E : Matrix ι ι ℝ) : WordLetter ι→Matrix ι ι ℝ
  | .diag _ => 0
  | .noise => E
  | .inverse => z • (pathK f R hR j a z M*diagonal a*E*pathK f R hR j a z M)

def actualWordDirection (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0≤R) (j : ℝ) (a : ι→ℝ)
    (z : ℝ) (M E : Matrix ι ι ℝ) : List (WordLetter ι)→Matrix ι ι ℝ
  | [] => 0
  | l::F => l.direction f R hR j a z M E*actualWord f R hR j a z F M +
      l.eval f R hR j a z M*actualWordDirection f R hR j a z M E F

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MarkedWordIBP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap

structure WordCut (ι : Type*) where
  left : List (WordLetter ι)
  right : List (WordLetter ι)
  inversePartner : Bool

variable {ι : Type*}

def WordCut.prepend (l : WordLetter ι) (c : WordCut ι) : WordCut ι :=
  ⟨l::c.left,c.right,c.inversePartner⟩

def wordPartners (a : ι→ℝ) : List (WordLetter ι)→List (WordCut ι)
  | [] => []
  | l::F => (match l with
      | .diag _ => []
      | .noise => [⟨[],F,false⟩]
      | .inverse => [⟨[.inverse,.diag a],.inverse::F,true⟩]) ++
      (wordPartners a F).map (WordCut.prepend l)

lemma wordPartners_cons (a : ι→ℝ) (l : WordLetter ι) (F : List (WordLetter ι)) :
    wordPartners a (l::F)=(match l with
      | .diag _ => []
      | .noise => [⟨[],F,false⟩]
      | .inverse => [⟨[.inverse,.diag a],.inverse::F,true⟩]) ++
      (wordPartners a F).map (WordCut.prepend l) := rfl

variable [Fintype ι] [DecidableEq ι]

def WordCut.value (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (M E : Matrix ι ι ℝ) (c : WordCut ι) : Matrix ι ι ℝ :=
  (if c.inversePartner then z else 1) •
    (actualWord f R hR j a z c.left M*E*actualWord f R hR j a z c.right M)

omit [Fintype ι] [DecidableEq ι] in
def ordinaryCount (F : List (WordLetter ι)) : ℕ :=
  F.countP (fun l=>match l with | .noise=>true | _=>false)
omit [Fintype ι] [DecidableEq ι] in
def inverseCount (F : List (WordLetter ι)) : ℕ :=
  F.countP (fun l=>match l with | .inverse=>true | _=>false)

omit [Fintype ι] [DecidableEq ι] in
lemma wordPartners_counts (a : ι→ℝ) (F : List (WordLetter ι)) (c : WordCut ι)
    (hc : c∈wordPartners a F) :
    ordinaryCount c.left+ordinaryCount c.right+(if c.inversePartner then 0 else 1)=ordinaryCount F ∧
    inverseCount c.left+inverseCount c.right=inverseCount F+(if c.inversePartner then 1 else 0) := by
  induction F generalizing c with
  | nil => simp [wordPartners] at hc
  | cons l F ih =>
    rw [wordPartners_cons a l F,List.mem_append] at hc
    rcases hc with hc|hc
    · cases l with
      | diag d => simp at hc
      | noise =>
        simp only [List.mem_singleton] at hc
        subst c
        simp [ordinaryCount,inverseCount]
      | inverse =>
        simp only [List.mem_singleton] at hc
        subst c
        simp [ordinaryCount,inverseCount]
        omega
    · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
      obtain ⟨h1,h2⟩ := ih d hd
      cases hf : d.inversePartner <;> cases l <;>
        simp [WordCut.prepend,ordinaryCount,inverseCount,hf] at * <;> omega
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordPartnerContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def markedContraction (U V Q : Matrix ι ι ℝ) (i : ι) : ℝ :=
  (U*Q) i i*trace V+(U*Vᵀ*Q) i i

def WordCut.leftContraction (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (M Q : Matrix ι ι ℝ) (i : ι) (c : WordCut ι) : ℝ :=
  (if c.inversePartner then z else 1)*markedContraction
    (actualWord f R hR j a z c.left M) (actualWord f R hR j a z c.right M) Q i

def WordCut.rightContraction (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (M U : Matrix ι ι ℝ) (i : ι) (c : WordCut ι) : ℝ :=
  (if c.inversePartner then z else 1)*markedContraction U
    (actualWord f R hR j a z c.left M) (actualWord f R hR j a z c.right M) i

end SKGap
end
end

section
noncomputable section
namespace SKGap
open scoped BigOperators
variable {ι : Type*}

@[simp] lemma ordinaryCount_append (P Q : List (WordLetter ι)) :
    ordinaryCount (P++Q)=ordinaryCount P+ordinaryCount Q := by simp [ordinaryCount]
@[simp] lemma inverseCount_append (P Q : List (WordLetter ι)) :
    inverseCount (P++Q)=inverseCount P+inverseCount Q := by simp [inverseCount]
@[simp] lemma ordinaryCount_noise (Q : List (WordLetter ι)) :
    ordinaryCount (.noise::Q)=ordinaryCount Q+1 := by simp [ordinaryCount]
@[simp] lemma inverseCount_noise (Q : List (WordLetter ι)) :
    inverseCount (.noise::Q)=inverseCount Q := by simp [inverseCount]

structure WordRecursionTerm (ι : Type*) where
  outer : List (WordLetter ι)
  inner : List (WordLetter ι)
  inversePartner : Bool

def WordCut.asLeft (Q : List (WordLetter ι)) (c : WordCut ι) : WordRecursionTerm ι :=
  ⟨c.left++Q,c.right,c.inversePartner⟩
def WordCut.asRight (P : List (WordLetter ι)) (c : WordCut ι) : WordRecursionTerm ι :=
  ⟨P++c.right,c.left,c.inversePartner⟩
def wordRecursionAt (a : ι→ℝ) (P Q : List (WordLetter ι)) : List (WordRecursionTerm ι) :=
  ((wordPartners a P).map (WordCut.asLeft Q))++((wordPartners a Q).map (WordCut.asRight P))

lemma wordRecursionAt_decreases (a : ι→ℝ) (P Q : List (WordLetter ι))
    (t : WordRecursionTerm ι) (ht : t∈wordRecursionAt a P Q) :
    ordinaryCount t.outer<ordinaryCount (P++(.noise::Q)) ∧
    ordinaryCount t.inner<ordinaryCount (P++(.noise::Q)) := by
  dsimp only [wordRecursionAt] at ht
  rw [List.mem_append] at ht
  rcases ht with ht|ht
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
    have hh := (wordPartners_counts a P c hc).1
    cases hi : c.inversePartner <;> simp [WordCut.asLeft,hi] at * <;> omega
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
    have hh := (wordPartners_counts a Q c hc).1
    cases hi : c.inversePartner <;> simp [WordCut.asRight,hi] at * <;> omega

def firstNoiseSplit : List (WordLetter ι)→Option (List (WordLetter ι)×List (WordLetter ι))
  | [] => none
  | .noise::F => some ([],F)
  | l::F => (firstNoiseSplit F).map (fun pq=>(l::pq.1,pq.2))

lemma firstNoiseSplit_some (F P Q : List (WordLetter ι)) (h : firstNoiseSplit F=some (P,Q)) :
    F=P++(.noise::Q) := by
  induction F generalizing P Q with
  | nil => simp [firstNoiseSplit] at h
  | cons l F ih =>
    cases l with
    | noise => simp only [firstNoiseSplit,Option.some.injEq,Prod.mk.injEq] at h;rcases h with ⟨rfl,rfl⟩;rfl
    | diag d =>
      simp only [firstNoiseSplit,Option.map_eq_some_iff] at h
      obtain ⟨⟨P',Q'⟩,h1,h2⟩ := h
      simp only [Prod.mk.injEq] at h2
      rcases h2 with ⟨rfl,rfl⟩
      simpa only [List.cons_append] using congrArg (List.cons (.diag d)) (ih P' Q' h1)
    | inverse =>
      simp only [firstNoiseSplit,Option.map_eq_some_iff] at h
      obtain ⟨⟨P',Q'⟩,h1,h2⟩ := h
      simp only [Prod.mk.injEq] at h2
      rcases h2 with ⟨rfl,rfl⟩
      simpa only [List.cons_append] using congrArg (List.cons (.inverse)) (ih P' Q' h1)

def wordRecursionTerms (a : ι→ℝ) (F : List (WordLetter ι)) : List (WordRecursionTerm ι) :=
  match firstNoiseSplit F with
  | none => []
  | some (P,Q) => wordRecursionAt a P Q

lemma wordRecursionTerms_decreases (a : ι→ℝ) (F : List (WordLetter ι))
    (t : WordRecursionTerm ι) (ht : t∈wordRecursionTerms a F) :
    ordinaryCount t.outer<ordinaryCount F ∧ ordinaryCount t.inner<ordinaryCount F := by
  unfold wordRecursionTerms at ht
  cases hs : firstNoiseSplit F with
  | none => simp [hs] at ht
  | some pq =>
    rcases pq with ⟨P,Q⟩
    have he := firstNoiseSplit_some F P Q hs
    simp only [hs] at ht
    simpa only [he] using wordRecursionAt_decreases a P Q t ht

def wordDiagonal (F : List (WordLetter ι)) (i : ι) : ℝ :=
  ((F.map (fun l=>match l with | .diag d=>d i | _=>1))).prod

def wordPrediction [Fintype ι] (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (F : List (WordLetter ι)) (i : ι) : ℝ :=
  if ordinaryCount F=0 then wordDiagonal F i else
    ((wordRecursionTerms a F).attach.map (fun th=>
      (if th.val.inversePartner then z else 1)*j*
        ((∑ k,wordPrediction j a z th.val.inner k)/(Fintype.card ι:ℝ))*
          wordPrediction j a z th.val.outer i)).sum
termination_by ordinaryCount F
decreasing_by
  · exact (wordRecursionTerms_decreases a F th.val th.property).2
  · exact (wordRecursionTerms_decreases a F th.val th.property).1

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_BlockDegree
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
namespace InverseDiagram

def blockDegree (bs : List Bool) : ℕ := (bs.map (fun b => if b then 1 else 2)).sum

def blockEnumerate : ℕ → List (List Bool)
  | 0 => [[]]
  | n+1 => (blockEnumerate n).map (true::·) ++
      (if n=0 then [] else (blockEnumerate (n-1)).map (false::·))
termination_by m => m

def Blocks (n : ℕ) := {bs : List Bool // blockDegree bs=n}

@[simp] lemma blockDegree_nil : blockDegree []=0 := rfl
@[simp] lemma blockDegree_true (bs : List Bool) :
    blockDegree (true::bs)=blockDegree bs+1 := by simp [blockDegree,add_comm]
@[simp] lemma blockDegree_false (bs : List Bool) :
    blockDegree (false::bs)=blockDegree bs+2 := by simp [blockDegree,add_comm]

lemma mem_blockEnumerate (bs : List Bool) (n : ℕ) :
    bs∈blockEnumerate n ↔ blockDegree bs=n := by
  induction n using Nat.strong_induction_on generalizing bs with
  | h n ih =>
    cases n with
    | zero =>
      cases bs with
      | nil => simp [blockEnumerate]
      | cons b bs => cases b <;> simp [blockEnumerate]
    | succ n =>
      rw [blockEnumerate]
      cases bs with
      | nil => split_ifs <;> simp
      | cons b bs =>
        cases b with
        | true =>
          have ht : ((true::bs)∈(blockEnumerate n).map (true::·) ++
            (if n=0 then [] else (blockEnumerate (n-1)).map (false::·))) ↔
              bs∈blockEnumerate n := by split_ifs <;> simp
          rw [ht,ih n (by omega) bs,blockDegree_true]
          omega
        | false =>
          by_cases hn : n=0
          · subst n; simp
          · have hf : ((false::bs)∈(blockEnumerate n).map (true::·) ++
                (if n=0 then [] else (blockEnumerate (n-1)).map (false::·))) ↔
                  bs∈blockEnumerate (n-1) := by simp [hn]
            rw [hf,ih (n-1) (by omega) bs,blockDegree_false]
            omega

instance blocksFintype (n : ℕ) : Fintype (Blocks n) :=
  Fintype.ofFinset (blockEnumerate n).toFinset (by
    intro bs
    simp only [List.mem_toFinset,mem_blockEnumerate]; rfl)

def LiteralPaired (n : ℕ) := Σ bs : Blocks n, Diagram.Paired (expandBlocks bs.val)
instance literalPairedFintype (n : ℕ) : Fintype (LiteralPaired n) :=
  inferInstanceAs (Fintype (Σ bs : Blocks n, Diagram.Paired (expandBlocks bs.val)))

def AtDegree (n : ℕ) := {d : InverseDiagram // d.degree=n}
instance atDegreeFintype (n : ℕ) : Fintype (AtDegree n) :=
  Fintype.ofFinset (enumerate n).toFinset (by
    intro d
    simp only [List.mem_toFinset,mem_enumerate]; rfl)

def toLiteral {n : ℕ} (d : AtDegree n) : LiteralPaired (2*n) :=
  ⟨⟨d.val.blocks,by
      simpa only [blockDegree,d.property] using d.val.blocks_degree⟩,
    ⟨d.val.toDiagram,d.val.toDiagram_word⟩⟩

lemma toLiteral_bijective (n : ℕ) : Function.Bijective (@toLiteral n) := by
  constructor
  · intro d e he
    apply Subtype.ext
    apply toDiagram_injective
    exact congrArg (fun z : LiteralPaired (2*n) => z.2.val) he
  · intro z
    obtain ⟨e,he,hed⟩ := toDiagram_surjective z.2.val z.1.val z.2.property
    have hn : e.degree=n := by
      have hh := e.blocks_degree
      rw [he] at hh
      change blockDegree z.1.val=2*e.degree at hh
      rw [z.1.property] at hh
      omega
    use ⟨e,hn⟩
    apply Sigma.ext
    · exact Subtype.ext he
    · apply (Subtype.heq_iff_coe_eq (fun d => ?_)).mpr hed
      change d.word=expandBlocks e.blocks ↔ d.word=expandBlocks z.1.val
      rw [he]

def literalEquiv (n : ℕ) : AtDegree n ≃ LiteralPaired (2*n) :=
  Equiv.ofBijective toLiteral (toLiteral_bijective n)

variable {ι : Type*} [Fintype ι]

def blockLabel (j : ℝ) (a : ι→ℝ) : Bool → ι→ℝ
  | true => a
  | false => fun i => -(j*average a)*a i

def literalCoefficient (j : ℝ) (a : ι→ℝ) (n : ℕ) (i : ι) : ℝ :=
  ∑ z : LiteralPaired n, (z.2.val.map (blockLabel j a)).value j i

end InverseDiagram
end SKGap.Noncrossing

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_NoiseSplit
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
namespace Diagram
variable {D : Type*}

@[ext] structure NoiseSplit (F : List (Letter D)) where
  before : List (Letter D)
  after : List (Letter D)
  word_eq : F=before++(.noise::after)

lemma NoiseSplit.before_take {F : List (Letter D)} (s : NoiseSplit F) :
    s.before=F.take s.before.length := by
  simpa using (congrArg (List.take s.before.length) s.word_eq).symm
lemma NoiseSplit.after_drop {F : List (Letter D)} (s : NoiseSplit F) :
    s.after=F.drop (s.before.length+1) := by
  simpa using (congrArg (List.drop (s.before.length+1)) s.word_eq).symm
lemma NoiseSplit.length_bound {F : List (Letter D)} (s : NoiseSplit F) :
    s.before.length<F.length := by
  have h := congrArg List.length s.word_eq
  simp only [List.length_append,List.length_cons] at h
  omega

def NoiseSplit.code {F : List (Letter D)} (s : NoiseSplit F) : Fin F.length :=
  ⟨s.before.length,s.length_bound⟩
lemma NoiseSplit.code_injective (F : List (Letter D)) :
    Function.Injective (NoiseSplit.code (F := F)) := by
  intro a b h
  have hh : a.before.length=b.before.length := congrArg Fin.val h
  apply NoiseSplit.ext
  · rw [a.before_take,b.before_take,hh]
  · rw [a.after_drop,b.after_drop,hh]
instance noiseSplitFinite (F : List (Letter D)) : Finite (NoiseSplit F) :=
  Finite.of_injective _ (NoiseSplit.code_injective F)
instance noiseSplitFintype (F : List (Letter D)) : Fintype (NoiseSplit F) :=
  Fintype.ofFinite _

def shapeAt (P Q : List (Letter D)) :
    NoiseSplit P ⊕ NoiseSplit Q → PairShape (P++(.noise::Q)) P.length
  | .inl s => ⟨s.before,s.after,Q,true,by
      simpa only [List.append_assoc,List.cons_append] using
        congrArg (fun f => f++(.noise::Q)) s.word_eq,by
      have h := congrArg List.length s.word_eq
      simpa using h⟩
  | .inr s => ⟨P,s.before,s.after,false,congrArg (fun f => P++(.noise::f)) s.word_eq,by simp⟩

lemma shapeAt_bijective (P Q : List (Letter D)) : Function.Bijective (shapeAt P Q) := by
  constructor
  · intro a b he
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        apply congrArg Sum.inl
        exact NoiseSplit.ext (congrArg PairShape.before he) (congrArg PairShape.between he)
      | inr b => have hh := congrArg PairShape.closing he; cases hh
    | inr a =>
      cases b with
      | inl b => have hh := congrArg PairShape.closing he; cases hh
      | inr b =>
        apply congrArg Sum.inr
        exact NoiseSplit.ext (congrArg PairShape.between he) (congrArg PairShape.after he)
  · intro s
    cases hc : s.closing with
    | false =>
      have hlen : P.length=s.before.length := by simpa [hc] using s.mark_eq
      have hparts := List.append_inj s.word_eq hlen
      have hP : P=s.before := hparts.1
      have hQ : Q=s.between++(.noise::s.after) := List.cons.inj hparts.2 |>.2
      refine ⟨.inr ⟨s.between,s.after,hQ⟩,?_⟩
      apply PairShape.ext <;> simp [shapeAt,hP,hc]
    | true =>
      have hlen : P.length=(s.before++(.noise::s.between)).length := by
        simpa [hc] using s.mark_eq
      have hw : P++(.noise::Q)=(s.before++(.noise::s.between))++(.noise::s.after) := by
        simpa only [List.append_assoc,List.cons_append] using s.word_eq
      have hparts := List.append_inj hw hlen
      have hP := hparts.1
      have hQ : Q=s.after := List.cons.inj hparts.2 |>.2
      refine ⟨.inl ⟨s.before,s.between,hP⟩,?_⟩
      apply PairShape.ext <;> simp [shapeAt,hQ,hc]

def shapeAtEquiv (P Q : List (Letter D)) :
    (NoiseSplit P ⊕ NoiseSplit Q) ≃ PairShape (P++(.noise::Q)) P.length :=
  Equiv.ofBijective (shapeAt P Q) (shapeAt_bijective P Q)

section Evaluate
variable {ι : Type*} [Fintype ι]

def evaluate (j : ℝ) (v : D→ι→ℝ) (d : Diagram D) : ι→ℝ := (d.map v).value j

@[simp] lemma evaluate_nil (j : ℝ) (v : D→ι→ℝ) (i : ι) :
    evaluate j v .nil i=1 := rfl
@[simp] lemma evaluate_diag (j : ℝ) (v : D→ι→ℝ) (a : D) (d : Diagram D) (i : ι) :
    evaluate j v (.diag a d) i=v a i*evaluate j v d i := rfl
@[simp] lemma evaluate_arch (j : ℝ) (v : D→ι→ℝ) (d e : Diagram D) (i : ι) :
    evaluate j v (.arch d e) i=j*mean (evaluate j v d)*evaluate j v e i := rfl

def expect (j : ℝ) (v : D→ι→ℝ) (F : List (Letter D)) (i : ι) : ℝ :=
  ∑ d : Paired F, evaluate j v d.val i

end Evaluate
end Diagram
end SKGap.Noncrossing

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Map
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
namespace Diagram
variable {D E : Type*}

def NoiseSplit.map (f : D→E) {F : List (Letter D)} (s : NoiseSplit F) :
    NoiseSplit (F.map (Letter.map f)) where
  before := s.before.map (Letter.map f)
  after := s.after.map (Letter.map f)
  word_eq := by simpa [Letter.map] using congrArg (List.map (Letter.map f)) s.word_eq

lemma NoiseSplit.map_bijective (f : D→E) (F : List (Letter D)) :
    Function.Bijective (NoiseSplit.map f (F := F)) := by
  constructor
  · intro s t h
    apply NoiseSplit.code_injective F
    apply Fin.ext
    have hh := congrArg (fun s => s.before.length) h
    simpa [NoiseSplit.map,NoiseSplit.code] using hh
  · intro s
    obtain ⟨p,q,hF,hp,hq⟩ := List.map_eq_append_iff.mp s.word_eq
    cases q with
    | nil => simp at hq
    | cons l q =>
      cases l with
      | diag a => simp [Letter.map] at hq
      | noise =>
        simp only [List.map_cons,Letter.map,List.cons.injEq,true_and] at hq
        refine ⟨⟨p,q,hF⟩,?_⟩
        apply NoiseSplit.ext <;> simp [NoiseSplit.map,hp,hq]

def NoiseSplit.mapEquiv (f : D→E) (F : List (Letter D)) :
    NoiseSplit F ≃ NoiseSplit (F.map (Letter.map f)) :=
  Equiv.ofBijective (NoiseSplit.map f) (NoiseSplit.map_bijective f F)

def NoiseSplit.appendLeft (P Q : List (Letter D)) (s : NoiseSplit P) :
    NoiseSplit (P++Q) :=
  ⟨s.before,s.after++Q,by
    simpa only [List.append_assoc,List.cons_append] using
      congrArg (fun f => f++Q) s.word_eq⟩
def NoiseSplit.appendRight (P Q : List (Letter D)) (s : NoiseSplit Q) :
    NoiseSplit (P++Q) :=
  ⟨P++s.before,s.after,by
    simpa only [List.append_assoc] using
      congrArg (fun f => P++f) s.word_eq⟩

def NoiseSplit.appendMap (P Q : List (Letter D)) :
    NoiseSplit P ⊕ NoiseSplit Q → NoiseSplit (P++Q) :=
  Sum.elim (NoiseSplit.appendLeft P Q) (NoiseSplit.appendRight P Q)

lemma take_noise_drop {F : List (Letter D)} {k : ℕ} (h : F[k]?=some .noise) :
    F=F.take k++(.noise::F.drop (k+1)) := by
  have he := List.take_append_drop k F
  rw [List.drop_eq_getElem?_toList_append,h] at he
  simpa using he.symm

lemma NoiseSplit.appendMap_bijective (P Q : List (Letter D)) :
    Function.Bijective (NoiseSplit.appendMap P Q) := by
  constructor
  · intro s t h
    cases s with
    | inl s =>
      cases t with
      | inl t =>
        apply congrArg Sum.inl
        apply NoiseSplit.code_injective P
        apply Fin.ext
        exact congrArg (fun s => s.before.length) h
      | inr t =>
        have hh := congrArg (fun s => s.before.length) h
        change s.before.length=(P++t.before).length at hh
        have hs := s.length_bound
        simp only [List.length_append] at hh
        omega
    | inr s =>
      cases t with
      | inl t =>
        have hh := congrArg (fun s => s.before.length) h
        change (P++s.before).length=t.before.length at hh
        have ht := t.length_bound
        simp only [List.length_append] at hh
        omega
      | inr t =>
        apply congrArg Sum.inr
        apply NoiseSplit.code_injective Q
        apply Fin.ext
        have hh := congrArg (fun s => s.before.length) h
        change (P++s.before).length=(P++t.before).length at hh
        simpa [NoiseSplit.code] using hh
  · intro s
    by_cases h : s.before.length<P.length
    · have he : (P++Q)[s.before.length]?=some .noise := by
        simpa using congrArg (fun f => f[s.before.length]?) s.word_eq
      have hP : P[s.before.length]?=some .noise := by simpa [List.getElem?_append,h] using he
      let t : NoiseSplit P :=
        ⟨P.take s.before.length,P.drop (s.before.length+1),
          take_noise_drop hP⟩
      refine ⟨.inl t,?_⟩
      apply NoiseSplit.code_injective (P++Q)
      apply Fin.ext
      change (P.take s.before.length).length=s.before.length
      simp [Nat.min_eq_left h.le]
    · have he : (P++Q)[s.before.length]?=some .noise := by
        simpa using congrArg (fun f => f[s.before.length]?) s.word_eq
      have hQ : Q[s.before.length-P.length]?=some .noise := by
        simpa [List.getElem?_append,h] using he
      let t : NoiseSplit Q :=
        ⟨Q.take (s.before.length-P.length),Q.drop (s.before.length-P.length+1),
          take_noise_drop hQ⟩
      refine ⟨.inr t,?_⟩
      apply NoiseSplit.code_injective (P++Q)
      apply Fin.ext
      change (P++Q.take (s.before.length-P.length)).length=s.before.length
      have hs := s.length_bound
      simp only [List.length_append,List.length_take]
      simp only [List.length_append] at hs
      rw [Nat.min_eq_left (by omega)]
      omega

def NoiseSplit.appendEquiv (P Q : List (Letter D)) :
    (NoiseSplit P ⊕ NoiseSplit Q) ≃ NoiseSplit (P++Q) :=
  Equiv.ofBijective (NoiseSplit.appendMap P Q) (NoiseSplit.appendMap_bijective P Q)

end Diagram
end SKGap.Noncrossing

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
namespace InverseDiagram
open Diagram

lemma expandBlocks_injective : Function.Injective expandBlocks := by
  intro p q h
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => rfl
    | cons b q => cases b <;> simp at h
  | cons b p ih =>
    cases q with
    | nil => cases b <;> simp at h
    | cons c q =>
      cases b <;> cases c <;> simp only [expandBlocks_false,
        expandBlocks_true,List.cons.injEq,Letter.diag.injEq,Bool.false_eq_true,
        Bool.true_eq_false,false_and,true_and] at h
      · exact congrArg (false::·) (ih h)
      · exact congrArg (true::·) (ih h)

@[simp] lemma blockDegree_append (p q : List Bool) :
    blockDegree (p++q)=blockDegree p+blockDegree q := by simp [blockDegree]

def SplitBlocks (n : ℕ) := {pq : List Bool × List Bool // blockDegree pq.1+blockDegree pq.2=n}
def SplitChoices (n : ℕ) := Σ k : Fin (n+1), Blocks k.val × Blocks (n-k.val)
def MarkedBlocks (n : ℕ) := Σ bs : Blocks (n+1), NoiseSplit (expandBlocks bs.val)

instance splitChoicesFintype (n : ℕ) : Fintype (SplitChoices n) := inferInstanceAs
  (Fintype (Σ k : Fin (n+1), Blocks k.val × Blocks (n-k.val)))
instance markedBlocksFintype (n : ℕ) : Fintype (MarkedBlocks n) := inferInstanceAs
  (Fintype (Σ bs : Blocks (n+1), NoiseSplit (expandBlocks bs.val)))

def splitChoice (n : ℕ) (z : SplitChoices n) : SplitBlocks n :=
  ⟨(z.2.1.val,z.2.2.val),by
    rw [z.2.1.property,z.2.2.property]
    have h := z.1.isLt
    omega⟩

lemma splitChoice_bijective (n : ℕ) : Function.Bijective (splitChoice n) := by
  constructor
  · rintro ⟨k,p,q⟩ ⟨l,r,s⟩ h
    have hp : p.val=r.val := congrArg (fun z => z.val.1) h
    have hq : q.val=s.val := congrArg (fun z => z.val.2) h
    have hk : k=l := by
      apply Fin.ext
      simpa only [p.property,r.property] using congrArg blockDegree hp
    subst l
    have hp' : p=r := Subtype.ext hp
    have hq' : q=s := Subtype.ext hq
    subst r; subst s; rfl
  · intro p
    refine ⟨⟨⟨blockDegree p.val.1,by have h := p.property; omega⟩,
      ⟨p.val.1,rfl⟩,⟨p.val.2,by
        change blockDegree p.val.2=n-blockDegree p.val.1
        have h := p.property; omega⟩⟩,?_⟩
    rfl

def splitChoiceEquiv (n : ℕ) : SplitChoices n ≃ SplitBlocks n :=
  Equiv.ofBijective (splitChoice n) (splitChoice_bijective n)
instance splitBlocksFintype (n : ℕ) : Fintype (SplitBlocks n) :=
  Fintype.ofEquiv (SplitChoices n) (splitChoiceEquiv n)

def splitToMarked (n : ℕ) (p : SplitBlocks n) : MarkedBlocks n :=
  ⟨⟨p.val.1++(true::p.val.2),by
      simp only [blockDegree_append,blockDegree_true]
      have h := p.property; omega⟩,
    ⟨expandBlocks p.val.1++[.diag true],expandBlocks p.val.2,by
      simp only [expandBlocks_append,expandBlocks_true,List.append_assoc,List.cons_append,
        List.nil_append]⟩⟩

lemma splitToMarked_bijective (n : ℕ) : Function.Bijective (splitToMarked n) := by
  constructor
  · intro p q h
    apply Subtype.ext
    apply Prod.ext
    · apply expandBlocks_injective
      have he := congrArg (fun z : MarkedBlocks n => z.2.before) h
      change expandBlocks p.val.1++[.diag true]=expandBlocks q.val.1++[.diag true] at he
      exact List.append_cancel_right he
    · apply expandBlocks_injective
      exact congrArg (fun z : MarkedBlocks n => z.2.after) h
  · rintro ⟨⟨bs,hbs⟩,s⟩
    obtain ⟨p,q,hpq,hp,hq⟩ := split_noise bs s.before s.after s.word_eq
    have hd : blockDegree p+blockDegree q=n := by
      rw [hpq,blockDegree_append,blockDegree_true] at hbs
      omega
    refine ⟨⟨(p,q),hd⟩,?_⟩
    subst bs
    have hs : (splitToMarked n ⟨(p,q),hd⟩).snd = s := by
      apply NoiseSplit.ext
      · exact hp.symm
      · exact hq.symm
    exact congrArg (Sigma.mk (⟨p++true::q,hbs⟩ : Blocks (n+1))) hs

def markedBlockEquiv (n : ℕ) : SplitChoices n ≃ MarkedBlocks n :=
  (splitChoiceEquiv n).trans (Equiv.ofBijective (splitToMarked n) (splitToMarked_bijective n))

end InverseDiagram
end SKGap.Noncrossing

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_Map
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
namespace Diagram
variable {D E : Type*}

@[simp] lemma map_size (f : D→E) (d : Diagram D) : (d.map f).size=d.size := by
  induction d <;> simp_all [map,size]

lemma fiber_map_injective (f : D→E) (d e : Diagram D)
    (hw : d.word=e.word) (he : d.map f=e.map f) : d=e := by
  induction d generalizing e with
  | nil => cases e <;> simp_all [word,map]
  | diag a d ih =>
    cases e with
    | nil => simp [word] at hw
    | arch u v => simp [word] at hw
    | diag b e =>
      simp only [word,List.cons.injEq,Letter.diag.injEq] at hw
      simp only [map,Diagram.diag.injEq] at he
      obtain ⟨rfl,hw⟩ := hw
      exact congrArg (Diagram.diag a) (ih e hw he.2)
  | arch d r hd hr =>
    cases e with
    | nil => simp [word] at hw
    | diag b e => simp [word] at hw
    | arch u v =>
      simp only [map,Diagram.arch.injEq] at he
      have hlen : d.word.length=u.word.length := by
        simpa only [word_length,map_size] using congrArg Diagram.size he.1
      simp only [word,List.cons.injEq,true_and] at hw
      have hw' := List.append_inj hw hlen
      have hu := hd u hw'.1 he.1
      have hv := hr v (List.cons.inj hw'.2).2 he.2
      subst u; subst v; rfl

lemma exists_map_of_word (f : D→E) (d : Diagram E) (F : List (Letter D))
    (hw : F.map (Letter.map f)=d.word) :
    ∃ e : Diagram D, e.word=F ∧ e.map f=d := by
  induction d generalizing F with
  | nil =>
    have hF : F=[] := List.map_eq_nil_iff.mp hw
    subst F
    exact ⟨.nil,rfl,rfl⟩
  | diag a d ih =>
    cases F with
    | nil => simp [word] at hw
    | cons l F =>
      cases l with
      | noise => simp [Letter.map,word] at hw
      | diag b =>
        simp only [List.map_cons,Letter.map,word,List.cons.injEq,Letter.diag.injEq] at hw
        obtain ⟨e,he,hef⟩ := ih F hw.2
        exact ⟨.diag b e,by simp [word,he],by simp [map,hef,hw.1]⟩
  | arch d e hd he =>
    cases F with
    | nil => simp [word] at hw
    | cons l F =>
      cases l with
      | diag b => simp [Letter.map,word] at hw
      | noise =>
        simp only [List.map_cons,Letter.map,word,List.cons.injEq,true_and] at hw
        obtain ⟨P,Q,hF,hP,hQ⟩ := List.map_eq_append_iff.mp hw
        cases Q with
        | nil => simp at hQ
        | cons l Q =>
          cases l with
          | diag b => simp [Letter.map] at hQ
          | noise =>
            simp only [List.map_cons,Letter.map,List.cons.injEq,true_and] at hQ
            obtain ⟨u,hu,huf⟩ := hd P hP
            obtain ⟨v,hv,hvf⟩ := he Q hQ
            exact ⟨.arch u v,by simp [word,hu,hv,hF],by simp [map,huf,hvf]⟩

def Paired.map (f : D→E) (F : List (Letter D)) (d : Paired F) :
    Paired (F.map (Letter.map f)) := ⟨d.val.map f,by rw [map_word,d.property]⟩
lemma Paired.map_bijective (f : D→E) (F : List (Letter D)) :
    Function.Bijective (Paired.map f F) := by
  constructor
  · intro d e h
    apply Subtype.ext
    exact fiber_map_injective f d.val e.val (d.property.trans e.property.symm)
      (congrArg (fun z => z.val) h)
  · intro d
    obtain ⟨e,he,hef⟩ := exists_map_of_word f d.val F d.property.symm
    exact ⟨⟨e,he⟩,Subtype.ext hef⟩
def Paired.mapEquiv (f : D→E) (F : List (Letter D)) :
    Paired F ≃ Paired (F.map (Letter.map f)) :=
  Equiv.ofBijective (Paired.map f F) (Paired.map_bijective f F)

end Diagram
end SKGap.Noncrossing

end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_Ordinary
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
open Diagram InverseDiagram
namespace WordSeries
variable {ι : Type*} [Fintype ι]

def ordinary (j : ℝ) (F : List (Letter (ι→ℝ))) : ι→ℝ := expect j id F
def chain (j : ℝ) (a : ι→ℝ) (bs : List Bool) : List (Letter (ι→ℝ)) :=
  (expandBlocks bs).map (Letter.map (blockLabel j a))
def inverseCoefficient (j : ℝ) (a : ι→ℝ) (P Q : List (Letter (ι→ℝ))) (n : ℕ) (i : ι) : ℝ :=
  ∑ bs : Blocks n, ordinary j (P++chain j a bs.val++Q) i

@[simp] lemma chain_nil (j : ℝ) (a : ι→ℝ) : chain j a []=[] := rfl
@[simp] lemma chain_append (j : ℝ) (a : ι→ℝ) (p q : List Bool) :
    chain j a (p++q)=chain j a p++chain j a q := by simp [chain]
@[simp] lemma chain_true (j : ℝ) (a : ι→ℝ) (p : List Bool) :
    chain j a (true::p)=.diag a::.noise::chain j a p := rfl
@[simp] lemma chain_false (j : ℝ) (a : ι→ℝ) (p : List Bool) :
    chain j a (false::p)=.diag (fun i => -(j*mean a)*a i)::chain j a p := rfl

lemma blocks_zero (bs : Blocks 0) : bs.val=[] := by
  have h := (mem_blockEnumerate bs.val 0).mpr bs.property
  simpa [blockEnumerate] using h
instance blocksZeroUnique : Unique (Blocks 0) where
  default := ⟨[],rfl⟩
  uniq bs := Subtype.ext (blocks_zero bs)

@[simp] lemma inverseCoefficient_zero (j : ℝ) (a : ι→ℝ)
    (P Q : List (Letter (ι→ℝ))) (i : ι) :
    inverseCoefficient j a P Q 0 i=ordinary j (P++Q) i := by
  simp [inverseCoefficient,blocks_zero]

end WordSeries
end SKGap.Noncrossing

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_InverseSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.WordSeries
open Diagram InverseDiagram PowerSeries
variable {ι : Type*} [Fintype ι]

instance noiseSplitNilIsEmpty {D : Type*} : IsEmpty (NoiseSplit ([] : List (Letter D))) :=
  ⟨fun s => by have h := congrArg List.length s.word_eq; simp at h⟩

def inverseSeries (j : ℝ) (a : ι→ℝ) (P Q : List (Letter (ι→ℝ))) (i : ι) : ℝ⟦X⟧ :=
  PowerSeries.mk (fun n => inverseCoefficient j a P Q n i)
def meanSeries (f : ι→ℝ⟦X⟧) : ℝ⟦X⟧ := C ((Fintype.card ι:ℝ)⁻¹)*(∑ i,f i)
@[simp] lemma coeff_inverseSeries (j : ℝ) (a : ι→ℝ) (P Q : List (Letter (ι→ℝ))) (n : ℕ) (i : ι) :
    coeff n (inverseSeries j a P Q i)=inverseCoefficient j a P Q n i := coeff_mk _ _
@[simp] lemma coeff_meanSeries (f : ι→ℝ⟦X⟧) (n : ℕ) :
    coeff n (meanSeries f)=mean (fun i=>coeff n (f i)) := by
  simp [meanSeries,mean,div_eq_mul_inv,mul_comm]
@[simp] lemma meanSeries_C (f : ι→ℝ) : meanSeries (fun i=>C (f i))=C (mean f) := by
  ext n
  simp only [coeff_meanSeries,coeff_C]
  split_ifs with hn
  · rfl
  · simp [mean]

end SKGap.Noncrossing.WordSeries

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
open Diagram InverseDiagram WordSeries PowerSeries
variable {ι : Type*}

def Letter.toWord : Letter (ι→ℝ)→WordLetter ι
  | .diag d => .diag d
  | .noise => .noise
def liftWord (F : List (Letter (ι→ℝ))) : List (WordLetter ι) := F.map Letter.toWord
@[simp] lemma liftWord_nil : liftWord ([] : List (Letter (ι→ℝ)))=[] := rfl
@[simp] lemma liftWord_cons (l : Letter (ι→ℝ)) (F : List (Letter (ι→ℝ))) :
    liftWord (l::F)=l.toWord::liftWord F := rfl
@[simp] lemma liftWord_append (P Q : List (Letter (ι→ℝ))) : liftWord (P++Q)=liftWord P++liftWord Q := List.map_append
@[simp] lemma inverseCount_lift (F : List (Letter (ι→ℝ))) : inverseCount (liftWord F)=0 := by
  induction F with
  | nil => rfl
  | cons l F ih => cases l <;> simpa [liftWord,Letter.toWord,inverseCount] using ih

@[simp] lemma inverseCount_inverse (F : List (WordLetter ι)) :
    inverseCount (.inverse::F)=inverseCount F+1 := by simp [inverseCount]

def expandWord [Fintype ι] (j : ℝ) (a : ι→ℝ) (bs : List Bool) (F : List (WordLetter ι)) :=
  F.flatMap (fun l=>match l with
    | .diag d => [Letter.diag d]
    | .noise => [.noise]
    | .inverse => chain j a bs)
@[simp] lemma expandWord_lift [Fintype ι] (j : ℝ) (a : ι→ℝ) (bs : List Bool) (F : List (Letter (ι→ℝ))) :
    expandWord j a bs (liftWord F)=F := by
  induction F with
  | nil => rfl
  | cons l F ih => cases l <;> simp [expandWord,liftWord,Letter.toWord] at * <;> exact ih
@[simp] lemma expandWord_oneInverse [Fintype ι] (j : ℝ) (a : ι→ℝ) (bs : List Bool)
    (P Q : List (Letter (ι→ℝ))) :
    expandWord j a bs (liftWord P++(.inverse::liftWord Q))=P++chain j a bs++Q := by
  simp only [expandWord,List.flatMap_append,List.flatMap_cons]
  change expandWord j a bs (liftWord P)++(chain j a bs++expandWord j a bs (liftWord Q))=_
  simp [List.append_assoc]

def literalSeries [Fintype ι] (j : ℝ) (a : ι→ℝ) (F : List (WordLetter ι)) (i : ι) : ℝ⟦X⟧ :=
  if inverseCount F=0 then PowerSeries.C (ordinary j (expandWord j a [] F) i)
  else PowerSeries.mk (fun n=>∑ bs : Blocks n, ordinary j (expandWord j a bs.val F) i)
@[simp] lemma literalSeries_lift [Fintype ι] (j : ℝ) (a : ι→ℝ) (F : List (Letter (ι→ℝ))) (i : ι) :
    literalSeries j a (liftWord F) i=PowerSeries.C (ordinary j F i) := by
  simp [literalSeries]
@[simp] lemma literalSeries_oneInverse [Fintype ι] (j : ℝ) (a : ι→ℝ)
    (P Q : List (Letter (ι→ℝ))) (i : ι) :
    literalSeries j a (liftWord P++(.inverse::liftWord Q)) i=inverseSeries j a P Q i := by
  have hc : inverseCount (liftWord P++(.inverse::liftWord Q))=1 := by simp only [inverseCount_append,inverseCount_inverse,inverseCount_lift,zero_add]
  simp [literalSeries,hc,inverseSeries,inverseCoefficient]

instance noiseSplitDiagIsEmpty {D : Type*} (d : D) : IsEmpty (NoiseSplit [Letter.diag d]) :=
  ⟨fun s => by
    have hle := s.length_bound
    have hp : s.before=[] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    have hh := s.word_eq
    simp [hp] at hh⟩
instance noiseSplitNoiseUnique {D : Type*} : Unique (NoiseSplit [Letter.noise (D := D)]) where
  default := ⟨[],[],rfl⟩
  uniq s := by
    have hle := s.length_bound
    have hp : s.before=[] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    have hq : s.after=[] := by have hh := s.word_eq; simpa [hp] using hh.symm
    apply NoiseSplit.ext <;> assumption

end SKGap.Noncrossing

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordBaseBias
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma wordDiagonal_nil (i : ι) : wordDiagonal [] i=1 := rfl
omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma wordDiagonal_diag (d : ι→ℝ) (F : List (WordLetter ι)) (i : ι) :
    wordDiagonal (.diag d::F) i=d i*wordDiagonal F i := rfl
omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma wordDiagonal_noise (F : List (WordLetter ι)) (i : ι) :
    wordDiagonal (.noise::F) i=wordDiagonal F i := by simp [wordDiagonal]
omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma wordDiagonal_inverse (F : List (WordLetter ι)) (i : ι) :
    wordDiagonal (.inverse::F) i=wordDiagonal F i := by simp [wordDiagonal]

def wordExpected (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ)
    (a : ι→ℝ) (z : ℝ) (F : List (WordLetter ι)) (i : ι) : ℝ :=
  ∫ g : MatrixCoordinates ι→ℝ,actualWord f R hR j a z F (goeMatrix (j/(Fintype.card ι:ℝ)) g) i i
    ∂Measure.pi (fun _=>gaussianReal 0 1)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_ConsDiag
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.Noncrossing.WordSeries.noiseSplitNilIsEmpty _root_.OAI.SKGap.Noncrossing.noiseSplitDiagIsEmpty _root_.OAI.SKGap.Noncrossing.noiseSplitNoiseUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
namespace Diagram
variable {D : Type*}

def Paired.consDiag (a : D) (F : List (Letter D)) (d : Paired F) : Paired (.diag a::F) :=
  ⟨.diag a d.val,by simp [word,d.property]⟩
lemma Paired.consDiag_bijective (a : D) (F : List (Letter D)) :
    Function.Bijective (Paired.consDiag a F) := by
  constructor
  · intro d e h
    apply Subtype.ext
    exact (Diagram.diag.inj (congrArg Subtype.val h)).2
  · intro ⟨d,hd⟩
    cases d with
    | nil => simp [word] at hd
    | arch u v => simp [word] at hd
    | diag b d =>
      change Letter.diag b::d.word=Letter.diag a::F at hd
      obtain ⟨hab,hword⟩ := List.cons.inj hd
      have hab := Letter.diag.inj hab
      subst b
      exact ⟨⟨d,hword⟩,rfl⟩
def Paired.consDiagEquiv (a : D) (F : List (Letter D)) : Paired F ≃ Paired (.diag a::F) :=
  Equiv.ofBijective _ (Paired.consDiag_bijective a F)
def Paired.appendDiag (a : D) (F : List (Letter D)) (d : Paired F) : Paired (F++[.diag a]) :=
  ⟨d.val.append (.diag a .nil),by simp [append_word,d.property,word]⟩
lemma Paired.appendDiag_bijective (a : D) (F : List (Letter D)) :
    Function.Bijective (Paired.appendDiag a F) := by
  constructor
  · intro d e h
    apply Subtype.ext
    exact append_last_diag_injective a (congrArg Subtype.val h)
  · intro ⟨d,hd⟩
    obtain ⟨e,he,hde⟩ := remove_last_diag d F a hd
    exact ⟨⟨e,he⟩,Subtype.ext hde.symm⟩
def Paired.appendDiagEquiv (a : D) (F : List (Letter D)) : Paired F ≃ Paired (F++[.diag a]) :=
  Equiv.ofBijective _ (Paired.appendDiag_bijective a F)
instance pairedNilUnique : Unique (Paired ([] : List (Letter D))) where
  default := ⟨.nil,rfl⟩
  uniq d := by
    apply Subtype.ext
    have h := d.property
    cases hd : d.val <;> simp_all [word]

variable {ι : Type*} [Fintype ι]
@[simp] lemma expect_nil (j : ℝ) (v : D→ι→ℝ) (i : ι) : expect j v [] i=1 := by
  rw [expect,Fintype.sum_unique]
  rfl
@[simp] lemma expect_cons_diag (j : ℝ) (v : D→ι→ℝ) (a : D) (F : List (Letter D)) (i : ι) :
    expect j v (.diag a::F) i=v a i*expect j v F i := by
  unfold expect
  rw [Finset.mul_sum]
  symm
  apply Fintype.sum_equiv (Paired.consDiagEquiv a F)
  intro d
  rfl
end Diagram
namespace WordSeries
open Diagram InverseDiagram
variable {ι : Type*} [Fintype ι]
@[simp] lemma ordinary_nil (j : ℝ) (i : ι) : ordinary j [] i=1 := expect_nil j id i
@[simp] lemma ordinary_cons_diag (j : ℝ) (d : ι→ℝ) (F : List (Letter (ι→ℝ))) (i : ι) :
    ordinary j (.diag d::F) i=d i*ordinary j F i := expect_cons_diag j id d F i
end WordSeries
end SKGap.Noncrossing

end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralSeriesLiftAppend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
open Diagram InverseDiagram WordSeries PowerSeries
variable {ι : Type*} [Fintype ι]

@[simp] lemma literalSeries_lift_append (j : ℝ) (a : ι→ℝ) (P Q : List (Letter (ι→ℝ))) (i : ι) :
    literalSeries j a (liftWord P++liftWord Q) i=C (ordinary j (P++Q) i) := by
  rw [← liftWord_append,literalSeries_lift]
@[simp] lemma literalSeries_two_prefix (j : ℝ) (a : ι→ℝ)
    (P R Q : List (Letter (ι→ℝ))) (i : ι) :
    literalSeries j a (liftWord P++(liftWord R++(.inverse::liftWord Q))) i=
      inverseSeries j a (P++R) Q i := by
  rw [← List.append_assoc,← liftWord_append,literalSeries_oneInverse]
@[simp] lemma literalSeries_two_suffix (j : ℝ) (a : ι→ℝ)
    (P Q R : List (Letter (ι→ℝ))) (i : ι) :
    literalSeries j a ((liftWord P++(.inverse::liftWord Q))++liftWord R) i=
      inverseSeries j a P (Q++R) i := by
  rw [List.append_assoc,List.cons_append,← liftWord_append,literalSeries_oneInverse]
@[simp] lemma literalSeries_cons_inverse (j : ℝ) (a : ι→ℝ)
    (Q : List (Letter (ι→ℝ))) (i : ι) :
    literalSeries j a (.inverse::liftWord Q) i=inverseSeries j a [] Q i := by
  exact literalSeries_oneInverse j a [] Q i

@[simp] lemma literalSeries_lift_fun (j : ℝ) (a : ι→ℝ) (F : List (Letter (ι→ℝ))) :
    literalSeries j a (liftWord F)=(fun i=>C (ordinary j F i)) := by
  funext i; exact literalSeries_lift j a F i
@[simp] lemma literalSeries_oneInverse_fun (j : ℝ) (a : ι→ℝ)
    (P Q : List (Letter (ι→ℝ))) :
    literalSeries j a (liftWord P++(.inverse::liftWord Q))=inverseSeries j a P Q := by
  funext i; exact literalSeries_oneInverse j a P Q i
@[simp] lemma literalSeries_inverse_diag_fun (j : ℝ) (a : ι→ℝ)
    (P : List (Letter (ι→ℝ))) :
    literalSeries j a (liftWord P++[.inverse,.diag a])=inverseSeries j a P [.diag a] := by
  exact literalSeries_oneInverse_fun j a P [.diag a]
@[simp] lemma literalSeries_inverse_single_append (j : ℝ) (a : ι→ℝ)
    (P Q : List (Letter (ι→ℝ))) :
    literalSeries j a (liftWord P++([.inverse]++liftWord Q))=inverseSeries j a P Q := by
  exact literalSeries_oneInverse_fun j a P Q
@[simp] lemma literalSeries_cons_inverse_fun (j : ℝ) (a : ι→ℝ)
    (Q : List (Letter (ι→ℝ))) :
    literalSeries j a (.inverse::liftWord Q)=inverseSeries j a [] Q := by
  exact literalSeries_oneInverse_fun j a [] Q

@[simp] lemma literalSeries_inverse_diag_suffix (j : ℝ) (a : ι→ℝ)
    (P Q : List (Letter (ι→ℝ))) :
    literalSeries j a ((liftWord P++[.inverse,.diag a])++liftWord Q)=
      inverseSeries j a P (.diag a::Q) := by
  rw [List.append_assoc]
  exact literalSeries_oneInverse_fun j a P (.diag a::Q)

end SKGap.Noncrossing

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
open Diagram InverseDiagram WordSeries PowerSeries
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
@[simp] lemma wordDiagonal_diags (D : List (ι→ℝ)) (i : ι) :
    wordDiagonal (liftWord (D.map Letter.diag)) i=(D.map (fun d=>d i)).prod := by
  simp [wordDiagonal,liftWord,Function.comp_def,Letter.toWord]
omit [Fintype ι] in
@[simp] lemma wordDiagonal_append (P Q : List (WordLetter ι)) (i : ι) :
    wordDiagonal (P++Q) i=wordDiagonal P i*wordDiagonal Q i := by simp [wordDiagonal]
omit [Fintype ι] in
@[simp] lemma wordDiagonal_inverse (Q : List (WordLetter ι)) (i : ι) :
    wordDiagonal (.inverse::Q) i=wordDiagonal Q i := by simp [wordDiagonal]

end SKGap.Noncrossing

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianRegression
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal
namespace SKGap.GaussianRegression

def matrixCLM {ι κ : Type*} [Fintype κ] (A : Matrix ι κ ℝ) :
    (κ → ℝ) →L[ℝ] (ι → ℝ) := A.mulVecLin.toContinuousLinearMap

@[simp] lemma matrixCLM_apply {ι κ : Type*} [Fintype κ] (A : Matrix ι κ ℝ) (x : κ → ℝ) :
    matrixCLM A x = A *ᵥ x := rfl

end SKGap.GaussianRegression
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GOEGaussian
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def goeEntryCoeff (r : ℝ) : Matrix (ι × ι) (MatrixCoordinates ι) ℝ :=
  fun p a => sqrt (2*r)/2 * ((if a=Sum.inl p then 1 else 0)+
    (if a=Sum.inl (p.2,p.1) then 1 else 0))

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ProjectedMarkedIBP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def markedError (r R : ℝ) (L K B C : NNReal) (D E p : ℝ) : ℝ :=
  B*R*C*p+B*C*(Fintype.card ι:ℝ)^2*sqrt (2*r)*sqrt p+
    (Fintype.card ι:ℝ)^2*(sqrt (2*r)*((L*C+B*K:NNReal)*
      (⟨sqrt (2*r),sqrt_nonneg _⟩*(Fintype.card (MatrixCoordinates ι):NNReal)^(1/(2:ℝ≥0∞)).toReal):NNReal)+
      r*(D*C+B*E))*p

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_MarkedErrorRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped NNReal ENNReal

def markedRateConstant (j R c : ℝ) (L K B C : NNReal) (D E : ℝ) : ℝ :=
  (B:ℝ)*R*C*(3/c)+B*C*sqrt (2*j)*(sqrt 3*6/(c/2)^3)+
    (2*(sqrt (2*j))^2*(L*C+B*K:NNReal)+j*(D*C+B*E))*(360/c^5)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordLeading
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def wordAverageExpected (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ)
    (a : ι→ℝ) (z : ℝ) (F : List (WordLetter ι)) : ℝ :=
  (∑ i,wordExpected f hR j a z F i)/(Fintype.card ι:ℝ)

def wordLeadingCost (j B : ℝ) (u v q : ℕ) : ℝ :=
  j*(B^u*B^q*((2*exp (π^2/8))*((v:ℝ)*B^v)*sqrt (2*j))+B^u*B^v*B^q)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def wordDifferentialBound (B : NNReal) (A z : ℝ) (k : ℕ) : ℝ :=
  (1+|z| *A*(B:ℝ)^2)*(wordParameterCoeff B k:ℝ)*2

def actualWordLoop (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (P Q : List (WordLetter ι)) (M : Matrix ι ι ℝ) (i : ι) : ℝ :=
    ((wordPartners a P).map (WordCut.leftContraction f hR j a z M (actualWord f R hR j a z Q M) i)).sum+
    ((wordPartners a Q).map (WordCut.rightContraction f hR j a z M (actualWord f R hR j a z P M) i)).sum

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordLoopLeading
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def wordRecursionAtExpected (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ)
    (a : ι→ℝ) (z : ℝ) (P Q : List (WordLetter ι)) (i : ι) : ℝ :=
  ((wordRecursionAt a P Q).map (fun t=>(if t.inversePartner then z else 1)*j*
    wordAverageExpected f hR j a z t.inner*wordExpected f hR j a z t.outer i)).sum

def wordRecursionAtCost (j B z : ℝ) (a : ι→ℝ) (P Q : List (WordLetter ι)) : ℝ :=
  ((wordPartners a P).map (fun c=>|if c.inversePartner then z else 1| *
    wordLeadingCost j B c.left.length c.right.length Q.length)).sum+
  ((wordPartners a Q).map (fun c=>|if c.inversePartner then z else 1| *
    wordLeadingCost j B P.length c.left.length c.right.length)).sum

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordExpectedRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap

def wordMarkedCost (B : NNReal) (j R A c z : ℝ) (p q : ℕ) : ℝ :=
  markedRateConstant j R c ((p:NNReal)*B^p) ((q:NNReal)*B^q) (B^p) (B^q)
    (wordDifferentialBound B A z p) (wordDifferentialBound B A z q)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_WordPredictionStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def wordAverage (e : List (WordLetter ι)→ι→ℝ) (F : List (WordLetter ι)) : ℝ :=
  (∑ k,e F k)/(Fintype.card ι:ℝ)
def wordRecursionValue (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (e : List (WordLetter ι)→ι→ℝ) (F : List (WordLetter ι)) (i : ι) : ℝ :=
  ((wordRecursionTerms a F).map (fun t=>(if t.inversePartner then z else 1)*j*
    wordAverage e t.inner*e t.outer i)).sum

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordBiasInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Set
open scoped BigOperators

def wordBiasConstant (L : ℕ) (j B C : ℝ) : ℕ → ℝ
  | 0 => C
  | k+1 => C+(L:ℝ)*j*(2*B+wordBiasConstant L j B C k)*wordBiasConstant L j B C k+
      wordBiasConstant L j B C k

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_AffineBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def affineRight (F : Matrix ι ι ℝ → Matrix ι ι ℝ) (d e : ι → ℝ)
    (w : ℝ) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ := F M*diagonal d-diagonal e-w • M

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianProductPower
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

def matrixEntryMean (F : EuclideanSpace ℝ κ→Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i k=>∫ g : κ→ℝ,F (WithLp.toLp 2 g) i k ∂Measure.pi (fun _=>gaussianReal 0 1)
def matrixCentered (F : EuclideanSpace ℝ κ→Matrix ι ι ℝ) (x : EuclideanSpace ℝ κ) :=
  F x-matrixEntryMean F

def matrixNormConstant : ℝ := 1+48*exp (π^2/8)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RealParameterIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Matrix Real Set
open scoped Matrix.Norms.Frobenius SchwartzMap
namespace SKGap.ComplexMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def kChange (f : 𝓢(ℝ,ℂ)) (R : ℝ) (B B' D D' C C' : Matrix ι ι ℂ) : ℝ :=
  gChange f R B B' D D'*(R+opNorm C)+gBound f D'*opNorm (C-C')
end SKGap.ComplexMatrix
end
end

section
noncomputable section
namespace SKGap.ComplexMatrix
open Matrix Real
open scoped Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def parameterGC (f : 𝓢(ℝ,ℂ)) (R V H : ℝ) : ℝ :=
  2*V*fourierMoment f 0+V^2*fl1 f*(H+2*V*R)
def parameterGM (f : 𝓢(ℝ,ℂ)) (R V H : ℝ) : ℝ :=
  2*V*fl1 f*V^2+V^2*(fl1 f*(2*V)+fl2 f*(2*(H+2*V*R))*V^2)
def parameterKC (f : 𝓢(ℝ,ℂ)) (R V T H : ℝ) : ℝ :=
  parameterGC f R V H*(R+T)+V^2*fourierMoment f 0
def parameterKM (f : 𝓢(ℝ,ℂ)) (R V T H : ℝ) : ℝ :=
  parameterGM f R V H*(R+T)+fl1 f*V^4+parameterGC f R V H

end SKGap.ComplexMatrix
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
def WordLetter.close (δ : ℝ) : WordLetter ι→WordLetter ι→Prop
  | .diag d,.diag e => ∀ i,|d i-e i|≤δ
  | .noise,.noise => True
  | .inverse,.inverse => True
  | _,_ => False

def wordHolderScale (f : 𝓢(ℝ,ℂ)) (R j A : ℝ) : ℝ :=
  (1+j)*(1+|ComplexMatrix.parameterKC f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2)|+
    |ComplexMatrix.parameterKM f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2)|)

lemma wordHolderScale_ge_one (f : 𝓢(ℝ,ℂ)) (R A : ℝ) {j : ℝ} (hj : 0≤j) :
    1≤wordHolderScale f R j A := by
  unfold wordHolderScale
  nlinarith [abs_nonneg (ComplexMatrix.parameterKC f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2)),
    abs_nonneg (ComplexMatrix.parameterKM f R (sqrt A) (j*A) (2*sqrt A*(j*A)+(sqrt A)^2))]

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

inductive WordTemplateLetter (m : ℕ) where
  | diag : Fin m→WordTemplateLetter m
  | noise : WordTemplateLetter m
  | inverse : WordTemplateLetter m
  deriving DecidableEq, Fintype

abbrev WordParameter (m : ℕ) (ι : Type*) := (Option (Fin m)×ι)→Icc (0:ℝ) 1

def templateInverse (A : ℝ) (θ : WordParameter m ι) (i : ι) : ℝ := A*(θ (none,i):ℝ)
def templateDiagonal (D : ℝ) (θ : WordParameter m ι) (k : Fin m) (i : ι) : ℝ :=
  D*(2*(θ (some k,i):ℝ)-1)
def WordTemplateLetter.realize (D : ℝ) (θ : WordParameter m ι) : WordTemplateLetter m→WordLetter ι
  | .diag k => .diag (templateDiagonal D θ k)
  | .noise => .noise
  | .inverse => .inverse

def templateWord (D : ℝ) (θ : WordParameter m ι) (F : List (WordTemplateLetter m)) :=
  F.map (WordTemplateLetter.realize D θ)

def templateScale (A D : ℝ) : ℝ := 1+A+2*D

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_GlobalWordIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def globalWordHolder (f : 𝓢(ℝ,ℂ)) (R j A D : ℝ) : ℝ :=
  wordHolderScale f R j A+2*actualWordBound f R j A D+1
lemma globalWordHolder_nonneg (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    0 ≤ globalWordHolder f R j A D := by
  have hh := wordHolderScale_ge_one f R A hj
  have hb := actualWordBound_pos f hR hj hA hD
  dsimp [globalWordHolder]
  linarith

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_GeneralTemplateRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

def generalTemplateMatrix (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (j A D : ℝ)
    (F : List (WordTemplateLetter m)) (θ : WordParameter m ι) : Matrix ι ι ℝ→Matrix ι ι ℝ :=
  actualWord f R hR j (templateInverse A θ) 1 (templateWord D θ F)

def generalTemplateHolder (f : 𝓢(ℝ,ℂ)) (R j A D : ℝ) : ℝ :=
  globalWordHolder f R j A D*sqrt (templateScale A D)

lemma generalTemplateHolder_nonneg (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    0 ≤ generalTemplateHolder f R j A D :=
  mul_nonneg (globalWordHolder_nonneg f hR hj hA hD) (sqrt_nonneg _)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_MatrixNormTail
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

def matrixWordSeminorm (p : Bool) (M : Matrix ι ι ℝ) : ℝ :=
  if p then offDiagonalSeminorm M else diagonalSeminorm M
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_IntervalMesh
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Set Filter Real
open scoped Topology

def intervalMeshPoint (k : ℕ) (i : Fin (4^k+1)) : ℝ := (i:ℝ)/(4:ℝ)^k

lemma intervalMeshPoint_mem (k : ℕ) (i : Fin (4^k+1)) :
    intervalMeshPoint k i ∈ Icc (0:ℝ) 1 := by
  constructor
  · unfold intervalMeshPoint;positivity
  · unfold intervalMeshPoint
    apply (div_le_one (by positivity : (0:ℝ)<4^k)).mpr
    exact_mod_cast (Nat.le_of_lt_succ i.isLt)

def intervalMeshIndex (t : Icc (0:ℝ) 1) (k : ℕ) : Fin (4^k+1) :=
  ⟨⌊(t:ℝ)*(4:ℝ)^k⌋₊,Nat.lt_succ_of_le (Nat.floor_le_of_le (by
    have hh := mul_le_mul_of_nonneg_right t.property.2 (show (0:ℝ) ≤ 4^k by positivity)
    simpa only [one_mul,Nat.cast_pow,Nat.cast_ofNat] using hh))⟩

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Set Filter Real
open scoped Topology BigOperators
variable {α : Type*}

def boxMeshPoint (k : ℕ) (v : α→Fin (4^k+1)) : α→Icc (0:ℝ) 1 :=
  fun i=>⟨intervalMeshPoint k (v i),intervalMeshPoint_mem k (v i)⟩
def boxMeshIndex (θ : α→Icc (0:ℝ) 1) (k : ℕ) : α→Fin (4^k+1) := fun i=>intervalMeshIndex (θ i) k

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_BoxChaining
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal Topology
variable {α : Type*} [Fintype α] [DecidableEq α]

def boxMeshEdges (k : ℕ) : Finset ((α→Fin (4^k+1))×(α→Fin (4^(k+1)+1))) :=
  Finset.univ.filter (fun e=>dist (boxMeshPoint (k+1) e.2) (boxMeshPoint k e.1)≤2*(1/4:ℝ)^k)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianMatrixChaining
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Matrix.Norms.Frobenius Topology
variable {κ α : Type*} [Fintype κ] [Fintype α] [DecidableEq α]

def gaussianMatrixChainConstant (H B : ℝ) : ℝ :=
  5*(matrixNormConstant*H+π*H*sqrt (B+1))

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_TemplatePatterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open scoped BigOperators

def wordPatternSet (m : ℕ) : ℕ→Finset (List (WordTemplateLetter m))
  | 0 => {[]}
  | L+1 => insert [] ((Finset.univ×ˢ wordPatternSet m L).image (fun p=>p.1::p.2))

@[simp] lemma mem_wordPatternSet {m L : ℕ} (F : List (WordTemplateLetter m)) :
    F∈wordPatternSet m L ↔ F.length ≤ L := by
  induction L generalizing F with
  | zero => simp [wordPatternSet]
  | succ L ih =>
    cases F with
    | nil => simp [wordPatternSet]
    | cons l F =>
      simp only [wordPatternSet,Finset.mem_insert,List.cons_ne_nil,Finset.mem_image,
        Finset.mem_product,Finset.mem_univ,true_and,Prod.exists,List.cons.injEq,false_or]
      constructor
      · rintro ⟨a,G,hG,ha,hFG⟩
        subst a G
        exact Nat.succ_le_succ ((ih F).mp hG)
      · intro h
        exact ⟨l,F,(ih F).mpr (Nat.le_of_succ_le_succ h),rfl,rfl⟩
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordTemplateSurjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*}

def inverseChart {A : ℝ} (hA : 0<A) (a : ℝ) (ha : a∈Icc 0 A) : Icc (0:ℝ) 1 :=
  ⟨a/A,div_nonneg ha.1 hA.le,(div_le_one hA).mpr ha.2⟩

def diagonalChart {D : ℝ} (hD : 0<D) (d : ℝ) (hd : |d|≤D) : Icc (0:ℝ) 1 := by
  refine ⟨(d/D+1)/2,?_,?_⟩
  · have hh : -1≤d/D := (le_div_iff₀ hD).mpr (by linarith [(abs_le.mp hd).1])
    linarith
  · have hh : d/D≤1 := (div_le_one hD).mpr (abs_le.mp hd).2
    linarith

def WordLetter.diagonalValue (i : ι) : WordLetter ι→ℝ
  | .diag d => d i
  | _ => 0
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_GOEDiagonalSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def removeDiagonal (M : Matrix ι ι ℝ) : Matrix ι ι ℝ := M-Matrix.diagonal (fun i=>M i i)
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_GOESubmatrix
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators RealInnerProductSpace
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def matrixCoordinatesEmbedding (e : κ ↪ ι) : MatrixCoordinates κ ↪ MatrixCoordinates ι :=
  (e.prodMap e).sumMap e

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_PathAgreement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pathFeature (p : Bool) (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R)
    (j : ℝ) (a : ι → ℝ) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  if p then realProject R hR M*pathK f R hR j a 1 M else pathK f R hR j a 1 M

def pathFeatureLip (f : 𝓢(ℝ,ℂ)) (R j A : ℝ) : ℝ :=
  pathLip f R j A+pathBound f R j A+R*pathLip f R j A

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_WordStableAgreement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def WordLetter.exactEval (j : ℝ) (a : ι→ℝ) : WordLetter ι→Matrix ι ι ℝ→Matrix ι ι ℝ
  | .diag d,_ => diagonal d
  | .noise,M => M
  | .inverse,M => (1-diagonal a*(M-((j/(Fintype.card ι:ℝ))*∑ b,a b) • 1))⁻¹

def exactWord (j : ℝ) (a : ι→ℝ) (F : List (WordLetter ι)) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  matrixFactorProduct (F.map (WordLetter.exactEval j a)) M

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordDiagUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Polynomial
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

def wordPredictionPolynomial (j : ℝ) (a : ι→ℝ) (F : List (WordLetter ι)) (i : ι) : ℝ[X] :=
  if ordinaryCount F=0 then C (wordDiagonal F i) else
    ((wordRecursionTerms a F).attach.map (fun th=>
      (if th.val.inversePartner then X else 1)*C j*
        (C ((Fintype.card ι:ℝ)⁻¹)*(∑ k,wordPredictionPolynomial j a th.val.inner k))*
          wordPredictionPolynomial j a th.val.outer i)).sum
termination_by ordinaryCount F
decreasing_by
  · exact (wordRecursionTerms_decreases a F th.val th.property).2
  · exact (wordRecursionTerms_decreases a F th.val th.property).1

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_PrimaryMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary
open WordSeries
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixLetter (J : Matrix ι ι ℝ) : Letter (ι→ℝ) → Matrix ι ι ℝ
  | .diag a => Matrix.diagonal a
  | .noise => J

def matrixWord (J : Matrix ι ι ℝ) (F : List (Letter (ι→ℝ))) : Matrix ι ι ℝ :=
  (F.map (matrixLetter J)).prod

def matrixPolynomial (J : Matrix ι ι ℝ) (P : WordPolynomial (ι:=ι)) : Matrix ι ι ℝ :=
  (P.map (fun p => p.1 • matrixWord J p.2)).sum

def primaryMatrix (j : ℝ) (J : Matrix ι ι ℝ) (a : ℕ→ι→ℝ) : ℕ → Matrix ι ι ℝ
  | 0 => 1
  | 1 => J
  | n+2 => J*Matrix.diagonal (a n)*primaryMatrix j J a (n+1) -
      (j*Diagram.mean (a n)) • (Matrix.diagonal (previousDiagonal a n)*primaryMatrix j J a n)

def coefficientMass (P : WordPolynomial (ι:=ι)) : ℝ := (P.map (fun p=>|p.1|)).sum

omit [DecidableEq ι]

def massBound (j : ℝ) : ℕ→ℝ
  | 0 => 1
  | 1 => 1
  | n+2 => massBound j (n+1)+|j| *massBound j n

end SKGap.Noncrossing.Primary
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PrimaryDifferentiation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Primary
open SKGap Matrix
variable {n : ℕ}

def primaryState (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) :
    ℕ → VectorFields n × VectorFields n
  | 0 => (spin,fun x i => h i+∑ a,J i a*spin x a)
  | k+1 =>
      let s := primaryState j J h k
      let m : VectorFields n := fun x i => Real.tanh (s.2 x i)
      let b : Spin n→ℝ := siteMean (fun x i => 1-(m x i)^2)
      (m,fun x i => h i+∑ a,J i a*m x a-j*b x*s.1 x i)

def primaryDiagonal (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) :
    ℕ→Fin n→ℝ := fun k i => scalarVariance ((primaryState j J h k).2 x i)

def formalField (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) (k : ℕ) :
    Interaction n :=
  SKGap.Noncrossing.Primary.primaryMatrix j J (primaryDiagonal j J h x) (k+1)

def formalMag (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) : ℕ→Interaction n
  | 0 => 1
  | k+1 => Matrix.diagonal (primaryDiagonal j J h x k)*formalField j J h x k

def differentiationBound (j R B : ℝ) : ℕ→ℝ
  | 0 => B+1
  | k+1 =>
    let C := differentiationBound j R B k
    let T := C+8*C^2
    let Q := 2*T+4*T^2
    B+1+(R*T+|j| *(C+Q+2*C*Q))+T

lemma differentiationBound_nonneg {j R B : ℝ} (hR : 0≤R) (hB : 0≤B) (k : ℕ) :
    0≤differentiationBound j R B k := by
  induction k with
  | zero => dsimp [differentiationBound]; positivity
  | succ k hk => dsimp only [differentiationBound]; positivity

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_OrdinaryGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary
open Diagram
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

inductive SourceTree (D : Type*) where
  | leaf : ℝ → SourceTree D
  | branch : D → SourceTree D → SourceTree D → SourceTree D

namespace SourceTree
variable {D : Type*}

def leafMass : SourceTree D→ℝ
  | .leaf c => c
  | .branch _ _ b => leafMass b

def words (j : ℝ) : SourceTree (ι→ℝ)→WordPolynomial (ι:=ι)×WordPolynomial (ι:=ι)
  | .leaf c => ([(c,[])],[(c,[.noise])])
  | .branch p a b =>
      (prependWords [.diag p] (words j a).2 ++ (words j b).1,
       (prependWords [.noise,.diag p] (words j a).2 ++
          scale (-(j*Diagram.mean p)) (words j a).1) ++ (words j b).2)

def sourceOperator (j : ℝ) (t : SourceTree (ι→ℝ)) := polynomialOperator j (t.words j).1
def fieldOperator (j : ℝ) (t : SourceTree (ι→ℝ)) := polynomialOperator j (t.words j).2

def sourceMatrix (j : ℝ) (J : Matrix ι ι ℝ) (t : SourceTree (ι→ℝ)) :=
  matrixPolynomial J (t.words j).1
def fieldMatrix (j : ℝ) (J : Matrix ι ι ℝ) (t : SourceTree (ι→ℝ)) :=
  matrixPolynomial J (t.words j).2
end SourceTree
end SKGap.Noncrossing.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_CoefficientRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

structure SmallBound (U : VectorFields n) (x : Spin n) (C : ℝ) : Prop where
  nonneg : 0≤C
  size : vectorNorm (U x)≤C
  derivative : ‖derivativeMatrix U x‖≤C

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_OrdinaryRecipe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

structure OrdinaryData (n : ℕ) (ι κ σ : Type*) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] where
  J : Interaction n
  j : ℝ
  H : ι→VectorFields n
  predecessor : ι→VectorFields n
  θ : κ→Spin n→ℝ
  seed : σ→Fin n→ℝ
  seedFunction : ℕ→σ→Fin n→Args (ι:=ι) (κ:=κ)→ℝ
  seedDerivative : ℕ→σ→Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ
  auxFunction : (a : ℕ)→Fin a→Fin n→Args (ι:=ι) (κ:=κ)→ℝ
  auxDerivative : (a : ℕ)→Fin a→Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ

namespace OrdinaryData
variable (D : OrdinaryData n ι κ σ)

def seedCoefficient (a : ℕ) (s : σ) : VectorFields n := coefficient D.H D.θ (D.seedFunction a s)
def auxCoefficient (a : ℕ) (b : Fin a) : VectorFields n := coefficient D.H D.θ (D.auxFunction a b)
def seedPartial (a : ℕ) (l : ι) (s : σ) : VectorFields n := localPartial D.H D.θ (D.seedDerivative a s) (.inl l)
def auxPartial (a : ℕ) (l : ι) (b : Fin a) : VectorFields n := localPartial D.H D.θ (D.auxDerivative a b) (.inl l)

def sourceOf (a : ℕ) (Y : Fin a→VectorFields n) : VectorFields n := fun x i=>
  (∑s,D.seedCoefficient a s x i*D.seed s i)+(∑b,D.auxCoefficient a b x i*Y b x i)

def partialOf (a : ℕ) (l : ι) (Y : Fin a→VectorFields n) : VectorFields n := fun x i=>
  (∑s,D.seedPartial a l s x i*D.seed s i)+(∑b,D.auxPartial a l b x i*Y b x i)

def fieldOf (a : ℕ) (W Y : Fin a→VectorFields n) : VectorFields n := fun x i=>
  D.J.mulVec (D.sourceOf a Y x) i-
    D.j*(∑l,siteMean (D.partialOf a l Y) x*D.predecessor l x i)-
    D.j*∑b,siteMean (D.auxCoefficient a b) x*W b x i

end OrdinaryData

structure CoefficientBound (a : VectorFields n) (x : Spin n) (A R : ℝ) : Prop where
  size_nonneg : 0≤A
  row_nonneg : 0≤R
  value : ∀i,|a x i|≤A
  difference : ∀i,∑k,(derivativeMatrix a x i k)^2≤R^2

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RecipeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.SourceTree
open Diagram
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def branches : List ((ι→ℝ)×SourceTree (ι→ℝ))→SourceTree (ι→ℝ)
  | [] => .leaf 0
  | (p,t)::ts => .branch p t (branches ts)

end SKGap.Noncrossing.Primary.SourceTree
namespace SKGapCutoff.Primary
open SKGap.Noncrossing.Primary
variable {n : ℕ}

def primaryTree (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) : ℕ→SourceTree (Fin n→ℝ)
  | 0 => .leaf 1
  | k+1 => .branch (primaryDiagonal j J h x k) (primaryTree j J h x k) (.leaf 0)

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_FockTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor
open Diagram
variable {ι : Type*} [Fintype ι]
abbrev Space := ι→List ι→ℝ

def tensorValue : List (ι→ℝ)→List ι→ℝ
  | [],[] => 1
  | a::A,i::I => a i*tensorValue A I
  | _,_ => 0

def realize : Primary.Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι) :=
  Finsupp.linearCombination ℝ (fun s i I =>s.1 i*tensorValue s.2 I)

def diagonal (a : ι→ℝ) : Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι) where
  toFun v i I := a i*v i I
  map_add' v w := by ext i I; simp [mul_add]
  map_smul' c v := by ext i I; simp [mul_left_comm]
def creation : Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι) where
  toFun v i I := match I with | [] => 0 | q::Q => v q Q
  map_add' v w := by ext i I; cases I <;> simp
  map_smul' c v := by ext i I; cases I <;> simp
def annihilation : Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι) where
  toFun v i I := Diagram.mean (fun q =>v q (i::I))
  map_add' v w := by ext i I; simp [Diagram.mean,Finset.sum_add_distrib,add_div]
  map_smul' c v := by ext i I; simp [Diagram.mean,←Finset.mul_sum,mul_div_assoc]
def noise (j : ℝ) : Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι) := creation+j • annihilation
def project : Space (ι:=ι)→ₗ[ℝ] (ι→ℝ) where
  toFun v i := v i []
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def vacuum : Space (ι:=ι) := realize Primary.vacuum

def letter (j : ℝ) : Letter (ι→ℝ)→Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι)
  | .diag a => diagonal a
  | .noise => noise j
def word (j : ℝ) : List (Letter (ι→ℝ))→Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι)
  | [] => LinearMap.id
  | a::F => (letter j a).comp (word j F)

end SKGap.Noncrossing.Primary.Tensor

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_LoopPrediction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor.Loop
open Diagram InverseDiagram WordSeries
variable {ι : Type*} [Fintype ι]

def blockPrepend (n : ℕ) : Blocks (n+1) ⊕ Blocks n → Blocks (n+2)
  | .inl bs => ⟨true::bs.val,by rw [blockDegree_true,bs.property]⟩
  | .inr bs => ⟨false::bs.val,by rw [blockDegree_false,bs.property]⟩

lemma blocks_one (bs : Blocks 1) : bs.val=[true] := by
  have h := (mem_blockEnumerate bs.val 1).mpr bs.property
  simpa [blockEnumerate] using h
instance blocksOneUnique : Unique (Blocks 1) where
  default := ⟨[true],rfl⟩
  uniq bs := Subtype.ext (blocks_one bs)

def kernel (j : ℝ) (a : ι→ℝ) (n : ℕ) : Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι) :=
  ∑ bs : Blocks n,word j (chain j a bs.val)
end SKGap.Noncrossing.Primary.Tensor.Loop

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_FockSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor.Series
open Diagram InverseDiagram WordSeries Loop
variable {ι : Type*}
abbrev Seq := ℕ→Space (ι:=ι)

def ofVector (v : Space (ι:=ι)) : Seq (ι:=ι) := fun n => if n=0 then v else 0

def shift : Seq (ι:=ι)→ₗ[ℝ] Seq (ι:=ι) where
  toFun v n := match n with | 0 => 0 | n+1 => v n
  map_add' _ _ := by ext n i I; cases n <;> simp
  map_smul' _ _ := by ext n i I; cases n <;> simp

def act (A : Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι)) : Seq (ι:=ι)→ₗ[ℝ] Seq (ι:=ι) where
  toFun v n := A (v n)
  map_add' _ _ := by funext n; exact A.map_add _ _
  map_smul' _ _ := by funext n; exact A.map_smul _ _

@[simp] lemma shift_zero (v : Seq (ι:=ι)) : shift v 0=0 := rfl
@[simp] lemma shift_succ (v : Seq (ι:=ι)) (n : ℕ) : shift v (n+1)=v n := rfl
@[simp] lemma act_apply (A : Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι)) (v : Seq (ι:=ι)) (n : ℕ) :
    act A v n=A (v n) := rfl

variable [Fintype ι]

def inverseSeq (j : ℝ) (a : ι→ℝ) (v : Seq (ι:=ι)) : Seq (ι:=ι)
  | 0 => v 0
  | 1 => v 1+diagonal a (noise j (v 0))
  | n+2 => v (n+2)+diagonal a (noise j (inverseSeq j a v (n+1)))-
      (j*Diagram.mean a) • diagonal a (inverseSeq j a v n)

lemma inverseSeq_add (j : ℝ) (a : ι→ℝ) (v w : Seq (ι:=ι)) :
    inverseSeq j a (v+w)=inverseSeq j a v+inverseSeq j a w := by
  funext n
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simp only [inverseSeq,Pi.add_apply,map_add]; abel
  | more n ih0 ih1 =>
    simp only [inverseSeq,Pi.add_apply] at ih0 ih1 ⊢
    rw [ih0,ih1]
    simp only [map_add,smul_add]
    abel
lemma inverseSeq_smul (j c : ℝ) (a : ι→ℝ) (v : Seq (ι:=ι)) :
    inverseSeq j a (c • v)=c • inverseSeq j a v := by
  funext n
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [inverseSeq,map_smul,smul_add]
  | more n ih0 ih1 =>
    simp only [inverseSeq,Pi.smul_apply] at ih0 ih1 ⊢
    rw [ih0,ih1]
    simp only [map_smul,smul_add,smul_sub,smul_smul]
    rw [mul_comm (j*Diagram.mean a) c]

def inverse (j : ℝ) (a : ι→ℝ) : Seq (ι:=ι)→ₗ[ℝ] Seq (ι:=ι) where
  toFun := inverseSeq j a
  map_add' := inverseSeq_add j a
  map_smul' c v := inverseSeq_smul j c a v

end SKGap.Noncrossing.Primary.Tensor.Series

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor.Series
open Diagram Loop
variable {ι : Type*} [Fintype ι]

def branchSource (p : ι→ℝ) (U V : Seq (ι:=ι)×Seq (ι:=ι)) : Seq (ι:=ι) :=
  act (diagonal p) U.2+V.1
def branchField (j : ℝ) (p : ι→ℝ) (U V : Seq (ι:=ι)×Seq (ι:=ι)) : Seq (ι:=ι) :=
  shift (act (noise j) (act (diagonal p) U.2))-
    (j*Diagram.mean p) • shift (shift U.1)+V.2

def ordinary (j : ℝ) : SourceTree (ι→ℝ)→Seq (ι:=ι)×Seq (ι:=ι)
  | .leaf c => (ofVector (c • vacuum),shift (ofVector (c • noise j vacuum)))
  | .branch p t u => (branchSource p (ordinary j t) (ordinary j u),
      branchField j p (ordinary j t) (ordinary j u))

def loopSource (j : ℝ) (a p : ι→ℝ) (t : SourceTree (ι→ℝ)) : Seq (ι:=ι) :=
  inverse j a (act (diagonal p) (ordinary j t).2-
    (j*Diagram.mean p) • shift (shift (act (diagonal a) (ordinary j t).1)))
def loopField (j : ℝ) (a p : ι→ℝ) (t : SourceTree (ι→ℝ)) : Seq (ι:=ι) :=
  shift (act (noise j) (loopSource j a p t))-
    (j*Diagram.mean a) • shift (shift (loopSource j a p t))-
    (j*Diagram.mean p) • shift (shift (ordinary j t).1)

inductive ClosedTree (D : Type*) where
  | leaf : ℝ→ClosedTree D
  | implicit : D→SourceTree D→ClosedTree D
  | branch : D→ClosedTree D→ClosedTree D→ClosedTree D

def ClosedTree.series (j : ℝ) (a : ι→ℝ) : ClosedTree (ι→ℝ)→Seq (ι:=ι)×Seq (ι:=ι)
  | .leaf c => ordinary j (.leaf c)
  | .implicit p t => (loopSource j a p t,loopField j a p t)
  | .branch p t u => (branchSource p (t.series j a) (u.series j a),
      branchField j p (t.series j a) (u.series j a))

def ClosedTree.leafMass {D : Type*} : ClosedTree D→ℝ
  | .leaf c => c
  | .implicit _ _ => 0
  | .branch _ _ u => u.leafMass

end SKGap.Noncrossing.Primary.Tensor.Series

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordFockSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor.Series
open Diagram InverseDiagram WordSeries Loop
variable {ι : Type*} [Fintype ι]

def wordOperator (j : ℝ) (a : ι→ℝ) : List (WordLetter ι)→Seq (ι:=ι)→ₗ[ℝ] Seq (ι:=ι)
  | [] => LinearMap.id
  | .diag d::F => (act (diagonal d)).comp (wordOperator j a F)
  | .noise::F => (act (noise j)).comp (wordOperator j a F)
  | .inverse::F => (inverse j a).comp (wordOperator j a F)

def wordSeq (j : ℝ) (a : ι→ℝ) (F : List (WordLetter ι)) : Seq (ι:=ι) :=
  wordOperator j a F (ofVector vacuum)

end SKGap.Noncrossing.Primary.Tensor.Series

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor.Series
open Diagram InverseDiagram WordSeries Loop
variable {ι : Type*} [Fintype ι]

def shifts : ℕ→Seq (ι:=ι)→ₗ[ℝ] Seq (ι:=ι)
  | 0 => LinearMap.id
  | n+1 => shift.comp (shifts n)

def letterOperator (j : ℝ) (a : ι→ℝ) : WordLetter ι→Seq (ι:=ι)→ₗ[ℝ] Seq (ι:=ι)
  | .diag d => act (diagonal d)
  | .noise => act (noise j)
  | .inverse => inverse j a

abbrev GradedWords (ι : Type*) := List (ℝ×ℕ×List (WordLetter ι))
namespace GradedWords

def scalar (c : ℝ) : GradedWords ι := [(c,0,[])]
def scale (c : ℝ) (P : GradedWords ι) : GradedWords ι := P.map (fun t=>(c*t.1,t.2))
def bump (P : GradedWords ι) : GradedWords ι := P.map (fun t=>(t.1,t.2.1+1,t.2.2))
def prepend (l : WordLetter ι) (P : GradedWords ι) : GradedWords ι := P.map (fun t=>(t.1,t.2.1,l::t.2.2))
def seq (j : ℝ) (a : ι→ℝ) (P : GradedWords ι) : Seq (ι:=ι) :=
  (P.map (fun t=>t.1 • shifts t.2.1 (wordSeq j a t.2.2))).sum

def predictionPolynomial (j : ℝ) (a : ι→ℝ) (P : GradedWords ι) (i : ι) : Polynomial ℝ :=
  (P.map (fun t=>Polynomial.C t.1*Polynomial.X^t.2.1*wordPredictionPolynomial j a t.2.2 i)).sum

def prediction (j : ℝ) (a : ι→ℝ) (z : ℝ) (P : GradedWords ι) (i : ι) : ℝ :=
  (P.map (fun t=>t.1*z^t.2.1*wordPrediction j a z t.2.2 i)).sum

end GradedWords

def projectSeries (i : ι) : Seq (ι:=ι)→ₗ[ℝ] PowerSeries ℝ where
  toFun v := PowerSeries.mk (fun n=>project (v n) i)
  map_add' v w := by ext n; simp
  map_smul' c v := by ext n; simp
omit [Fintype ι] in
@[simp] lemma projectSeries_coeff (i : ι) (v : Seq (ι:=ι)) (n : ℕ) :
    PowerSeries.coeff n (projectSeries i v)=project (v n) i := by simp [projectSeries]
end SKGap.Noncrossing.Primary.Tensor.Series

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ClosedPrediction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor.Series
open Diagram InverseDiagram WordSeries Loop
variable {ι : Type*} [Fintype ι]
namespace GradedWords

def branch (j : ℝ) (p : ι→ℝ) (U V : GradedWords ι×GradedWords ι) : GradedWords ι×GradedWords ι :=
  (prepend (.diag p) U.2++V.1,
    (bump (prepend .noise (prepend (.diag p) U.2))++
      scale (-(j*Diagram.mean p)) (bump (bump U.1)))++V.2)
def ordinaryWords (j : ℝ) : SourceTree (ι→ℝ)→GradedWords ι×GradedWords ι
  | .leaf c => (scalar c,bump (prepend .noise (scalar c)))
  | .branch p t u => branch j p (ordinaryWords j t) (ordinaryWords j u)
def implicitSource (j : ℝ) (a p : ι→ℝ) (t : SourceTree (ι→ℝ)) : GradedWords ι :=
  prepend .inverse (prepend (.diag p) (ordinaryWords j t).2++
    scale (-(j*Diagram.mean p)) (bump (bump (prepend (.diag a) (ordinaryWords j t).1))))
def implicitField (j : ℝ) (a p : ι→ℝ) (t : SourceTree (ι→ℝ)) : GradedWords ι :=
  (bump (prepend .noise (implicitSource j a p t))++
    scale (-(j*Diagram.mean a)) (bump (bump (implicitSource j a p t))))++
    scale (-(j*Diagram.mean p)) (bump (bump (ordinaryWords j t).1))

def pairSeq (j : ℝ) (a : ι→ℝ) (P : GradedWords ι×GradedWords ι) :=
  (seq j a P.1,seq j a P.2)

section
omit [Fintype ι]

def bounded (k : ℕ) (P : GradedWords ι) : Prop := ∀ t∈P,inverseCount t.2.2≤k

end

end GradedWords

namespace ClosedTree
open GradedWords

def words (j : ℝ) (a : ι→ℝ) : ClosedTree (ι→ℝ)→GradedWords ι×GradedWords ι
  | .leaf c => ordinaryWords j (.leaf c)
  | .implicit p t => (implicitSource j a p t,implicitField j a p t)
  | .branch p t u => GradedWords.branch j p (t.words j a) (u.words j a)
end ClosedTree
end SKGap.Noncrossing.Primary.Tensor.Series

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_ClosedTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.Noncrossing
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Primary.Tensor.Series.GradedWords

def matrixValue (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) (P : GradedWords ι) : Matrix ι ι ℝ :=
  (P.map (fun t=>t.1 • exactWord j a t.2.2 J)).sum

end Primary.Tensor.Series.GradedWords
end SKGap.Noncrossing

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.Noncrossing.Primary
open Diagram WordSeries Matrix
variable {n : ℕ}

inductive SmallMark (n : ℕ) where
  | diagonal : List (Letter (Fin n→ℝ))→(Fin n→ℝ)→List (Letter (Fin n→ℝ))→SmallMark n
  | average : (Fin n→ℝ)→List (Letter (Fin n→ℝ))→SmallMark n

namespace SmallMark

def vector : SmallMark n→Fin n→ℝ
  | .diagonal _ s _ => s
  | .average s _ => s

def word : SmallMark n→List (Letter (Fin n→ℝ))
  | .diagonal P s Q => P++(.diag s::Q)
  | .average _ P => P

def scalar : SmallMark n→ℝ
  | .diagonal _ _ _ => 1
  | .average s _ => Diagram.mean s

def prepend (P : List (Letter (Fin n→ℝ))) : SmallMark n→SmallMark n
  | .diagonal Q s R => .diagonal (P++Q) s R
  | .average s Q => .average s (P++Q)

def diagnostic (d : Fin n→ℝ) : SmallMark n→List (Letter (Fin n→ℝ))
  | .diagonal P _ Q => Q++(.diag d::P)
  | .average _ P => P

end SmallMark

abbrev MarkedPolynomial (n : ℕ) := List (ℝ×SmallMark n)
namespace MarkedPolynomial

def plain (P : MarkedPolynomial n) : WordPolynomial (ι:=Fin n) :=
  P.map (fun t=>(t.1*t.2.scalar,t.2.word))
def budget (P : MarkedPolynomial n) : ℝ :=
  (P.map (fun t=>|t.1| *SKGapCutoff.Recipe.vectorNorm t.2.vector)).sum

def prepend (F : List (Letter (Fin n→ℝ))) (P : MarkedPolynomial n) : MarkedPolynomial n :=
  P.map (fun t=>(t.1,t.2.prepend F))
def scale (c : ℝ) (P : MarkedPolynomial n) : MarkedPolynomial n := P.map (fun t=>(c*t.1,t.2))

end MarkedPolynomial
end SKGap.Noncrossing.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_PrimitiveTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.SourceError
variable {n : ℕ}

def testSize (P : Interaction n) : ℝ := SKGap.opNorm P+SKGap.offDiagonalSeminorm P

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Matrix SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Diagram
variable {n : ℕ}

abbrev OrdinaryWord (n : ℕ) := List (Letter (Fin n→ℝ))

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_ClosedErrorTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Diagram
variable {n : ℕ}

def closedWordBounded (A : ℝ) (w : List (WordLetter (Fin n))) : Prop :=
  ∀l∈w,match l with | .diag p=>∀i,|p i|≤A | .noise=>True | .inverse=>True

def ClosedWordTestBound (j : ℝ) (a : Fin n→ℝ) (J : Interaction n)
    (A M : ℝ) (L : ℕ) : Prop :=
  ∀w:List (WordLetter (Fin n)),w.length≤L→inverseCount w≤1→closedWordBounded A w→
    testSize (exactWord j a w J)≤M

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ResidualInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Primary
open Matrix SKGap.Stein
variable {n : ℕ}

def mag (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) : VectorFields n :=
  (primaryState j J h k).1

def fld (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) : VectorFields n :=
  (primaryState j J h k).2

def onsager (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) : Spin n→ℝ :=
  siteMean (fun x i=>1-(mag j J h k x i)^2)

def residual (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) : VectorFields n :=
  fun x i=>mag j J h k x i-mag j J h (k+1) x i

def previousResidual (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) : VectorFields n :=
  fun x i=>mag j J h (k-1) x i-mag j J h k x i

def steinSource (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ)
    (U : VectorFields n) : VectorFields n := fun x i=>
  phi (fld j J h k x i) (fld j J h (k+1) x i)
    (j*(onsager j J h (k+1) x-onsager j J h k x))*U x i

def steinPartial (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ)
    (U : VectorFields n) : VectorFields n := fun x i=>
  phiZ (fld j J h k x i) (fld j J h (k+1) x i)
    (j*(onsager j J h (k+1) x-onsager j J h k x))*U x i

def nextField {ι κ : Type*} [Fintype ι] [Fintype κ]
    (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ)
    (U : VectorFields n) (L : ι→ℕ) (α : ι→Spin n→ℝ)
    (W : κ→VectorFields n) (γ : κ→Spin n→ℝ) : VectorFields n := fun x i=>
  (∑l,J i l*steinSource j J h k U x l)-
  j*siteMean (steinPartial j J h k U) x*mag j J h k x i-
  j*(∑l,α l x*mag j J h (L l) x i)-j*∑b,γ b x*W b x i

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ResidualAdmissibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary
variable {n M : ℕ} {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]
namespace OrdinaryData

def Admissible (D : OrdinaryData n (Fin M) κ σ) (N p : ℕ) : Prop :=
  ∀a≤N,∀q:Fin M,q.val<p→ (∀s,D.seedPartial a q s=0) ∧ (∀b,D.auxPartial a q b=0)

end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Reference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianStep
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
noncomputable section
variable {n : ℕ}

def reference (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance reference_probability (n : ℕ) : IsProbabilityMeasure (reference n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi _))

structure Prior (n : ℕ) where
  mass : Spin n → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  sum_one : ∑ x, mass x = 1

@[ext] lemma Prior.ext {p q : Prior n} (h : p.mass = q.mass) : p = q := by
  cases p
  cases q
  congr

instance instCoeFunPriorForallSpinReal : CoeFun (Prior n) (fun _ => Spin n → ℝ) := ⟨Prior.mass⟩

def gibbsPrior (g : Disorder n) (h : Fin n → ℝ) : Prior n :=
  ⟨mass g h, mass_nonneg g h, sum_mass g h⟩

def mean (p : Prior n) (i : Fin n) : ℝ := ∑ x, p x * spinValue (x i)

def likelihood (t : ℝ) (x : Spin n) (z : Fin n → ℝ) : ℝ :=
  exp (sqrt t * (∑ i, spinValue (x i) * z i) - t * n / 2)

def density (p : Prior n) (t : ℝ) (z : Fin n → ℝ) : ℝ :=
  ∑ x, p x * likelihood t x z

lemma likelihood_pos (t : ℝ) (x : Spin n) (z : Fin n → ℝ) :
    0 < likelihood t x z := exp_pos _

lemma density_jensen (p : Prior n) (t : ℝ) (z : Fin n → ℝ) :
    exp (sqrt t * (∑ i, mean p i * z i) - t*n/2) ≤ density p t z := by
  have he : (∑ x, p x * (sqrt t * (∑ i, spinValue (x i) * z i) - t*n/2)) =
      sqrt t * (∑ i, mean p i * z i) - t*n/2 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, p.sum_one, one_mul]
    congr 1
    simp only [mean, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hj := convexOn_exp.map_sum_le (t := Finset.univ) (w := p.mass)
    (p := fun x => sqrt t * (∑ i, spinValue (x i) * z i) - t*n/2)
    (fun x _ => p.nonneg x) p.sum_one (fun _ _ => Set.mem_univ _)
  simpa only [smul_eq_mul, he, density, likelihood] using hj

lemma density_pos (p : Prior n) (t : ℝ) (z : Fin n → ℝ) :
    0 < density p t z := (exp_pos _).trans_le (density_jensen p t z)

def interaction (p : Prior n) (x y : Spin n) : ℝ :=
  ((∑ i, (spinValue (x i) + spinValue (y i) - mean p i)^2) - n) / 2

def pairKernel (p : Prior n) (t : ℝ) (x y : Spin n) (z : Fin n → ℝ) : ℝ :=
  exp ((∑ i, (sqrt t * (spinValue (x i) + spinValue (y i) - mean p i)) * z i) - t*n/2)

def majorant (p : Prior n) (a : Spin n → ℝ) (t : ℝ) (z : Fin n → ℝ) : ℝ :=
  (∑ x, a x*likelihood t x z)^2 * exp (-(sqrt t * (∑ i, mean p i * z i) - t*n/2))

def quadraticIntegrand (p : Prior n) (a : Spin n → ℝ) (t : ℝ) (z : Fin n → ℝ) : ℝ :=
  (∑ x, a x*likelihood t x z)^2 / density p t z

def avg (p : Prior n) (f : Spin n → ℝ) : ℝ := ∑ x, p x * f x

def var (p : Prior n) (f : Spin n → ℝ) : ℝ :=
  avg p (fun x => (f x - avg p f)^2)

def posterior (p : Prior n) (t : ℝ) (z : Fin n → ℝ) : Prior n where
  mass x := p x * likelihood t x z / density p t z
  nonneg x := div_nonneg (mul_nonneg (p.nonneg x) (likelihood_pos t x z).le)
    (density_pos p t z).le
  sum_one := by
    rw [← Finset.sum_div]
    exact div_self (density_pos p t z).ne'

end
end SKGap.GaussianStep

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_DivergenceIntegrand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianStep
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
noncomputable section
variable {n : ℕ}

def divergenceIntegrand (p q : Prior n) (t : ℝ) (z : Fin n → ℝ) : ℝ :=
  density q t z * log (density q t z/density p t z) - density q t z + density p t z

def squarePrior (p : Prior n) (f : Spin n → ℝ) (hf : 0 < avg p (fun x => (f x)^2)) : Prior n where
  mass x := p x*(f x)^2/avg p (fun x => (f x)^2)
  nonneg x := div_nonneg (mul_nonneg (p.nonneg x) (sq_nonneg _)) hf.le
  sum_one := by rw [← Finset.sum_div]; exact div_self hf.ne'

def cond (p : Prior n) (i : Fin n) (f : Spin n → ℝ) (x : Spin n) : ℝ :=
  (p x*f x+p (flip i x)*f (flip i x))/(p x+p (flip i x))

def energy (p : Prior n) (f : Spin n → ℝ) : ℝ :=
  ∑ i, avg p (fun x => (f x-cond p i f x)^2)

end
end SKGap.GaussianStep

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Posterior_History
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

abbrev History (n : ℕ) : ℕ → Type
  | 0 => Unit
  | k+1 => History n k × (Fin n → ℝ)

@[reducible] instance historyMeasurable (n : ℕ) : (k : ℕ) → MeasurableSpace (History n k)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | k+1 => by
    change MeasurableSpace (History n k × (Fin n → ℝ))
    letI := historyMeasurable n k
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

@[reducible] instance historyTopology (n : ℕ) : (k : ℕ) → TopologicalSpace (History n k)
  | 0 => inferInstanceAs (TopologicalSpace Unit)
  | k+1 => by
    change TopologicalSpace (History n k × (Fin n → ℝ))
    letI := historyTopology n k
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance historySecondCountable (n : ℕ) : (k : ℕ) → SecondCountableTopology (History n k)
  | 0 => inferInstanceAs (SecondCountableTopology Unit)
  | k+1 => by
    change SecondCountableTopology (History n k × (Fin n → ℝ))
    let := historySecondCountable n k
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance historyBorel (n : ℕ) : (k : ℕ) → BorelSpace (History n k)
  | 0 => inferInstanceAs (BorelSpace Unit)
  | k+1 => by
    change BorelSpace (History n k × (Fin n → ℝ))
    let := historyBorel n k
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def reference (n : ℕ) : (k : ℕ) → Measure (History n k)
  | 0 => Measure.dirac ()
  | k+1 => (reference n k).prod (GaussianStep.reference n)

instance reference_probability (n : ℕ) : (k : ℕ) → IsProbabilityMeasure (reference n k)
  | 0 => inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | k+1 => by
    change IsProbabilityMeasure ((reference n k).prod (GaussianStep.reference n))
    let := reference_probability n k
    first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def likelihood (t : ℝ) (x : Spin n) : {k : ℕ} → History n k → ℝ
  | 0, _ => 1
  | _+1, h => likelihood t x h.1 * GaussianStep.likelihood t x h.2

lemma likelihood_pos (t : ℝ) (x : Spin n) : ∀ {k : ℕ} (h : History n k),
    0 < likelihood t x h
  | 0, _ => zero_lt_one
  | _+1, h => mul_pos (likelihood_pos t x h.1) (GaussianStep.likelihood_pos t x h.2)

def density (p : Prior n) (t : ℝ) {k : ℕ} (h : History n k) : ℝ :=
  ∑ x, p x*likelihood t x h

lemma density_pos (p : Prior n) (t : ℝ) {k : ℕ} (h : History n k) :
    0 < density p t h := by
  have he : ∃ x, 0 < p x := by
    by_contra hn
    push Not at hn
    have hz : ∑ x, p x = 0 := Finset.sum_eq_zero (fun x _ => le_antisymm (hn x) (p.nonneg x))
    linarith [p.sum_one]
  obtain ⟨x,hx⟩ := he
  exact Finset.sum_pos' (fun y _ => mul_nonneg (p.nonneg y) (likelihood_pos t y h).le)
    ⟨x, Finset.mem_univ _, mul_pos hx (likelihood_pos t x h)⟩

def posterior (p : Prior n) (t : ℝ) {k : ℕ} (h : History n k) : Prior n where
  mass x := p x*likelihood t x h/density p t h
  nonneg x := div_nonneg (mul_nonneg (p.nonneg x) (likelihood_pos t x h).le) (density_pos p t h).le
  sum_one := by rw [← Finset.sum_div]; exact div_self (density_pos p t h).ne'

lemma posterior_avg_weight (p : Prior n) (t : ℝ) {k : ℕ} (h : History n k) (f : Spin n → ℝ) :
    density p t h*avg (posterior p t h) f=∑ x, p x*likelihood t x h*f x := by
  simp only [avg, posterior, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  field_simp [(density_pos p t h).ne']

def relativeEntropyIntegrand (p q : Prior n) (t : ℝ) {k : ℕ} (h : History n k) : ℝ :=
  density q t h*log (density q t h/density p t h)

def divergenceIntegrand (p q : Prior n) (t : ℝ) {k : ℕ} (h : History n k) : ℝ :=
  relativeEntropyIntegrand p q t h-density q t h+density p t h

def entropy (p q : Prior n) (t : ℝ) (k : ℕ) : ℝ :=
  ∫h:History n k,relativeEntropyIntegrand p q t h ∂reference n k

def law (p : Prior n) (t : ℝ) (k : ℕ) : Measure (History n k) :=
  (reference n k).withDensity (fun h => ENNReal.ofReal (density p t h))

def eventProbability (p : Prior n) (t : ℝ) {k : ℕ} (E : Set (History n k)) : ℝ :=
  ∫h in E,density p t h ∂reference n k

end
end SKGap.GaussianHistory

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_ContinuousPosteriorMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

lemma squarePrior_density (p : Prior n) (f : Spin n→ℝ) (hf : 0<avg p (fun x => (f x)^2))
    (t : ℝ) {k : ℕ} (h : History n k) :
    density (squarePrior p f hf) t h =
      density p t h*avg (posterior p t h) (fun x => (f x)^2)/avg p (fun x => (f x)^2) := by
  rw [posterior_avg_weight]
  unfold density squarePrior
  dsimp
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma posterior_square_pos (p : Prior n) (f : Spin n→ℝ) (hf : 0<avg p (fun x => (f x)^2))
    (t : ℝ) {k : ℕ} (h : History n k) : 0<avg (posterior p t h) (fun x => (f x)^2) := by
  have hs:=density_pos (squarePrior p f hf) t h
  rw [squarePrior_density] at hs
  exact (mul_pos_iff_of_pos_left (density_pos p t h)).mp ((div_pos_iff_of_pos_right hf).mp hs)

end
end SKGap.GaussianHistory

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_LogDetPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def logPath (q : ℝ) (a : ι → ℝ) (M : Matrix ι ι ℝ) (z : ℝ) : Matrix ι ι ℝ :=
  1+(z^2*q) • diagonal a-z • (diagonal a*M)

def logPathCutoffDerivative (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R)
    (j : ℝ) (a : ι → ℝ) (M : Matrix ι ι ℝ) (z : ℝ) : ℝ :=
  (2*z*((j/(Fintype.card ι:ℝ))*∑ b,a b)*(pathK f R hR j a z M*diagonal a).trace-
    (realProject R hR M*pathK f R hR j a z M*diagonal a).trace)/(Fintype.card ι:ℝ)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_ConditionalBadSet
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

def plantedInteraction {n : ℕ} (j : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  W+(j/(n:ℝ)) • vecMulVec (fun _=>1) (fun _=>1)

def badFieldSet (n : ℕ) (j A ε c : ℝ) : Set (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) :=
  {p | ∃ a : Fin n → ℝ, (∀ i,a i ∈ Icc 0 A) ∧
    (∑ i,(a i-spinVariance p.2 i)^2) ≤ ε^2*(n:ℝ) ∧
    ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖=1 ∧
      quadraticForm (fieldHessian j (plantedInteraction j p.1) p.2 a) x.ofLp ≤ c}

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_EntropyEll
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
namespace SKGap

def entropyEll (u : ℝ) : ℝ := -log (1 - u) - u

def entropySlack (B u : ℝ) : ℝ := u ^ 2 / 2 - B * entropyEll u

def entropyVarianceSlack (k B C : ℝ) : ℝ :=
  C ^ 2 / k - 1 - log (C ^ 2 / k) - (C - B) ^ 2 / (1 + k)

def entropyVarianceSlope (k B C : ℝ) : ℝ :=
  2 * C / k - 2 / C - 2 * (C - B) / (1 + k)

end SKGap

end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ScalarFixedPointJoined
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
namespace SKGap

theorem integrable_tanh {P : Measure ℝ} [IsFiniteMeasure P] : Integrable tanh P := by
  apply Integrable.of_bound continuous_tanh.aestronglyMeasurable 1
  exact ae_of_all _ (fun y => by simpa using (abs_tanh_lt_one y).le)

theorem integrable_tanh_sq {P : Measure ℝ} [IsFiniteMeasure P] :
    Integrable (fun y => tanh y ^ 2) P := by
  apply Integrable.of_bound (by fun_prop) 1
  exact ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (tanh y))]
    using (tanh_sq_lt_one y).le)

def oddVariance (y : ℝ) : ℝ := tanh y * (1 - tanh y^2)

lemma abs_oddVariance_le_one (y : ℝ) : |oddVariance y| ≤ 1 := by
  have ht := (abs_tanh_lt_one y).le
  have hs := (tanh_sq_lt_one y).le
  dsimp [oddVariance]
  rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hs)]
  exact (mul_le_mul_of_nonneg_right ht (sub_nonneg.mpr hs)).trans (by nlinarith [sq_nonneg (tanh y)])

lemma integrable_oddVariance {P : Measure ℝ} [IsFiniteMeasure P] :
    Integrable oddVariance P := by
  apply Integrable.of_bound (by unfold oddVariance; fun_prop) 1
  exact ae_of_all _ (fun y => by simpa using abs_oddVariance_le_one y)

lemma gaussianPDFReal_diagonal_factor {s : ℝ≥0} (hs : s ≠ 0) (y : ℝ) :
    gaussianPDFReal s s y =
      (1 / sqrt (2*π*s) * exp (-y^2/(2*s) - s/2)) * exp y := by
  have hs' : (s : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hs
  have he : -(y-(s:ℝ))^2/(2*s) = (-y^2/(2*s)-s/2)+y := by
    field_simp
    ring
  rw [gaussianPDFReal, he, exp_add]
  ring

lemma gaussianPDFReal_diagonal_symmetry {s : ℝ≥0} (hs : s ≠ 0) (y : ℝ) :
    gaussianPDFReal s s y - gaussianPDFReal s s (-y) =
      tanh y * (gaussianPDFReal s s y + gaussianPDFReal s s (-y)) := by
  rw [gaussianPDFReal_diagonal_factor hs y, gaussianPDFReal_diagonal_factor hs (-y)]
  rw [neg_sq, tanh_eq]
  have he : exp y + exp (-y) ≠ 0 := (add_pos (exp_pos _) (exp_pos _)).ne'
  field_simp

theorem gaussian_nishimori (s : ℝ≥0) :
    (∫ y, tanh y ∂gaussianReal s s) = (∫ y, tanh y^2 ∂gaussianReal s s) := by
  by_cases hs : s = 0
  · subst s
    simp
  have hi := (integrable_gaussian_iff hs).mp
    (integrable_tanh.sub (integrable_tanh_sq (P := gaussianReal s s)))
  set f : ℝ → ℝ := fun y => gaussianPDFReal s s y * (tanh y - tanh y^2)
  have hf : Integrable f := hi
  have hid (y : ℝ) : f y + f (-y) = 0 := by
    have hh := gaussianPDFReal_diagonal_symmetry hs y
    dsimp [f]
    rw [tanh_neg, neg_sq]
    nlinarith [congrArg (fun x => tanh y * x) hh]
  have hz : (∫ y, f y) + ∫ y, f (-y) = 0 := by
    rw [← integral_add hf hf.comp_neg]
    simp only [hid, integral_zero]
  rw [integral_neg_eq_self] at hz
  have h0 : ∫ y, f y = 0 := by linarith
  have hsub : ∫ y, tanh y - tanh y^2 ∂gaussianReal s s = 0 := by
    rw [integral_gaussianReal_eq_integral_smul hs]
    exact h0
  rw [integral_sub integrable_tanh integrable_tanh_sq] at hsub
  exact sub_eq_zero.mp hsub

lemma tanh_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ tanh x := by
  rw [tanh_eq]
  exact div_nonneg (sub_nonneg.mpr (exp_le_exp.mpr (by linarith))) (by positivity)

lemma tanh_nonpos_of_nonpos {x : ℝ} (hx : x ≤ 0) : tanh x ≤ 0 := by
  rw [tanh_eq]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (exp_le_exp.mpr (by linarith))) (by positivity)

lemma gaussianPDFReal_reflection_le {d : ℝ} (hd : 0 ≤ d) (s : ℝ≥0)
    {y : ℝ} (hy : 0 ≤ y) : gaussianPDFReal d s (-y) ≤ gaussianPDFReal d s y := by
  unfold gaussianPDFReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith

theorem gaussian_odd_sign {d : ℝ} (hd : 0 ≤ d) (s : ℝ≥0) :
    0 ≤ ∫ y, oddVariance y ∂gaussianReal d s := by
  by_cases hs : s = 0
  · subst s
    simp only [gaussianReal_zero_var, integral_dirac]
    exact mul_nonneg (tanh_nonneg_of_nonneg hd) (sub_nonneg.mpr (tanh_sq_lt_one d).le)
  have hi := (integrable_gaussian_iff hs).mp (integrable_oddVariance (P := gaussianReal d s))
  set f : ℝ → ℝ := fun y => gaussianPDFReal d s y * oddVariance y
  have hf : Integrable f := hi
  have hodd (y : ℝ) : oddVariance (-y) = -oddVariance y := by
    simp [oddVariance, tanh_neg]
  have hid (y : ℝ) : 0 ≤ f y + f (-y) := by
    have he : f y + f (-y) = (gaussianPDFReal d s y - gaussianPDFReal d s (-y)) * oddVariance y := by
      dsimp [f]; rw [hodd]; ring
    rw [he]
    by_cases hy : 0 ≤ y
    · exact mul_nonneg (sub_nonneg.mpr (gaussianPDFReal_reflection_le hd s hy))
        (mul_nonneg (tanh_nonneg_of_nonneg hy) (sub_nonneg.mpr (tanh_sq_lt_one y).le))
    · have hy' : 0 ≤ -y := by linarith
      have hp := gaussianPDFReal_reflection_le hd s hy'
      rw [neg_neg] at hp
      apply mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hp)
      exact mul_nonpos_of_nonpos_of_nonneg (tanh_nonpos_of_nonpos (le_of_not_ge hy))
        (sub_nonneg.mpr (tanh_sq_lt_one y).le)
  have hn := MeasureTheory.integral_nonneg (μ := volume) (f := fun y : ℝ => f y + f (-y)) hid
  rw [integral_add hf hf.comp_neg, integral_neg_eq_self] at hn
  rw [integral_gaussianReal_eq_integral_smul hs]
  change 0 ≤ ∫ y, f y
  linarith

end SKGap

namespace SKGap
open Filter
open scoped Topology

def gaussianF (s : ℝ) : ℝ := gaussianAverage tanh s s

lemma continuous_gaussianF : Continuous gaussianF :=
  (continuous_gaussianAverage continuous_tanh
    (fun y => by simpa using (abs_tanh_lt_one y).le)).comp (continuous_id.prodMk continuous_id)

lemma gaussianF_eq_square {s : ℝ} (hs : 0 ≤ s) :
    gaussianF s = gaussianAverage (fun y => tanh y^2) s s := by
  rw [gaussianF, gaussianAverage_eq_integral continuous_tanh s hs,
    gaussianAverage_eq_integral (by fun_prop) s hs]
  convert gaussian_nishimori s.toNNReal using 1 <;> rw [Real.coe_toNNReal _ hs]

lemma gaussianF_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ gaussianF s := by
  rw [gaussianF_eq_square hs]
  exact MeasureTheory.integral_nonneg (f := fun x => tanh (s+sqrt s*x)^2) (fun x => sq_nonneg _)

lemma gaussianF_raw_deriv {s : ℝ} (hs : 0 < s) :
    HasDerivAt gaussianF
      (∫ x, (1-tanh (s+sqrt s*x)^2)*(1+x/(2*sqrt s)) ∂gaussianReal 0 1) s := by
  let bound : ℝ → ℝ := fun x => 1+|x|/(2*sqrt (s/2))
  have hb : Integrable bound (gaussianReal 0 1) :=
    (integrable_const 1).add ((IsGaussian.integrable_id (μ := gaussianReal 0 1)).abs.div_const _)
  have hnorm (t x : ℝ) (ht : t ∈ Ioi (s/2)) :
      ‖(1-tanh (t+sqrt t*x)^2)*(1+x/(2*sqrt t))‖ ≤ bound x := by
    have ht0 : 0 < t := lt_trans (half_pos hs) ht
    have hsqrt : 0 < sqrt (s/2) := sqrt_pos.2 (half_pos hs)
    have htqrt : 0 < sqrt t := sqrt_pos.2 ht0
    have h1 : |1-tanh (t+sqrt t*x)^2| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith [tanh_sq_lt_one (t+sqrt t*x), sq_nonneg (tanh (t+sqrt t*x))]
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ 1*|1+x/(2*sqrt t)| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ 1+|x|/(2*sqrt t) := by
        simpa only [one_mul, abs_one, abs_div, abs_of_pos (mul_pos (by norm_num : (0:ℝ)<2) htqrt)] using abs_add_le (1:ℝ) (x/(2*sqrt t))
      _ ≤ bound x := by
        dsimp [bound]
        gcongr
        exact ht.le
  have hder (t x : ℝ) (ht : t ∈ Ioi (s/2)) :
      HasDerivAt (fun t => tanh (t+sqrt t*x))
        ((1-tanh (t+sqrt t*x)^2)*(1+x/(2*sqrt t))) t := by
    have ht0 : 0 < t := lt_trans (half_pos hs) ht
    convert! (hasDerivAt_tanh (t+sqrt t*x)).comp t
      ((hasDerivAt_id t).add ((hasDerivAt_sqrt ht0.ne').mul_const x)) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (s := Ioi (s/2)) (x₀ := s)
    (F := fun t x => tanh (t+sqrt t*x))
    (F' := fun t x => (1-tanh (t+sqrt t*x)^2)*(1+x/(2*sqrt t)))
    (bound := bound) (Ioi_mem_nhds (half_lt_self hs))
    (Eventually.of_forall (fun t => (by fun_prop : Continuous (fun x : ℝ => tanh (t+sqrt t*x))).aestronglyMeasurable))
    (integrable_gaussian_comp_of_bound continuous_tanh (fun y => by simpa using (abs_tanh_lt_one y).le) s s)
    (by fun_prop)
    (ae_of_all _ (fun x t ht => hnorm t x ht)) hb
    (ae_of_all _ (fun x t ht => hder t x ht))).2

lemma gaussian_diagonal_stein (s : ℝ) :
    (∫ x, x*(1-tanh (s+sqrt s*x)^2) ∂gaussianReal 0 1) =
      -2*sqrt s * (∫ x, oddVariance (s+sqrt s*x) ∂gaussianReal 0 1) := by
  have hv (x : ℝ) : ‖1-tanh (s+sqrt s*x)^2‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [tanh_sq_lt_one (s+sqrt s*x), sq_nonneg (tanh (s+sqrt s*x))]
  have hi : Integrable (fun x => 1-tanh (s+sqrt s*x)^2) (gaussianReal 0 1) :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ hv)
  have hid : Integrable (fun x => -2*sqrt s*oddVariance (s+sqrt s*x)) (gaussianReal 0 1) :=
    (integrable_gaussian_comp_of_bound (by unfold oddVariance; fun_prop)
      (fun y => by simpa using abs_oddVariance_le_one y) s s).const_mul _
  have hxi : Integrable (fun x => (x-0)*(1-tanh (s+sqrt s*x)^2)) (gaussianReal 0 1) := by
    simpa only [sub_zero, id_eq] using
      (IsGaussian.integrable_id (μ := gaussianReal 0 1)).mul_bdd (c := 1) (by fun_prop) (ae_of_all _ hv)
  have hd (x : ℝ) : HasDerivAt (fun x => 1-tanh (s+sqrt s*x)^2)
      (-2*sqrt s*oddVariance (s+sqrt s*x)) x := by
    convert! (((hasDerivAt_tanh (s+sqrt s*x)).comp x
      (((hasDerivAt_id x).const_mul (sqrt s)).const_add s)).pow 2).const_sub 1 using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [oddVariance]
    ring
  have h := gaussian_integration_by_parts (d := 0) (s := 1) (by norm_num) hd hi hid hxi
  simpa only [sub_zero, NNReal.coe_one, one_mul, integral_const_mul] using h

lemma gaussianF_deriv {s : ℝ} (hs : 0 < s) :
    HasDerivAt gaussianF (gaussianAverage (fun y => (1-tanh y^2)*(1-tanh y)) s s) s := by
  have h := gaussianF_raw_deriv hs
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  have hi := integrable_gaussian_comp_of_bound (f := fun y => 1-tanh y^2) (by fun_prop)
    (C := 1) (fun y => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> nlinarith [tanh_sq_lt_one y, sq_nonneg (tanh y)]) s s
  have ho := integrable_gaussian_comp_of_bound (f := oddVariance) (by unfold oddVariance; fun_prop)
    (C := 1) (fun y => by simpa using abs_oddVariance_le_one y) s s
  have hxi : Integrable (fun x => x*(1-tanh (s+sqrt s*x)^2)) (gaussianReal 0 1) :=
    (IsGaussian.integrable_id (μ := gaussianReal 0 1)).mul_bdd (c := 1) (by fun_prop)
      (ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs, abs_le]; constructor <;> nlinarith [tanh_sq_lt_one (s+sqrt s*x), sq_nonneg (tanh (s+sqrt s*x))]))
  have h1 : gaussianAverage (fun y => (1-tanh y^2)*(1-tanh y)) s s =
      (∫ x, 1-tanh (s+sqrt s*x)^2 ∂gaussianReal 0 1) -
        ∫ x, oddVariance (s+sqrt s*x) ∂gaussianReal 0 1 := by
    rw [← integral_sub hi ho]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by dsimp [oddVariance]; ring)
  rw [h1]
  have he (x : ℝ) : (1-tanh (s+sqrt s*x)^2)*(1+x/(2*sqrt s)) =
      (1-tanh (s+sqrt s*x)^2) + (x*(1-tanh (s+sqrt s*x)^2))/(2*sqrt s) := by ring
  simp_rw [he]
  rw [integral_add hi (hxi.div_const _), integral_div, gaussian_diagonal_stein]
  field_simp
  ring

lemma gaussianF_derivative_bounds {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ gaussianAverage (fun y => (1-tanh y^2)*(1-tanh y)) s s ∧
      gaussianAverage (fun y => (1-tanh y^2)*(1-tanh y)) s s ≤ 1 := by
  have hm (y : ℝ) : 0 ≤ (1-tanh y^2)*(1-tanh y) :=
    mul_nonneg (sub_nonneg.mpr (tanh_sq_lt_one y).le)
      (sub_nonneg.mpr (le_trans (le_abs_self _) (abs_tanh_lt_one y).le))
  constructor
  · exact MeasureTheory.integral_nonneg (f := fun x => (1-tanh (s+sqrt s*x)^2)*(1-tanh (s+sqrt s*x))) (fun x => hm _)
  · rw [gaussianAverage_eq_integral (by fun_prop) s hs]
    have he (y : ℝ) : (1-tanh y^2)*(1-tanh y) = (1-tanh y^2)-oddVariance y := by
      dsimp [oddVariance]; ring
    simp_rw [he]
    rw [integral_sub (f := fun y => 1-tanh y^2) (g := oddVariance)
      ((integrable_const 1).sub (integrable_tanh_sq (P := gaussianReal s s.toNNReal)))
      integrable_oddVariance,
      integral_sub (integrable_const 1) (integrable_tanh_sq (P := gaussianReal s s.toNNReal)), integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    have ho := gaussian_odd_sign hs s.toNNReal
    have hq : 0 ≤ ∫ y, tanh y^2 ∂gaussianReal s s.toNNReal :=
      MeasureTheory.integral_nonneg (f := fun y => tanh y^2) (fun y => sq_nonneg _)
    linarith

end SKGap

namespace SKGap
open Filter
open scoped Topology

lemma gaussianF_lipschitz : LipschitzOnWith 1 gaussianF (Ici 0) := by
  have h : LipschitzOnWith 1 gaussianF (Ioi 0) :=
    Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun s hs => (gaussianF_deriv hs).differentiableAt)
      (fun s hs => by
        rw [(gaussianF_deriv hs).deriv]
        have hb := gaussianF_derivative_bounds hs.le
        exact_mod_cast (show ‖gaussianAverage (fun y => (1-tanh y^2)*(1-tanh y)) s s‖ ≤ 1 by
          rw [Real.norm_eq_abs, abs_of_nonneg hb.1]; exact hb.2))
      (convex_Ioi 0)
  simpa only [closure_Ioi] using LipschitzOnWith.closure continuous_gaussianF.continuousOn h

lemma gaussianF_le_one {s : ℝ} (hs : 0 ≤ s) : gaussianF s ≤ 1 := by
  rw [gaussianF_eq_square hs, gaussianAverage_eq_integral (by fun_prop) s hs]
  have h := integral_mono (integrable_tanh_sq (P := gaussianReal s s.toNNReal)) (integrable_const 1)
    (fun y => (tanh_sq_lt_one y).le)
  simpa using h

end SKGap

namespace SKGap

lemma gaussian_fixed_unique {j t s r : ℝ} (hj : 0 < j) (hj1 : j < 1)
    (hs : 0 ≤ s) (hr : 0 ≤ r) (hes : s = t+j*gaussianF s)
    (her : r = t+j*gaussianF r) : s = r := by
  have h := gaussianF_lipschitz.dist_le_mul s hs r hr
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
  have he : |s-r| = j*|gaussianF s-gaussianF r| := by
    have he' : s-r = j*(gaussianF s-gaussianF r) := by linarith
    rw [he', abs_mul, abs_of_pos hj]
  have hz : |s-r| = 0 := by nlinarith [abs_nonneg (s-r), abs_nonneg (gaussianF s-gaussianF r)]
  exact sub_eq_zero.mp (abs_eq_zero.mp hz)

lemma exists_gaussian_fixed {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    ∃! s : ℝ, 0 ≤ s ∧ s = t+j*gaussianF s := by
  let g : ℝ → ℝ := fun s => s-t-j*gaussianF s
  have hg : Continuous g := (continuous_id.sub continuous_const).sub (continuous_const.mul continuous_gaussianF)
  have hl : g t ≤ 0 := by dsimp [g]; nlinarith [gaussianF_nonneg ht]
  have hu : 0 ≤ g (t+j) := by dsimp [g]; nlinarith [gaussianF_le_one (by linarith : 0 ≤ t+j)]
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc (by linarith : t ≤ t+j) hg.continuousOn ⟨hl, hu⟩
  have hs0 : 0 ≤ s := le_trans ht hs.1
  have hes : s = t+j*gaussianF s := by change s-t-j*gaussianF s = 0 at he; linarith
  refine ⟨s, ⟨hs0, hes⟩, ?_⟩
  intro r hr
  exact gaussian_fixed_unique hj hj1 hr.1 hs0 hr.2 hes

def scalarFixedPoint (j t : ℝ) : ℝ :=
  if h : 0 < j ∧ j < 1 ∧ 0 ≤ t then (exists_gaussian_fixed h.1 h.2.1 h.2.2).choose else 0

def scalarQ (j t : ℝ) : ℝ := gaussianF (scalarFixedPoint j t)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_EntropyTransport
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
namespace SKGap

def entropyTransport (u y : ℝ) : ℝ := y - u * tanh y

def entropyTransportDeriv (u y : ℝ) : ℝ := 1 - u * (1 - tanh y ^ 2)

def entropyTransportLog (u d s y : ℝ) : ℝ :=
  u / s * ((y - d) * tanh y) - u ^ 2 / (2 * s) * tanh y ^ 2 +
    log (entropyTransportDeriv u y)

def gaussianRatioLog (d : ℝ) (s r : ℝ≥0) (y : ℝ) : ℝ :=
  log (gaussianPDFReal d r y) - log (gaussianPDFReal d s y)

end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_EmpiricalLaw
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
namespace SKGap

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def empiricalLaw (y : ι → ℝ) : ProbabilityMeasure ℝ :=
  ⟨(Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (y i), ⟨by
    rw [Measure.smul_apply, Measure.finsetSum_apply]
    simp only [Measure.dirac_apply_of_mem (mem_univ _), Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast ((Fintype.card_pos (α := ι)).ne')) (by simp)⟩⟩

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_NormalLogConst
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open Set Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
namespace SKGap

variable {ι : Type*} [Fintype ι]

def normalLogConst (d s : ℝ) : ℝ := -log (sqrt (2*Real.pi*s))-d^2/(2*s)

def normalLogDensity (d s x : ℝ) : ℝ := normalLogConst d s+d/s*x-x^2/(2*s)

def productNormal (d s : ℝ) (y : ι → ℝ) : ℝ := ∏ i, gaussianPDFReal d s.toNNReal (y i)

end SKGap

namespace SKGap

def normalDensityError (R d s d₀ s₀ : ℝ) : ℝ :=
  |normalLogConst d s-normalLogConst d₀ s₀| + |d/s-d₀/s₀| * (1+R) +
    |1/(2*s)-1/(2*s₀)| * R

end SKGap
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_ScalarEntropyTarget
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
namespace SKGap

def scalarEntropyTarget (P : Measure ℝ) (j d : ℝ) (s : ℝ≥0) : ℝ :=
  j * ((∫ y, (y - d) * tanh y ∂P) - (s : ℝ) * (1 - ∫ y, tanh y ^ 2 ∂P)) ^ 2 /
    (2 * (s : ℝ) * ((s : ℝ) + j * (∫ y, tanh y ^ 2 ∂P)))

end SKGap

noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace SKGap

def EntropyTestBound (P Q : Measure ℝ) (D : ℝ) : Prop :=
  ∀ f : ℝ →ᵇ ℝ, (∫ x, f x ∂P) - log (∫ x, exp (f x) ∂Q) ≤ D

def realClip (n : ℕ) (x : ℝ) : ℝ := max (-(n:ℝ)) (min (n:ℝ) x)

lemma realClip_bounds (n : ℕ) (x : ℝ) : -(n:ℝ) ≤ realClip n x ∧ realClip n x ≤ n := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_left _ _)

def clippedBC {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => realClip n (f x))
    (by unfold realClip; fun_prop) n (fun x => by
      rw [Real.norm_eq_abs, abs_le]; exact realClip_bounds n (f x))

end SKGap

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_FiniteRankPositive
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Real Matrix Set
open scoped BigOperators
namespace SKGap
variable {ι : Type*} [Fintype ι]

def rayleigh (M : Matrix ι ι ℝ) (v : EuclideanSpace ℝ ι) : ℝ :=
  (WithLp.ofLp v) ⬝ᵥ (M *ᵥ WithLp.ofLp v)

def unitEuclidean (ι : Type*) [Fintype ι] := {v : EuclideanSpace ℝ ι | ‖v‖ = 1}

def lowerRayleigh (M : Matrix ι ι ℝ) : ℝ := sInf (rayleigh M '' unitEuclidean ι)

end SKGap

noncomputable section
open Real Matrix Set
open scoped BigOperators
namespace SKGap

def limitingGram (b e s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![b,e,-2*e; e,e,b-3*e; -2*e,b-3*e,b/s-2*b+6*e]

def rankCoefficient (j b s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  j • !![1,0,0; 0,2-j*b/s,1; 0,1,0]

end SKGap

end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianGramMomentsJoined
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal

namespace SKGap

def scalarGramVariance (y : ℝ) := 1-tanh y^2

def spinMixed (y : ℝ) := tanh y^2*scalarGramVariance y

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

def scalarGramVector (s y : ℝ) : Fin 3 → ℝ := ![1,tanh y,(y-s)/s]

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_WeightedScalarMoments
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real MeasureTheory
open scoped BigOperators BoundedContinuousFunction

lemma scalarVariance_cosh (y : ℝ) : (1-tanh y^2)*cosh y^2=1 := by
  rw [tanh_eq_sinh_div_cosh]
  field_simp
  exact cosh_sq_sub_sinh_sq y

lemma square_le_sinh_square (y : ℝ) : y^2 ≤ sinh y^2 := by
  by_cases hy : 0 ≤ y
  · have h := (self_le_sinh_iff).2 hy
    have hs := (sinh_nonneg_iff).2 hy
    nlinarith
  · have h := (sinh_le_self_iff).2 (le_of_not_ge hy)
    have hs := (sinh_nonpos_iff).2 (le_of_not_ge hy)
    nlinarith

lemma scalarVariance_weight_bound (y : ℝ) : (1+y^2)*(1-tanh y^2) ≤ 1 := by
  have hv : 0 ≤ 1-tanh y^2 := sub_nonneg.mpr (tanh_sq_lt_one y).le
  have hb : 1+y^2 ≤ cosh y^2 := by linarith [square_le_sinh_square y,cosh_sq_sub_sinh_sq y]
  have h := mul_le_mul_of_nonneg_right hb hv
  rw [mul_comm (cosh y^2),scalarVariance_cosh] at h
  exact h

lemma weightedScalarMoment_bound (k l : Fin 3) (y : ℝ) :
    |y^(k:ℕ)*tanh y^(l:ℕ)*(1-tanh y^2)| ≤ 1 := by
  have hv : 0 ≤ 1-tanh y^2 := sub_nonneg.mpr (tanh_sq_lt_one y).le
  have ht : |tanh y|^(l:ℕ) ≤ 1 := pow_le_one₀ (abs_nonneg _) (abs_tanh_lt_one y).le
  have hy : |y|^(k:ℕ) ≤ 1+y^2 := by
    fin_cases k
    · simp only [pow_zero]; nlinarith [sq_nonneg y]
    · simp only [pow_one]
      nlinarith [sq_nonneg (|y|-1),sq_abs y]
    · simp only [pow_two,← sq_abs y]; nlinarith [sq_abs y]
  calc
    _ = (|y|^(k:ℕ)*|tanh y|^(l:ℕ))*(1-tanh y^2) := by
      rw [abs_mul,abs_mul,abs_pow,abs_pow,abs_of_nonneg hv]
    _ ≤ (1+y^2)*(1-tanh y^2) := by
      apply mul_le_mul_of_nonneg_right _ hv
      exact (mul_le_mul_of_nonneg_left ht (by positivity)).trans (by simpa using hy)
    _ ≤ 1 := scalarVariance_weight_bound y

def weightedScalarMoment (k l : Fin 3) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun y => y^(k:ℕ)*tanh y^(l:ℕ)*(1-tanh y^2)) (by
      have ht : Continuous tanh := by
        change Continuous (fun y => tanh y)
        simp_rw [tanh_eq_sinh_div_cosh]
        exact continuous_sinh.div continuous_cosh (fun y => (cosh_pos y).ne')
      fun_prop) (1:ℝ) (fun y => by
        simpa only [Real.norm_eq_abs] using weightedScalarMoment_bound k l y)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_ScalarMomentGram
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius

def gramCoordinates (d s y : ℝ) : Fin 3 → ℝ := ![1,tanh y,(y-d)/s]

def scalarMomentGram (P : ProbabilityMeasure ℝ) (d s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let M := fun k l => ∫ y,weightedScalarMoment k l y ∂P
  !![M 0 0,M 0 1,(M 1 0-d*M 0 0)/s;
     M 0 1,M 0 2,(M 1 1-d*M 0 1)/s;
     (M 1 0-d*M 0 0)/s,(M 1 1-d*M 0 1)/s,
       (M 2 0-2*d*M 1 0+d^2*M 0 0)/s^2]

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_EqualityCurve
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal

def scalarCurve (j t : ℝ) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal (scalarFixedPoint j t) (scalarFixedPoint j t).toNNReal,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩

def scalarBMoment (P : ProbabilityMeasure ℝ) : ℝ := 1-scalarQMoment P

def scalarEMoment (P : ProbabilityMeasure ℝ) : ℝ := ∫ y,weightedScalarMoment 0 2 y ∂P

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ScalarEmpirical
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open Set Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal
namespace SKGap
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def scalarEmpirical (y : ι → ℝ) (t σ : ℝ) : ScalarPoint := (empiricalLaw y,(t,σ))

def scalarIntegrand (j t σ : ℝ) (y : ι → ℝ) : ℝ :=
  exp ((Fintype.card ι:ℝ)*scalarPsi j (scalarEmpirical y t σ))*
    productNormal (scalarD j (scalarEmpirical y t σ)) (scalarS j (scalarEmpirical y t σ)) y

end SKGap

namespace SKGap

def scalarBox (j R T smin : ℝ) : Set ScalarPoint :=
  (momentBall R ×ˢ (Icc 0 T ×ˢ Icc 0 1)) ∩ {p | smin ≤ scalarS j p}

end SKGap

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_SquareTail
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open Set Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace SKGap

def squareTail (R y : ℝ) : ℝ := if R < |y| then y^2 else 0

end SKGap

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RankCovariance
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rankOneCovariance (s r : ℝ) (m : ι → ℝ) : Matrix ι ι ℝ :=
  s • (1 : Matrix ι ι ℝ)+r • vecMulVec m m

def rankOneCovarianceInverse (s r : ℝ) (m : ι → ℝ) : Matrix ι ι ℝ :=
  s⁻¹ • (1 : Matrix ι ι ℝ)-(r/(s*(s+r*(m⬝ᵥm)))) • vecMulVec m m

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rankOneTransform (a b : ℝ) (u : ι → ℝ) : Matrix ι ι ℝ :=
  a • (1 : Matrix ι ι ℝ)+(b-a) • vecMulVec u u

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianLinearDensity
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def radialDensity (a : ℝ) (x : ι → ℝ) : ℝ :=
  ((sqrt (2*Real.pi)*a)⁻¹)^(Fintype.card ι)*exp (-(x⬝ᵥx)/(2*a^2))

end SKGap.GaussianDensity
end
end

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal NNReal
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
  {P : Measure Ω} {X : Ω → ι → ℝ}

def rankOneDensity (s r : ℝ) (m x : ι → ℝ) : ℝ :=
  sqrt (s/(s+r*(m⬝ᵥm)))*radialDensity (sqrt s) x*
    exp (r/(2*s*(s+r*(m⬝ᵥm)))*(m⬝ᵥx)^2)

end SKGap.GaussianDensity
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Posterior_GOEObservation
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def goeObservation (r v : ℝ) (m : ι → ℝ) (g : MatrixCoordinates ι → ℝ) : ι → ℝ :=
  fun i => (goeMatrix r g*ᵥm) i+sqrt v*g (.inr i)

def observationCoeff (r v : ℝ) (m : ι → ℝ) : Matrix ι (MatrixCoordinates ι) ℝ :=
  fun i a => (∑ k, m k*goeEntryCoeff r (i,k) a)+sqrt v*(if a=Sum.inr i then 1 else 0)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_GOERegression
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def goeCrossCovariance (r : ℝ) (m : ι → ℝ) : Matrix (ι × ι) ι ℝ :=
  fun p l => r*((if p.1=l then m p.2 else 0)+(if p.2=l then m p.1 else 0))

def goeRegressionCoefficient (r v : ℝ) (m : ι → ℝ) : Matrix (ι × ι) ι ℝ :=
  goeCrossCovariance r m * rankOneCovarianceInverse (r*(m⬝ᵥm)+v) r m

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real GaussianDensity
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma continuous_radialDensity (a : ℝ) : Continuous (radialDensity (ι := ι) a) := by
  unfold radialDensity dotProduct
  fun_prop

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Bilinear2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def exactG (j : ℝ) (a : ι → ℝ) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  pathDiagonal a 1*(1-pathDiagonal a 1*(M-((j/(Fintype.card ι:ℝ))*∑ b,a b) • 1)*pathDiagonal a 1)⁻¹*pathDiagonal a 1

def bilinearDataD (k : Fin 3) (q : ℝ) (a : ι → ℝ) : ι → ℝ :=
  if k=0 then a else fun i => 1+q*a i

def bilinearDataE (k : Fin 3) : ι → ℝ := if k=1 then 1 else 0

def bilinearDataW (k : Fin 3) : ℝ := if k=2 then 1 else 0

def bilinearError (k : Fin 3) (j : ℝ) (a : ι → ℝ) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  let q := (j/(Fintype.card ι:ℝ))*∑ b,a b
  if k=0 then exactG j a M-diagonal a
  else if k=1 then exactG j a M*M-q • diagonal a
  else M*exactG j a M*M-q • (1:Matrix ι ι ℝ)-q^2 • diagonal a

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_BilinearUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap Topology

def bilinearPathGood {n : ℕ} (j A : ℝ) (a : Fin n → ℝ)
    (g : MatrixCoordinates (Fin n) → ℝ) : Prop :=
  ∀ z ∈ Icc (0:ℝ) 1, g ∈ truncationGoodSet (j/(n:ℝ))
    (2*sqrt j+1+1) ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A))
    (pathDiagonal a z) (pathShift z ((j/(n:ℝ))*∑ b,a b))

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι κ : Type*} [Fintype ι]

def matrixPair (G : Matrix ι ι ℝ) (x y : ι → ℝ) := x ⬝ᵥ (G*ᵥy)

def residualGramVector (B : ℝ) (W : Matrix ι ι ℝ) (u : ι → ℝ) :=
  (Real.sqrt B)⁻¹ • (W*ᵥu-B • u)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_GramUniformRobust
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius

variable {κ ν : Type*} [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]

def augmentedGram (H : Matrix κ κ ℝ) : Matrix (κ ⊕ ν) (κ ⊕ ν) ℝ :=
  fromBlocks H 0 0 1

def augmentedCoefficient (C : Matrix κ κ ℝ) (V : Matrix κ ν ℝ) :
    Matrix (κ ⊕ ν) (κ ⊕ ν) ℝ := fromBlocks (C-V*Vᵀ) V Vᵀ 0

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ConditionalRankAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators
variable {ι : Type*}

def conditionalColumns (X M G N : ι → ℝ) : Matrix ι ((Fin 3) ⊕ Unit) ℝ :=
  fun i k => Sum.elim (fun l => ![X i,M i,G i] l) (fun _ => N i) k

def conditionalCoupling (c : ℝ) : Matrix (Fin 3) Unit ℝ := fun k _ => ![0,c,0] k

def conditionalCoefficient (j cM cG cN : ℝ) :
    Matrix ((Fin 3) ⊕ Unit) ((Fin 3) ⊕ Unit) ℝ :=
  fromBlocks !![j,0,0;0,cM,cG;0,cG,0] (conditionalCoupling cN)
    (conditionalCoupling cN)ᵀ 0

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_GOEBilinearCov
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def goeBilinear (r : ℝ) (x y : ι → ℝ) (g : MatrixCoordinates ι → ℝ) : ℝ :=
  x⬝ᵥ(goeMatrix r g*ᵥy)

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def unitRow (κ : ℝ) (u : ι → ℝ) (i : ι) : ι → ℝ :=
  Pi.single i 1+((κ-1)*u i) • u

def goeBlockResidual (r κ ell : ℝ) (u : ι → ℝ) (g : MatrixCoordinates ι → ℝ) : Matrix ι ι ℝ :=
  fun i k => goeBilinear r (unitRow κ u i) (unitRow κ u k) g+
    ((ell-κ^2)*u i*u k)*goeBilinear r u u g

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ConditionalModelAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def conditionalBlockMatrix (r j q s S a B κ ell : ℝ) (u Z : ι → ℝ)
    (g : MatrixCoordinates ι → ℝ) : Matrix ι ι ℝ :=
  goeBlockResidual r κ ell u g+
    vecMulVec u ((j*sqrt (q/s)) • Z-(j*a/s) • u)+
    vecMulVec ((j*sqrt (q/s)) • Z-(j*a/s) • u) u+
    (2*j*(a+B*q)/S) • vecMulVec u u

def conditionalMeanCoefficient (j q s S a B BA κ : ℝ) :=
  conditionalCoefficient j
    ((2*j*q-2*j*a/s+2*j*(a+B*q)/S+2*BA*(κ-1))/q)
    j ((κ-1)*sqrt BA/sqrt q)

def conditionalScalarCoefficient (q κ ell : ℝ) :=
  conditionalCoefficient 0 ((ell-2*κ+1)/q) 0 0

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators Matrix.Norms.Frobenius

def conditionalKappa (j : ℝ) (p : ScalarPoint) : ℝ := sqrt ((p.2.1+p.2.2^2)/scalarS j p)
def conditionalEll (j : ℝ) (p : ScalarPoint) : ℝ :=
  sqrt ((p.2.1+p.2.2^2)/(scalarS j p+j*scalarQMoment p.1))
def conditionalMeanData (j : ℝ) (p : ScalarPoint) (r : ℝ) :
    Matrix ((Fin 3) ⊕ Unit) ((Fin 3) ⊕ Unit) ℝ :=
  conditionalMeanCoefficient j (scalarQMoment p.1) (scalarS j p)
    (scalarS j p+j*scalarQMoment p.1) (scalarA j p)
    (j*scalarBMoment p.1) (j*scalarBMoment p.1+r) (conditionalKappa j p)
def conditionalScalarData (j : ℝ) (p : ScalarPoint) :
    Matrix ((Fin 3) ⊕ Unit) ((Fin 3) ⊕ Unit) ℝ :=
  conditionalScalarCoefficient (scalarQMoment p.1) (conditionalKappa j p) (conditionalEll j p)
def curveKappa (j t : ℝ) : ℝ := sqrt (t/scalarFixedPoint j t)
def curveCoefficient (j t : ℝ) : Matrix ((Fin 3) ⊕ Unit) ((Fin 3) ⊕ Unit) ℝ :=
  conditionalCoefficient j
    ((2*j*scalarQ j t+2*(j*scalarBMoment (scalarCurve j t))*(curveKappa j t-1))/scalarQ j t)
    j ((curveKappa j t-1)*sqrt (j*scalarBMoment (scalarCurve j t))/sqrt (scalarQ j t))

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_CompactTube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators Matrix.Norms.Frobenius

def conditionalScalarSize (j : ℝ) (p : ScalarPoint) (r : ℝ) : ℝ :=
  (1+|scalarD j p|)/scalarS j p+1/scalarQMoment p.1+1/scalarS j p+
    1/(j*scalarBMoment p.1+r)+(j*scalarBMoment p.1+r)+‖conditionalScalarData j p‖

abbrev ScalarTimeDomain (R t0 T : ℝ) := (momentBall R) × (Icc t0 T)

def scalarEqualitySet (j R t0 T : ℝ) : Set (ScalarTimeDomain R t0 T) :=
  {x | (x.1 : ProbabilityMeasure ℝ)=scalarCurve j x.2}

def scalarPerturbedPoint {R t0 T : ℝ} (z : ScalarTimeDomain R t0 T × (ℝ × ℝ)) : ScalarPoint :=
  ((z.1.1 : ProbabilityMeasure ℝ),(z.1.2 : ℝ),z.2.1)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_GramColumnBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def extendColumns (p : κ → ι → ℝ) (N : ι → ℝ) : Matrix ι (κ ⊕ Unit) ℝ :=
  fun i k => Sum.elim (fun r => p r i) (fun _ => N i) k

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_ConditionalGramTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def augmentedGramTolerance (B ε : ℝ) : ℝ :=
  4*(ε+(sqrt B)⁻¹*(1+B)*ε+B⁻¹*(1+2*B+B^2)*ε)

def actualAugmentedGram {n : ℕ} (j : ℝ) (a : Fin n → ℝ)
    (p : Fin 3 → EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin n))
    (g : MatrixCoordinates (Fin n) → ℝ) : Matrix ((Fin 3) ⊕ Unit) ((Fin 3) ⊕ Unit) ℝ :=
  let B := j/(n:ℝ)*∑ i,a i
  let W := goeMatrix (j/(n:ℝ)) g
  let V := extendColumns (fun r => (p r).ofLp) (residualGramVector B W u.ofLp)
  Vᵀ*exactG j a W*V

def diagonalAugmentedGram {n : ℕ} (a : Fin n → ℝ)
    (p : Fin 3 → EuclideanSpace ℝ (Fin n)) :
    Matrix ((Fin 3) ⊕ Unit) ((Fin 3) ⊕ Unit) ℝ :=
  fromBlocks (fun r s => matrixPair (diagonal a) (p r).ofLp (p s).ofLp) 0 0 1

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_EmpiricalGramBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius

def empiricalGramColumns {n : ℕ} (y : Fin n → ℝ) (d s : ℝ) :
    Fin 3 → EuclideanSpace ℝ (Fin n) := fun r => WithLp.toLp 2 (fun i => gramCoordinates d s (y i) r/√(n:ℝ))

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_EmpiricalConditionalData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius

def empiricalUnit {n : ℕ} (y : Fin n → ℝ) (q : ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i=>tanh (y i)/sqrt ((n:ℝ)*q))

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_GOEResidualCov
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def goeRegressionResidual (r v : ℝ) (m : ι → ℝ) (g : MatrixCoordinates ι → ℝ) : (ι × ι) → ℝ :=
  (fun p => goeMatrix r g p.1 p.2)-goeRegressionCoefficient r v m*ᵥgoeObservation r v m g

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def blockCoefficient (κ ell : ℝ) (u : ι → ℝ) : Matrix (ι × ι) (ι × ι) ℝ :=
  fun p q => unitRow κ u p.1 q.1*unitRow κ u p.2 q.2+
    ((ell-κ^2)*u p.1*u p.2)*(u q.1*u q.2)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Posterior_GOEPointwisePosterior
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real GaussianDensity GaussianRegression
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def goeLaw (r : ℝ) : Measure ((ι × ι) → ℝ) :=
  (gaussianCoordinates (MatrixCoordinates ι)).map (fun g p => goeMatrix r g p.1 p.2)

def conditionalGoeLaw (r v : ℝ) (m z : ι → ℝ) : Measure ((ι × ι) → ℝ) :=
  ((gaussianCoordinates (MatrixCoordinates ι)).map (goeRegressionResidual r v m)).map
    (fun R => R+goeRegressionCoefficient r v m*ᵥz)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ConditionalEmpiricalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

def empiricalObservation {n : ℕ} [NeZero n] (j t σ : ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i=>y i-scalarD j (empiricalLaw y,t,σ)+j*scalarBMoment (empiricalLaw y)*tanh (y i)

def empiricalConditionalGoe {n : ℕ} [NeZero n] (j t σ : ℝ) (y : Fin n → ℝ)
    (g : MatrixCoordinates (Fin n) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  let p : ScalarPoint := (empiricalLaw y,t,σ)
  let q := scalarQMoment p.1
  let s := scalarS j p
  conditionalBlockMatrix (j/(n:ℝ)) j q s (s+j*q) (scalarA j p)
    (j*scalarBMoment p.1) (conditionalKappa j p) (conditionalEll j p)
    (empiricalUnit y q).ofLp (sqrt s • (empiricalGramColumns y (scalarD j p) s 2).ofLp) g

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GOEScalarTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

def conditionalBase {n : ℕ} (j : ℝ) (a : Fin n → ℝ)
    (g : MatrixCoordinates (Fin n) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1-pathDiagonal a 1*(goeMatrix (j/(n:ℝ)) g-((j/(n:ℝ))*∑ i,a i) • 1)*pathDiagonal a 1

def conditionalUpdateColumns {n : ℕ} (j : ℝ) (a : Fin n → ℝ)
    (p : Fin 3 → EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin n))
    (g : MatrixCoordinates (Fin n) → ℝ) : Matrix (Fin n) ((Fin 3) ⊕ Unit) ℝ :=
  extendColumns (fun r => (p r).ofLp)
    (residualGramVector (j/(n:ℝ)*∑ i,a i) (goeMatrix (j/(n:ℝ)) g) u.ofLp)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ConditionalTolerance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix
open scoped BigOperators Matrix.Norms.Frobenius

def augmentedToleranceConstant (L : ℝ) :=
  4*(1+(L+1)*(1+L)+L*(1+2*L+L^2))

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius

def conditionalEmpiricalCore {n : ℕ} [NeZero n] (j t σ : ℝ) (a y : Fin n → ℝ)
    (g : MatrixCoordinates (Fin n) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  let p : ScalarPoint := (empiricalLaw y,t,σ)
  let B := j*scalarBMoment p.1
  let BA := j/(n:ℝ)*∑ i,a i
  let u := empiricalUnit y (scalarQMoment p.1)
  let V := conditionalUpdateColumns j a (empiricalGramColumns y (scalarD j p) (scalarS j p)) u g
  conditionalBase j a g-pathDiagonal a 1*V*
    (conditionalMeanData j p (BA-B)+matrixBilinear (goeMatrix (j/(n:ℝ)) g) u u • conditionalScalarData j p)*
    Vᵀ*pathDiagonal a 1+(B-BA) • diagonal a

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_DiagonalHessianJoined
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def diagonalRoot (a : ι → ℝ) : Matrix ι ι ℝ := diagonal (fun i => sqrt (a i))
def diagonalHessian (a : ι → ℝ) (K : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  1-diagonalRoot a*K*diagonalRoot a

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius

def empiricalConditionalMiddle {n : ℕ} [NeZero n] (j t σ : ℝ) (y : Fin n → ℝ)
    (g : MatrixCoordinates (Fin n) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  let p : ScalarPoint := (empiricalLaw y,t,σ)
  let q := scalarQMoment p.1
  let s := scalarS j p
  let u := (empiricalUnit y q).ofLp
  let X := (empiricalGramColumns y (scalarD j p) s 0).ofLp
  let Z := sqrt s • (empiricalGramColumns y (scalarD j p) s 2).ofLp
  conditionalBlockMatrix (j/(n:ℝ)) j q s (s+j*q) (scalarA j p)
    (j*scalarBMoment p.1) (conditionalKappa j p) (conditionalEll j p) u Z g+
    j • vecMulVec X X+(2*j*q) • vecMulVec u u-
    (j*scalarBMoment p.1) • (1 : Matrix (Fin n) (Fin n) ℝ)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_RegularizedLogDet
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap.LogDet
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def regularizedGram (γ : ℝ) (M : Matrix ι ι ℝ) := Mᵀ*M+γ • 1

def regularizedLogDet (γ : ℝ) (M : Matrix ι ι ℝ) : ℝ :=
  Real.log (regularizedGram γ M).det/(Fintype.card ι:ℝ)

end SKGap.LogDet
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_CubeApprox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators Matrix.Norms.Frobenius Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def coordAverage (a : ι → ℝ) : ℝ := (∑ i,a i)/(Fintype.card ι:ℝ)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_TAPVectorTaylor
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators

def varianceAverage {n : ℕ} (y : Field n) : ℝ := 1-overlap y

def varianceLinear {n : ℕ} (y d : Field n) : ℝ :=
  (-2/(n:ℝ))*∑ i,magnetization y i*spinVariance y i*d i

def magnetizationRemainder {n : ℕ} (y d : Field n) : Field n :=
  magnetization (y+d)-magnetization y-(fun i => spinVariance y i*d i)

attribute [local irreducible] vectorNorm varianceAverage varianceLinear magnetizationRemainder tapField fieldJacobian magnetization

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_LocalGaussianMoments
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators ENNReal NNReal

def localGaussianBall (n : ℕ) : Set (Field n) := {g | vectorSqNorm g ≤ 4*(n:ℝ)}

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalVolumeEnergy
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators ENNReal NNReal

def localExponent {n : ℕ} (j σ : ℝ) (J U : Matrix (Fin n) (Fin n) ℝ) (h y g : Field n) : ℝ :=
  vectorNorm g^2/2-vectorNorm (tapField j J h (y+(σ • U)*ᵥg))^2/(2*σ^2)+
    (n:ℝ)*j*varianceAverage (y+(σ • U)*ᵥg)^2/2

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalVolumeChange
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators ENNReal NNReal

def localAction {n : ℕ} (j σ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h z : Field n) : ℝ :=
    -vectorNorm (tapField j J h z)^2/(2*σ^2)+(n:ℝ)*j*varianceAverage z^2/2

def localVolume {n : ℕ} (j σ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h : Field n) (E : Set (Field n)) : ℝ≥0∞ :=
    ENNReal.ofReal (((sqrt (2*Real.pi)*σ)⁻¹)^n) *
      ∫⁻ z in E,ENNReal.ofReal (exp (localAction j σ J h z))

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_FieldIntegralReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal
attribute [local fun_prop] continuous_radialDensity

def fieldMollifier {n : ℕ} (j σ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h y : Fin n → ℝ) : ℝ :=
  radialDensity σ (tapField j J h y)*exp ((n:ℝ)*j*(1-overlap y)^2/2)

def fieldIntegral {n : ℕ} (j σ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h : Fin n → ℝ) (E : Set (Fin n → ℝ)) : ℝ≥0∞ :=
  ∫⁻ y in E, ENNReal.ofReal (fieldMollifier j σ J h y)

def conditionalFieldWeight {n : ℕ} [NeZero n] (j t σ : ℝ)
    (E : Set (((Fin n×Fin n) → ℝ) × (Fin n → ℝ))) (y : Fin n → ℝ) : ℝ≥0∞ :=
  conditionalGoeLaw (j/(n:ℝ)) (t+σ^2) (magnetization y) (empiricalObservation j t σ y)
    {W | (W,y) ∈ E}

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

def plantedJacobianPerturbation {n : ℕ} (j : ℝ) (y : Field n) : Matrix (Fin n) (Fin n) ℝ :=
  (-j/(n:ℝ)) • vecMulVec (fun _=>1) (spinVariance y)+
  (-2*j/(n:ℝ)) • vecMulVec (magnetization y) (fun i=>magnetization y i*spinVariance y i)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ConditionalWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

instance conditionalGoeLaw_probability {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (r v : ℝ) (m z : ι → ℝ) : IsProbabilityMeasure (conditionalGoeLaw r v m z) := by
  unfold conditionalGoeLaw
  haveI : IsProbabilityMeasure ((gaussianCoordinates (MatrixCoordinates ι)).map (goeRegressionResidual r v m)) := Measure.isProbabilityMeasure_map (Measurable.aemeasurable (f := goeRegressionResidual r v m) (by
    unfold goeRegressionResidual goeObservation goeMatrix
    refine measurable_pi_lambda _ fun p => ?_
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
    fun_prop))
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ScalarRelativeIsolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal

def scalarRelativeForbidden {R t0 T : ℝ} (U : Set (ScalarTimeDomain R t0 T)) : Set ScalarPoint :=
  (fun p : ScalarPoint => (p.1,p.2.1)) ⁻¹'
    ((fun x : ScalarTimeDomain R t0 T => ((x.1 : ProbabilityMeasure ℝ),(x.2 : ℝ))) '' Uᶜ)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SparseCubeNet
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Set Real
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def optionSupport [DecidableEq ι] (f : ι → Option κ) : Finset ι :=
  Finset.univ.filter (fun i => (f i).isSome)

def optionCube (v : ι → ℝ) (grid : κ → ℝ) (f : ι → Option κ) : ι → ℝ :=
  fun i => (f i).elim (v i) grid

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ConditionalMiddleSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

def conditionalMiddleSize (j V W : ℝ) (p : ScalarPoint) : ℝ :=
  (1+2*|conditionalKappa j p-1|+|conditionalEll j p-2*conditionalKappa j p+1|)*W+
    2*(|j*sqrt (scalarQMoment p.1/scalarS j p)| * (sqrt (scalarS j p)*V)+
      |j*scalarA j p/scalarS j p|)+
    |2*j*(scalarA j p+j*scalarBMoment p.1*scalarQMoment p.1)/(scalarS j p+j*scalarQMoment p.1)|+
    |j| * V^2+|2*j*scalarQMoment p.1|+|j*scalarBMoment p.1|

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ConditionalIntegralRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

def badFieldFlat (n : ℕ) (j A ε m : ℝ) : Set (((Fin n×Fin n) → ℝ) × (Fin n → ℝ)) :=
  {p | ((fun i k=>p.1 (i,k)),p.2)∈badFieldSet n j A ε m}

def reducedBadDensity {n : ℕ} [NeZero n] (j t σ A ε m : ℝ) (y : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (sqrt (scalarS j (scalarEmpirical y t σ)/
    (scalarS j (scalarEmpirical y t σ)+j*scalarQMoment (empiricalLaw y)))*scalarIntegrand j t σ y)*
    conditionalFieldWeight j t σ (badFieldFlat n j A ε m) y

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_LogDetIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def logPathGood (R lo hi q : ℝ) (a : ι → ℝ) : Set (Matrix ι ι ℝ) :=
  {M | opNorm M ≤ R ∧ ∀ z ∈ Icc (0:ℝ) 1,
    lo ≤ ComplexSpectral.lowerRayleigh (liftMatrix (1-pathDiagonal a z*(M-pathShift z q)*pathDiagonal a z)) ∧
    -hi ≤ ComplexSpectral.lowerRayleigh (-liftMatrix (1-pathDiagonal a z*(M-pathShift z q)*pathDiagonal a z))}

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_LogDetExpected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def logdetMeanError (j R B C rate γ : ℝ) : ℝ :=
  2*(2*j+1)*C+(|log γ|+(1+j)/sqrt γ+2*((2*j+R)*B))*(3/rate)+
    (sqrt (2*j)/sqrt γ)*(8*sqrt 3/rate^2)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PlantedFixedTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators ENNReal

def plantedRootBad (n : ℕ) (j A K ε c ρ t : ℝ) :
    Set ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) :=
  {p | (∀ z : Field n,vectorNorm (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1)*ᵥz) ≤ K*vectorNorm z) ∧
    ∃ y : Field n,vectorNorm (tapField j (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1))
      (fun i=>t+p.2 i) y) ≤ ρ*sqrt (n:ℝ) ∧
      (goeMatrix (j/(n:ℝ)) p.1,y)∈badFieldSet n j A ε c}

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_RootDiagonalTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators

def rootBad {n : ℕ} (j A ε c ρ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) : Prop :=
  ∃ y : Field n,vectorNorm (tapField j J h y) ≤ ρ*sqrt (n:ℝ) ∧
    ∃ a : Field n,(∀ i,a i∈Icc 0 A) ∧
      (∑ i,(a i-spinVariance y i)^2) ≤ ε^2*(n:ℝ) ∧
      ∃ x : EuclideanSpace ℝ (Fin n),‖x‖=1 ∧ quadraticForm (fieldHessian j J y a) x.ofLp ≤ c

def eraseDiagonal {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  J-diagonal (fun i=>J i i)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_RootBadMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius
variable {n : ℕ}
local instance matrixMeasurable : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) := borel _
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_SparseSubsetEntropy
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory Real Set Filter
open scoped BigOperators Topology
variable {ι : Type*} [Fintype ι]

def smallSupports (α : ℝ) : Finset (Finset ι) := by
  classical
  exact Finset.univ.powerset.filter (fun S=>(S.card:ℝ) ≤ α*(Fintype.card ι:ℝ))

end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianMarginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

def field (t : ℝ) : {k : ℕ} → History n k → (Fin n → ℝ)
  | 0, _ => 0
  | _+1, h => fun i => field t h.1 i+sqrt t*h.2 i

end
end SKGap.GaussianHistory

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_SpinEnergy
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators

def spinMul {n : ℕ} (x y : Spin n) : Spin n := fun i => !(xor (x i) (y i))

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianPartition
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

def edgeCoefficient {n : ℕ} (r : ℝ) (x : Spin n) : Edge n→ℝ :=
  fun e=>sqrt r*spinValue (x e.1.1)*spinValue (x e.1.2)

def gaussianSpinPartition (n : ℕ) (r : ℝ) (g : Disorder n) : ℝ :=
  ∑ x : Spin n,exp (∑ e,edgeCoefficient r x e*g e)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_PartitionSecondMoment
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

def quadraticGaussianBound (j : ℝ) : ℝ := ∫ g : ℝ, exp (j*g^2/2) ∂gaussianReal 0 1

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RecipeMarked
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.MarkedPolynomial
open Diagram
variable {n : ℕ}

def diagonalWords (s : Fin n→ℝ) (P : WordPolynomial (ι:=Fin n)) : MarkedPolynomial n :=
  P.map (fun t=>(t.1,SmallMark.diagonal [] s t.2))
def averageWords (c : ℝ) (s : Fin n→ℝ) (P : WordPolynomial (ι:=Fin n)) : MarkedPolynomial n :=
  P.map (fun t=>(c*t.1,SmallMark.average s t.2))
def mass (P : WordPolynomial (ι:=Fin n)) : ℝ := (P.map (fun t=>|t.1|)).sum

abbrev Pair (n : ℕ) := MarkedPolynomial n×MarkedPolynomial n

def pairPlain (V : Pair n) : WordPolynomial (ι:=Fin n)×WordPolynomial (ι:=Fin n) := (V.1.plain,V.2.plain)

def zeroPair : Pair n := ([(0,.average 0 [])],[(0,.average 0 [.noise])])

def smallBranch (j : ℝ) (p : Fin n→ℝ) (T : SourceTree (Fin n→ℝ)) (V : Pair n) : Pair n :=
  (diagonalWords p (T.words j).2++V.1,
    ((diagonalWords p (T.words j).2).prepend [.noise]++averageWords (-j) p (T.words j).1)++V.2)

def boundedBranch (j : ℝ) (p : Fin n→ℝ) (U V : Pair n) : Pair n :=
  (U.2.prepend [.diag p]++V.1,
    (U.2.prepend [.noise,.diag p]++U.1.scale (-(j*Diagram.mean p)))++V.2)

end SKGap.Noncrossing.Primary.MarkedPolynomial

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_RecipeTraceBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.MarkedPolynomial
open Diagram
variable {n : ℕ}

def pairBudget (V : Pair n) : ℝ := V.1.budget+V.2.budget

end SKGap.Noncrossing.Primary.MarkedPolynomial

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ClosedMarked
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.Noncrossing.ClosedMarked
open Matrix
variable {n : ℕ}

abbrev Word (n : ℕ) := List (WordLetter (Fin n))
abbrev Polynomial (n : ℕ) := List (ℝ×Word n)
def matrixValue (j : ℝ) (a : Fin n→ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (P : Polynomial n) : Matrix (Fin n) (Fin n) ℝ :=
  (P.map (fun t=>t.1 • exactWord j a t.2 J)).sum
def prediction (j : ℝ) (a : Fin n→ℝ) (P : Polynomial n) (i : Fin n) : ℝ :=
  (P.map (fun t=>t.1*wordPrediction j a 1 t.2 i)).sum

def ungrade (P : Primary.Tensor.Series.GradedWords (Fin n)) : Polynomial n :=
  P.map (fun t=>(t.1,t.2.2))

inductive Mark (n : ℕ) where
  | diagonal : Word n→(Fin n→ℝ)→Word n→Mark n
  | average : (Fin n→ℝ)→Word n→Mark n
namespace Mark

def vector : Mark n→Fin n→ℝ
  | .diagonal _ s _ => s
  | .average s _ => s
def word : Mark n→Word n
  | .diagonal P s Q => P++(.diag s::Q)
  | .average _ P => P
def scalar : Mark n→ℝ
  | .diagonal _ _ _ => 1
  | .average s _ => Diagram.mean s
def prepend (P : Word n) : Mark n→Mark n
  | .diagonal Q s R => .diagonal (P++Q) s R
  | .average s Q => .average s (P++Q)
def diagnostic (d : Fin n→ℝ) : Mark n→Word n
  | .diagonal P _ Q => Q++(.diag d::P)
  | .average _ P => P

end Mark

abbrev Marked (n : ℕ) := List (ℝ×Mark n)
namespace Marked

def plain (P : Marked n) : Polynomial n := P.map (fun t=>(t.1*t.2.scalar,t.2.word))
def budget (P : Marked n) : ℝ := (P.map (fun t=>|t.1| *SKGapCutoff.Recipe.vectorNorm t.2.vector)).sum
def prepend (F : Word n) (P : Marked n) : Marked n := P.map (fun t=>(t.1,t.2.prepend F))
def scale (c : ℝ) (P : Marked n) : Marked n := P.map (fun t=>(c*t.1,t.2))
end Marked
end SKGap.Noncrossing.ClosedMarked

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.Noncrossing.ClosedMarked
open Matrix Primary Primary.Tensor.Series
variable {n : ℕ}

namespace Marked

def diagonalWords (s : Fin n→ℝ) (P : GradedWords (Fin n)) : Marked n :=
  P.map (fun t=>(t.1,Mark.diagonal [] s t.2.2))
def averageWords (c : ℝ) (s : Fin n→ℝ) (P : GradedWords (Fin n)) : Marked n :=
  P.map (fun t=>(c*t.1,Mark.average s t.2.2))
def mass (P : GradedWords (Fin n)) : ℝ := (P.map (fun t=>|t.1|)).sum
end Marked

abbrev Pair (n : ℕ) := Marked n×Marked n
def pairPlain (P : Pair n) : Polynomial n×Polynomial n := (P.1.plain,P.2.plain)
def pairUngrade (P : GradedWords (Fin n)×GradedWords (Fin n)) := (ungrade P.1,ungrade P.2)
def zeroPair : Pair n := ([(0,.average 0 [])],[(0,.average 0 [.noise])])

def implicitPair (j : ℝ) (a p : Fin n→ℝ) (t : SourceTree (Fin n→ℝ)) : Pair n :=
  let T:=GradedWords.ordinaryWords j t
  let S:=(Marked.diagonalWords p T.2).prepend [.inverse]++
    (Marked.averageWords (-j) p T.1).prepend [.inverse,.diag a]
  (S,(S.prepend [.noise]++S.scale (-(j*Diagram.mean a)))++Marked.averageWords (-j) p T.1)

def smallBranch (j : ℝ) (p : Fin n→ℝ) (T : GradedWords (Fin n)×GradedWords (Fin n)) (V : Pair n) : Pair n :=
  (Marked.diagonalWords p T.2++V.1,
    ((Marked.diagonalWords p T.2).prepend [.noise]++Marked.averageWords (-j) p T.1)++V.2)
def boundedBranch (j : ℝ) (p : Fin n→ℝ) (U V : Pair n) : Pair n :=
  (U.2.prepend [.diag p]++V.1,
    (U.2.prepend [.noise,.diag p]++U.1.scale (-(j*Diagram.mean p)))++V.2)

inductive SmallTree (n : ℕ) where
  | zero
  | implicit : (Fin n→ℝ)→SourceTree (Fin n→ℝ)→SmallTree n
  | small : (Fin n→ℝ)→ClosedTree (Fin n→ℝ)→SmallTree n→SmallTree n
  | bounded : (Fin n→ℝ)→SmallTree n→SmallTree n→SmallTree n
namespace SmallTree

def tree : SmallTree n→ClosedTree (Fin n→ℝ)
  | .zero=>.leaf 0
  | .implicit p T=>.implicit p T
  | .small p T V=>.branch p T V.tree
  | .bounded p T V=>.branch p T.tree V.tree
def marked (j : ℝ) (a : Fin n→ℝ) : SmallTree n→Pair n
  | .zero=>zeroPair
  | .implicit p T=>implicitPair j a p T
  | .small p T V=>smallBranch j p (T.words j a) (V.marked j a)
  | .bounded p T V=>boundedBranch j p (T.marked j a) (V.marked j a)
end SmallTree
end SKGap.Noncrossing.ClosedMarked

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_StartedRecipe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap.Noncrossing.Primary
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n ι κ σ)

def startedEvaluate (D : OrdinaryData n ι κ σ) (w y : VectorFields n) (a : ℕ) : VectorFields n×VectorFields n :=
  match a with
  | 0 => (w,y)
  | a+1 => let prev:=fun b : Fin (a+1)=>startedEvaluate D w y b
      (D.sourceOf (a+1) (fun b=>(prev b).2),
       D.fieldOf (a+1) (fun b=>(prev b).1) (fun b=>(prev b).2))
termination_by a

def startedSource (w y : VectorFields n) (a : ℕ) : VectorFields n := (D.startedEvaluate w y a).1
def startedAuxiliary (w y : VectorFields n) (a : ℕ) : VectorFields n := (D.startedEvaluate w y a).2
def startedPartial (w y : VectorFields n) (a : ℕ) (l : ι) : VectorFields n :=
  D.partialOf a l (fun b=>D.startedAuxiliary w y b)

@[simp] lemma startedSource_zero (w y : VectorFields n) : D.startedSource w y 0=w := by
  rw [startedSource,startedEvaluate]
@[simp] lemma startedAuxiliary_zero (w y : VectorFields n) : D.startedAuxiliary w y 0=y := by
  rw [startedAuxiliary,startedEvaluate]

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_ClosedTreeMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor.Series.ClosedTree
open Matrix GradedWords
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def ofOrdinary : SourceTree (ι→ℝ)→ClosedTree (ι→ℝ)
  | .leaf c => .leaf c
  | .branch p t u => .branch p (ofOrdinary t) (ofOrdinary u)

def sourceMatrix (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) (t : ClosedTree (ι→ℝ)) :=
  GradedWords.matrixValue j a J (t.words j a).1
def fieldMatrix (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) (t : ClosedTree (ι→ℝ)) :=
  GradedWords.matrixValue j a J (t.words j a).2

def branches (xs : List ((ι→ℝ)×ClosedTree (ι→ℝ))) : ClosedTree (ι→ℝ) :=
  xs.foldr (fun t v=>.branch t.1 t.2 v) (.leaf 0)

end SKGap.Noncrossing.Primary.Tensor.Series.ClosedTree

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_StartedGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

def startedTree (D : OrdinaryData n ι κ σ) (w y : VectorFields n)
    (T : ι→SourceTree (Fin n→ℝ)) (t₀ : ClosedTree (Fin n→ℝ)) (x : Spin n)
    (a : ℕ) : ClosedTree (Fin n→ℝ) :=
  match a with
  | 0 => t₀
  | a+1 => ClosedTree.branches
      ((Finset.univ.toList.map (fun l=>(D.startedPartial w y (a+1) l x,ClosedTree.ofOrdinary (T l))))++
       (Finset.univ.toList.map (fun b : Fin (a+1)=>(D.auxCoefficient (a+1) b x,startedTree D w y T t₀ x b))))
termination_by a

variable (D : OrdinaryData n ι κ σ) (w y : VectorFields n)
    (T : ι→SourceTree (Fin n→ℝ)) (t₀ : ClosedTree (Fin n→ℝ)) (a₀ : Fin n→ℝ) (x : Spin n)
def startedRetainedSource (a : ℕ) := (D.startedTree w y T t₀ x a).sourceMatrix D.j a₀ D.J
def startedRetainedField (a : ℕ) := (D.startedTree w y T t₀ x a).fieldMatrix D.j a₀ D.J

end SKGapCutoff.Recipe.OrdinaryData

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n ι κ σ) (w y : VectorFields n)
    (T : ι→SourceTree (Fin n→ℝ)) (t₀ : ClosedTree (Fin n→ℝ)) (a₀ : Fin n→ℝ) (x : Spin n)

def startedSourceError (a : ℕ) : Interaction n :=
  derivativeMatrix (D.startedSource w y a) x-D.startedRetainedSource w y T t₀ a₀ x a
def startedFieldError (a : ℕ) : Interaction n :=
  derivativeMatrix (D.startedAuxiliary w y a) x-D.startedRetainedField w y T t₀ a₀ x a

@[simp] lemma startedSourceError_zero : D.startedSourceError w y T t₀ a₀ x 0=
    derivativeMatrix w x-t₀.sourceMatrix D.j a₀ D.J := by
  simp [startedSourceError,startedRetainedSource,startedTree]
@[simp] lemma startedFieldError_zero : D.startedFieldError w y T t₀ a₀ x 0=
    derivativeMatrix y x-t₀.fieldMatrix D.j a₀ D.J := by
  simp [startedFieldError,startedRetainedField,startedTree]

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_StartedMarked
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.ClosedMarked.SmallTree
open Primary Primary.Tensor.Series
variable {n : ℕ}

def smallBranches (xs : List ((Fin n→ℝ)×ClosedTree (Fin n→ℝ))) (U : SmallTree n) : SmallTree n :=
  xs.foldr (fun t v=>.small t.1 t.2 v) U
def boundedBranches (xs : List ((Fin n→ℝ)×SmallTree n)) (U : SmallTree n) : SmallTree n :=
  xs.foldr (fun t v=>.bounded t.1 t.2 v) U
end SKGap.Noncrossing.ClosedMarked.SmallTree

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ClosedMarkedControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.ClosedMarked
open SKGapCutoff.Recipe Primary Primary.Tensor.Series Marked
variable {n : ℕ}

def MarkControl (A : ℝ) (L : ℕ) (t : Mark n) : Prop :=
  ∀d:Fin n→ℝ,(∀i,|d i|≤1)→ closedWordBounded A (t.diagnostic d) ∧ (t.diagnostic d).length≤L

def MarkedControl (A : ℝ) (L : ℕ) (P : Marked n) : Prop := ∀t∈P,MarkControl A L t.2

def PairControl (A : ℝ) (L : ℕ) (P : Pair n) : Prop := MarkedControl A L P.1 ∧ MarkedControl A L P.2

end SKGap.Noncrossing.ClosedMarked

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.ClosedMarked
open SKGapCutoff.Recipe Primary Primary.Tensor.Series Marked
variable {n : ℕ}

def GradedControl (A : ℝ) (L : ℕ) (P : GradedWords (Fin n)) : Prop :=
  ∀v∈P,closedWordBounded A v.2.2 ∧ v.2.2.length≤L

end SKGap.Noncrossing.ClosedMarked

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_DriftSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

def driftSquare (p q : Prior n) (t : ℝ) {k : ℕ} (h : History n k) : ℝ :=
  ∑i,(mean (posterior q t h) i-mean (posterior p t h) i)^2

end
end SKGap.GaussianHistory

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Envelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

def envelope (p : Prior n) (t : ℝ) {k : ℕ} (A : Set (History n k)) (f : Spin n→ℝ)
    (h : History n k) : ℝ :=
  by classical exact if h∈A then var (posterior p t h) f else avg (posterior p t h) (fun x => (f x)^2)

def envelopeIntegral (p : Prior n) (t : ℝ) {k : ℕ} (A : Set (History n k)) (f : Spin n→ℝ) : ℝ :=
  ∫h,density p t h*envelope p t A f h ∂reference n k

end
end SKGap.GaussianHistory

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_CondSubConst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

def localizationLoss (n : ℕ) (t W A a b T : ℝ) : ℝ :=
  16*(n:ℝ)^2*T*t+(exp (4*T/a)*(T*(W*(n:ℝ)+2*A*sqrt (n:ℝ)+4/a)+64*(n:ℝ)^2*T*t)+1)/(b*(n:ℝ))

def localizationCost (n : ℕ) (A a b D L T : ℝ) : ℝ :=
  D*T+L+exp (4*T/a)*T*A*sqrt (n:ℝ)/(b*(n:ℝ))

end
end SKGap.GaussianHistory

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

def goodPrefix (B : ∀k, Set (History n k)) : ∀k,Set (History n k)
  | 0 => (B 0)ᶜ
  | k+1 => (Prod.fst ⁻¹' goodPrefix B k) ∩ (B (k+1))ᶜ

end
end SKGap.GaussianHistory

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_DiagonalStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

def erasedPlantedRootBad (n : ℕ) (j A K ε c ρ t : ℝ) :
    Set ((MatrixCoordinates (Fin n)→ℝ) × (Fin n→ℝ)) :=
  {p | (∀ z : Field n, vectorNorm
      (eraseDiagonal (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1))*ᵥz) ≤ K*vectorNorm z) ∧
    rootBad j A ε c ρ (eraseDiagonal (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1)))
      (fun i=>t+p.2 i)}

end SKGap.ObservationBridge

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_TAPGauge
attribute [-instance] _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators

def spinAct {n : ℕ} (s : Spin n) (y : Field n) : Field n :=
  fun i=>spinValue (s i)*y i

def spinMatrixAct {n : ℕ} (s : Spin n) (J : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i k=>spinValue (s i)*J i k*spinValue (s k)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_GaugeStabilityLaw
attribute [-instance] _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
variable {n : ℕ}
local instance matrixMeasurable : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) := borel _

def operatorBound (K : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ z : Field n,vectorNorm (J*ᵥz) ≤ K*vectorNorm z

def literalBadPair (j A K ε c ρ : ℝ) : Set (Matrix (Fin n) (Fin n) ℝ × Field n) :=
  {p | operatorBound K p.1 ∧ rootBad j A ε c ρ p.1 p.2}

def edgeSpinSign (s : Spin n) (e : Edge n) : ℝ := spinValue (s e.1.1)*spinValue (s e.1.2)
lemma edgeSpinSign_sq (s : Spin n) (e : Edge n) : edgeSpinSign s e^2=1 := by
  simp only [edgeSpinSign,mul_pow,spinValue_sq,one_mul]

def plantedEdges (r : ℝ) (s : Spin n) (g : Disorder n) : Disorder n :=
  fun e=>sqrt r*g e+r*spinValue (s e.1.1)*spinValue (s e.1.2)
def plusPlantedEdges (r : ℝ) (g : Disorder n) : Disorder n := fun e=>sqrt r*g e+r

end SKGap.ObservationBridge

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PlantedMarginalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
variable {n : ℕ}
local instance marginalMatrixMeasurable : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) := borel _

def goeEdges (r : ℝ) (g : MatrixCoordinates (Fin n)→ℝ) : Disorder n :=
  fun e=>goeMatrix r g e.1.1 e.1.2
end SKGap.ObservationBridge

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_FixedTimeAnnealed
attribute [-instance] _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
variable {n : ℕ}
local instance annealedMatrixMeasurable : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) := borel _

def gibbsObservationBad (j A K ε c ρ t : ℝ) (s : Spin n) : Set (Disorder n × Field n) :=
  {p | (coupling p.1,(fun i=>t*spinValue (s i)+p.2 i))∈literalBadPair j A K ε c ρ}

def conditionalSpinFailure (j A K ε c ρ t : ℝ) (s : Spin n) (J : Disorder n) : ℝ≥0∞ :=
  (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal))
    ((Prod.mk J) ⁻¹' gibbsObservationBad j A K ε c ρ t s)

def fixedTimeFailureENN (j A K ε c ρ t : ℝ) (J : Disorder n) : ℝ≥0∞ :=
  ∑ s : Spin n, ENNReal.ofReal (mass J 0 s)*conditionalSpinFailure j A K ε c ρ t s J

end SKGap.ObservationBridge

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_FixedTimeQuenched
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

def fixedTimeFailure (n : ℕ) (j A K ε c ρ t : ℝ) (J : Disorder n) : ℝ :=
  (fixedTimeFailureENN j A K ε c ρ t J).toReal

def partitionSizeBias (β : ℝ) (n : ℕ) (J : Disorder n) : ℝ :=
  partition J 0/(∫ J,partition J 0 ∂disorderLaw β n)

end SKGap.ObservationBridge

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_GridSteps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianHistory
open Real Filter
open scoped Topology
noncomputable section

def gridSteps (n : ℕ) : ℕ := (n+1)^4
def gridStep (T : ℝ) (n : ℕ) : ℝ := T/(gridSteps n:ℝ)

end
end SKGap.GaussianHistory

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RecipeCoefficientClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

def SegmentValue (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ) (x : Spin n) (K : ℝ) : Prop :=
  ∀i k t,t∈Set.Icc (0:ℝ) 1→|F i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))|≤K

namespace OrdinaryData

structure CoefficientClass (D : OrdinaryData n ι κ σ) (N : ℕ) (x : Spin n) (K : ℝ) : Prop where
  one_le : 1≤K
  seedRegular : ∀a≤N,∀s,SegmentRegular D.H D.θ (D.seedFunction a s) (D.seedDerivative a s) x K
  auxRegular : ∀a≤N,∀b,SegmentRegular D.H D.θ (D.auxFunction a b) (D.auxDerivative a b) x K
  seedValue : ∀a≤N,∀s,SegmentValue D.H D.θ (D.seedFunction a s) x K
  auxValue : ∀a≤N,∀b,SegmentValue D.H D.θ (D.auxFunction a b) x K

end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ConditionalMean
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
namespace SKGapCutoff.Static

noncomputable def conditionalMean {n : ℕ} (P : Spin n → ℝ) (x : Spin n)
    (i : Fin n) : ℝ :=
  spin x i * ((P x - P (flip x i)) / (P x + P (flip x i)))

@[simp] lemma conditionalMean_flip {n : ℕ} (P : Spin n → ℝ)
    (x : Spin n) (i : Fin n) : conditionalMean P (flip x i) i = conditionalMean P x i := by
  simp only [conditionalMean, flip_flip, spin_flip_self]
  rw [add_comm (P (flip x i)), ← neg_sub (P x) (P (flip x i)), neg_div, neg_mul_neg]

end SKGapCutoff.Static

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_WeakResidual
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
variable {n : ℕ}

def conditionalVariance (P : Spin n→ℝ) (x : Spin n) (i : Fin n) : ℝ :=
  1-(conditionalMean P x i)^2

def varianceEnergy (P : Spin n→ℝ) (f : Observables n) : ℝ :=
  ∑ x,P x*∑ i,conditionalVariance P x i*(halfDiff i f x)^2

end SKGapCutoff.Static

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalWeakBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
open Classical
variable {n : ℕ}

def flipNeighborhood (E : Set (Spin n)) : Set (Spin n) :=
  {x | x∈E ∨ ∃i,flip x i∈E}

end SKGapCutoff.Static

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalUniformWeak
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
open Primary Recipe
universe u
variable {Ω : Type u} {n : Ω→ℕ}

def LocalUniformMultiplier (E : ∀a,Set (Spin (n a))) (θ : ∀a,Observables (n a)) : Prop :=
  ∃B L : ℝ,0≤B ∧ 0≤L ∧ (∀a x,x∈flipNeighborhood (E a)→|θ a x|≤B) ∧
    (∀a x,x∈E a→∑i,(halfDiff i (θ a) x)^2≤L^2)

end SKGapCutoff.Static

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_UniformRecipeClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M : ℕ}
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

structure FamilyRecipe (j : ℝ) (J : ∀a,Interaction (n a)) (h : ∀a,Fin (n a)→ℝ)
    (D : ∀a,OrdinaryData (n a) (Fin M) (Fin M) σ) (N p : ℕ) (K : ℝ) : Prop where
  interaction : ∀a,(D a).J=J a
  coupling : ∀a,(D a).j=j
  primary : ∀a q,(D a).H q=fld j (J a) (h a) q.val
  predecessor : ∀a q,(D a).predecessor q=mag j (J a) (h a) q.val
  parameter : ∀a q,(D a).θ q=fun x=>j*(onsager j (J a) (h a) (q.val+1) x-onsager j (J a) (h a) q.val x)
  seed : ∃S : ℝ,0≤S ∧ ∀a,(∑s,vectorNorm ((D a).seed s))≤S
  coefficients : ∀a x,(D a).CoefficientClass N x K
  admissible : ∀a,(D a).Admissible N p

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalRecipeClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
variable {σ τ : Type} [Fintype σ] [Fintype τ]

structure LocalFamilyRecipe (E : ∀a,Set (Spin (n a))) (j : ℝ)
    (J : ∀a,Interaction (n a)) (h : ∀a,Fin (n a)→ℝ) (Θ : ∀a,κ→Observables (n a))
    (w y : ∀a,VectorFields (n a)) (D : ∀a,OrdinaryData (n a) (Fin M) κ σ) (N p : ℕ) (K : ℝ) : Prop where
  positive : 1≤N
  interaction : ∀a,(D a).J=J a
  coupling : ∀a,(D a).j=j
  primary : ∀a q,(D a).H q=fld j (J a) (h a) q.val
  predecessor : ∀a q,(D a).predecessor q=mag j (J a) (h a) q.val
  parameter : ∀a,(D a).θ=Θ a
  seed : ∃S : ℝ,0≤S ∧ ∀a,(∑s,vectorNorm ((D a).seed s))≤S
  coefficients : ∀a x,x∈flipNeighborhood (E a)→(D a).CoefficientClass N x K
  admissible : ∀a,(D a).Admissible N p
  initial : ∀a x,x∈E a→(D a).startedSource (w a) (y a) 1 x=w a x ∧
    (D a).startedAuxiliary (w a) (y a) 1 x=y a x

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalStartedDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.ClosedMarked
open Matrix Primary Primary.Tensor.Series
variable {n : ℕ}
open Marked

def pairBudget (V : Pair n) : ℝ := V.1.budget+V.2.budget
end SKGap.Noncrossing.ClosedMarked

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PhiCoefficient
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory
namespace SKGap.Stein

def phiA (z r a : ℝ) : ℝ := ∫u in (0:ℝ)..1,
  ((1-u^2)/2)*(weight a u*Real.cosh (u*(z-r))/(Real.cosh z*Real.cosh r))

end SKGap.Stein

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PhiResponse
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.Stein
open KernelExpr

def phiR (z r a : ℝ) : ℝ := eval (dr (atom 0 0 false)) z r a
def phiRZ (z r a : ℝ) : ℝ := eval (dz (dr (atom 0 0 false))) z r a

end SKGap.Stein

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PrimaryLocalInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Primary
open Recipe SKGap.Noncrossing.Primary
variable {n : ℕ}

def averageBudget (j R B : ℝ) (k : ℕ) : ℝ :=
  let C:=differentiationBound j R B k
  let T:=C+8*C^2
  2*T+4*T^2
lemma averageBudget_nonneg {j R B : ℝ} (hR : 0≤R) (hB : 0≤B) (k : ℕ) :
    0≤averageBudget j R B k := by
  have hh:=differentiationBound_nonneg (j:=j) hR hB k
  unfold averageBudget
  positivity

def localPrimaryBudget (j R B : ℝ) (M : ℕ) : ℝ :=
  ∑q:Fin M,(differentiationBound j R B q.val+averageBudget j R B q.val)
lemma localPrimaryBudget_nonneg {j R B : ℝ} (hR : 0≤R) (hB : 0≤B) (M : ℕ) :
    0≤localPrimaryBudget j R B M :=
  Finset.sum_nonneg (fun index _=>add_nonneg
    (differentiationBound_nonneg hR hB index.val) (averageBudget_nonneg hR hB index.val))

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PrimaryQuenched
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Primary
open SKGap Matrix MeasureTheory ProbabilityTheory Real Set
open SKGap.Noncrossing.Primary

variable {n : ℕ}
def formalOpBound (j R : ℝ) : ℕ→ℝ
  | 0 => 1
  | 1 => R
  | k+2 => R*formalOpBound j R (k+1)+|j| *formalOpBound j R k

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_QuenchedHelpers
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.disorderLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.FullMain
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
noncomputable section

def Whp (β : ℝ) (P : ∀n,Disorder n→Prop) : Prop :=
  Tendsto (fun n=>disorderLaw β n {g | ¬P n g}) atTop (𝓝 0)

end
end SKGap.FullMain

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RareCoordinate
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators

variable {ι : Type*} [Fintype ι] {E : ι→Type*} [∀ i,MeasurableSpace (E i)]

def rareCount (B : ∀ i,Set (E i)) (x : ∀ i,E i) : ℝ := by
  classical
  exact ∑ i,if x i∈B i then 1 else 0

end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_TapPotential
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Real Matrix Set Filter Function
open scoped Topology
namespace SKGap

def tapPotential {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h y : Field n) : ℝ :=
  (∑ i, (y i * magnetization y i - log (cosh (y i)))) -
    (∑ i, h i * magnetization y i) -
    (1/2:ℝ) * quadraticForm J (magnetization y) +
    (j/2) * vectorSqNorm (magnetization y) -
    (j/(4*n)) * vectorSqNorm (magnetization y)^2

def weightedTap {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h y : Field n) : Field n := fun i => spinVariance y i * tapField j J h y i

abbrev EField (n : ℕ) := EuclideanSpace ℝ (Fin n)

def tapPotentialE {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h : Field n) (y : EField n) : ℝ := tapPotential j J h (WithLp.ofLp y)

def weightedTapE {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h : Field n) (y : EField n) : EField n :=
  WithLp.toLp 2 (weightedTap j J h (WithLp.ofLp y))

def weightedJacobianMap {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (y : Field n) : Field n →L[ℝ] Field n :=
  ContinuousLinearMap.pi (fun i => spinVariance y i •
    ((ContinuousLinearMap.proj i : Field n →L[ℝ] ℝ).comp
      (fieldJacobian j J y).mulVecLin.toContinuousLinearMap))

def fieldBoxE (n : ℕ) (R : ℝ) : Set (EField n) :=
  (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm '' Metric.closedBall (0:Field n) R

section Basins
variable {X : Type*} [TopologicalSpace X] (T : X → X)

def attractionBasin (p : X) : Set X :=
  {x | Tendsto (fun n : ℕ => T^[n] x) atTop (𝓝 p)}

end Basins
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_FixedNormRecipeEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter

namespace SKGapCutoff
namespace GapBridge

def edgeInteraction {n : ℕ} (g : SKGap.Disorder n) : Interaction n := Matrix.of (SKGap.coupling g)

end GapBridge
end SKGapCutoff
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_StartedWordClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series
open SKGap.Noncrossing.ClosedMarked
variable {n : ℕ}

def ClosedWordDiagramBound (j : ℝ) (a : Fin n→ℝ) (J : Interaction n) (A B : ℝ) (L : ℕ) : Prop :=
  ∀w:List (WordLetter (Fin n)),w.length≤L→inverseCount w≤1→closedWordBounded A w→
    diagonalSeminorm (exactWord j a w J-Matrix.diagonal (wordPrediction j a 1 w))≤B

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary MeasureTheory ProbabilityTheory Real Set
variable {n : ℕ}

def ClosedWordSeminormBound (j : ℝ) (a : Fin n→ℝ) (J : Interaction n)
    (A C : ℝ) (L : ℕ) : Prop :=
  ∀(p : Bool) (w : List (WordLetter (Fin n))),w.length≤L→inverseCount w≤1→closedWordBounded A w→
    matrixWordSeminorm p (exactWord j a w J-Matrix.diagonal (wordPrediction j a 1 w))≤C

def ClosedWordEvent (j A D c C : ℝ) (L : ℕ) (J : Interaction n) : Prop :=
  ∀a:Fin n→ℝ,(∀i,a i∈Icc 0 A)→
    c≤ComplexSpectral.lowerRayleigh (RealComplex.liftMatrix (stabilityMatrix a 1 ((j/n)*∑i,a i) J))→
    ClosedWordSeminormBound j a J D C L

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_BufferedClosedWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary Matrix MeasureTheory ProbabilityTheory Real Set Filter
variable {n : ℕ}

def inverseDenominator (j : ℝ) (a : Fin n→ℝ) (J : Interaction n) : Interaction n :=
  1-Matrix.diagonal a*(J-((j/n)*∑i,a i) • 1)

def BufferedClosedWordEvent (j A D c C : ℝ) (L : ℕ) (J : Interaction n) : Prop :=
  ∀a:Fin n→ℝ,(∀i,a i∈Icc 0 A)→
    c<ComplexSpectral.lowerRayleigh (RealComplex.liftMatrix (stabilityMatrix a 1 ((j/n)*∑i,a i) J))→
    (inverseDenominator j a J).det≠0→ClosedWordSeminormBound j a J D C L

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_GOESparse
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators RealInnerProductSpace
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def principalOperatorNorm (M : Matrix ι ι ℝ) (S : Finset ι) : ℝ :=
  ‖matrixOperator (M.submatrix (fun i : S=>i.1) (fun i : S=>i.1))‖

end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_TanhMatrixBounds
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators
variable {n : ℕ}

def goeDisorder (r : ℝ) (g : MatrixCoordinates (Fin n)→ℝ) : Disorder n :=
  fun e=>goeMatrix r g e.1.1 e.1.2

end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ImplicitLinear
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ImplicitSystem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def rank (u v : E) : E →L[ℝ] E := (innerSL ℝ v).smulRight u

@[simp] lemma rank_apply (u v w : E) : rank u v w=inner ℝ v w • u := rfl

def L₂ (j χ r : ℝ) (J : E →L[ℝ] E) (v ell : E) : E →L[ℝ] E :=
  -J+(j*χ) • 1+(j*r) • rank v ell

def stableMatrix (j b r : ℝ) (X J : E →L[ℝ] E) (m : E) : E →L[ℝ] E :=
  1+(j*b) • (X*X)-X*J*X-(2*j*r) • (X*rank m m*X)

def Equations (j χ r p : ℝ) (A J : E →L[ℝ] E) (u m t ell w y : E) (c : ℝ) : Prop :=
  w=A (u+y-(j*c) • t) ∧ y=J w-(j*χ) • w-(j*c) • m ∧ c=r*inner ℝ ell w+p

end SKGap.ImplicitSystem

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ImplicitPerturb
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}
abbrev Euclid (n : ℕ) := EuclideanSpace ℝ (Fin n)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ImplicitFlip
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ImplicitSystem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def columnNorm (V : ι→E) : ℝ := ‖(WithLp.toLp 2 V : PiLp 2 (fun _ : ι=>E))‖

end SKGap.ImplicitSystem

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ImplicitUniformControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ImplicitSystem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

def uniformControlBudget (j δ B : ℝ) : ℝ :=
  let L:=B+|j| *B^2+2*|j| *B
  let W:=(1+B^2*(δ/2)⁻¹*L)*B^2*(B+2*|j| *B)
  let C:=B*W+B
  let Y:=(B+|j| *B^2)*W+|j| *C
  let F:=(1+B^2*(δ/2)⁻¹*L)*(B*(B+Y+|j| *C)+B^2*B+
        |j| *B^2*W*B+|j| *B^2*C*B+|j| *B^2*2*(B*W+B))
  let G:=B*W+B+B*F
  let H:=(B+|j| *B^2)*F+|j| *W*B+|j| *C*B+|j| *G
  W+C+Y+F+G+H

end SKGap.ImplicitSystem

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_FieldGibbs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff
variable {n : ℕ}

def fieldEnergy (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) : ℝ :=
  energy J x+∑i,h i*spin x i

def fieldPartition (J : Interaction n) (h : Fin n→ℝ) : ℝ := ∑x,Real.exp (fieldEnergy J h x)
def fieldGibbs (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) : ℝ :=
  Real.exp (fieldEnergy J h x)/fieldPartition J h

end SKGapCutoff

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_TapFieldE
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Real Matrix Set Filter Function
open scoped Topology
noncomputable section
open Set Function Real
open scoped Topology NNReal
namespace SKGap

def tapFieldE {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h : Field n) (y : EField n) : EField n :=
  WithLp.toLp 2 (tapField j J h (WithLp.ofLp y))

end SKGap

end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Posterior_BufferedPosteriorDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
open Primary Recipe
variable {n : ℕ}

def centeredSpinCovariance (P G : Observables n) : Fin n→ℝ :=
  fun i=>∑x,P x*(G x-∑y,P y*G y)*spin x i

end SKGapCutoff.Static

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Posterior_GaussianChannel
attribute [-instance] _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal
variable {n : ℕ}

def channelReference (n : ℕ) : Measure (Fin n→ℝ) := Measure.pi (fun _=>gaussianReal 0 1)
instance channelReference_probability (n : ℕ) : IsProbabilityMeasure (channelReference n) := by
  unfold channelReference
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def gaussianChannelLikelihood (T : ℝ) (x : Spin n) (z : Fin n→ℝ) : ℝ :=
  exp ((∑ i,sqrt T*spinValue (x i)*z i)-(n:ℝ)*T/2)

def gaussianChannelDensity (g : Disorder n) (T : ℝ) (z : Fin n→ℝ) : ℝ :=
  ∑ x,mass g 0 x*gaussianChannelLikelihood T x z

def gaussianChannelLaw (g : Disorder n) (T : ℝ) : Measure (Fin n→ℝ) :=
  (channelReference n).withDensity (fun z=>ENNReal.ofReal (gaussianChannelDensity g T z))

end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Posterior_QuenchedPosterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.FullMain
open MeasureTheory ProbabilityTheory Filter Set Real
open scoped Topology BigOperators
open SKGapCutoff SKGapCutoff.Recipe SKGapCutoff.Primary SKGapCutoff.Static
noncomputable section

def PosteriorCovarianceProperty {n : ℕ} (j Aroot ε c r₀ D : ℝ) (g : Disorder n) : Prop :=
  ∀h:Fin n→ℝ,¬rootBad j Aroot ε c r₀ (coupling g) h→∀f:Observables n,
    vectorNorm (centeredSpinCovariance (fieldGibbs (coupling g) h) f)≤
      D*sqrt ((∑x,fieldGibbs (coupling g) h x*(f x-∑y,fieldGibbs (coupling g) h y*f y)^2)+
          varianceEnergy (fieldGibbs (coupling g) h) f)

end
end SKGap.FullMain

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_TerminalMatrixTransfer
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators
variable {n : ℕ}

def heatBathGenerator (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) (x : Spin n) : ℝ :=
  ∑ i,(f x-conditionalExpectation g h i f x)

end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Posterior_StaticExperimentBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.FullMain
open MeasureTheory ProbabilityTheory Filter Real Set
open scoped Topology BigOperators ENNReal
open GaussianStep GaussianHistory ObservationBridge
noncomputable section
variable {n : ℕ}
local instance instMeasurableSpaceMatrixFinReal_solutions : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) := borel _

end
end SKGap.FullMain

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_RootGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.FullMain
open MeasureTheory ProbabilityTheory Filter Real Set ObservationBridge GaussianHistory
open scoped Topology BigOperators ENNReal
noncomputable section

def gridFailure (n : ℕ) (j A K ε c ρ T : ℝ) (g : Disorder n) : ℝ :=
  ∑k∈Finset.range (gridSteps n+1),fixedTimeFailure n j A K ε c ρ ((k:ℝ)*gridStep T n) g

end
end SKGap.FullMain

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_PairRationalBounds
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators

def pairRationalWeight (a b u x y : ℝ) : ℝ :=
  (1-u^2)^2*(1+u*x*y)/((1+u*a*b)*(1+u*a*y)^2*(1+u*b*x)^2)

end SKGap

end
end

section
noncomputable section
namespace SKGap
open Real

def pairK (a b u : ℝ) : ℝ :=
  (1-u^2)/((1+u*a*b)*(1-u^2*a^2)*(1-u^2*b^2))
def pairR (a b u : ℝ) : ℝ :=
  1+u*a*b+u^2*(a^2*b^2-a^2-b^2)-u^3*a*b

def pairCrossPolynomial (a b u p s r : ℝ) : ℝ :=
  pairK a b u*((-u+u^2*a*b)*p*s+u^2*b*(1-a^2)*r*p+
    u^2*a*(1-b^2)*r*s+pairR a b u*r^2)

end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_SpinLocalField
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators
variable {n : ℕ}

def localField (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) : ℝ :=
  h i+∑ k,coupling g i k*spinValue (x k)
def spinGradient (i : Fin n) (f : Spin n→ℝ) (x : Spin n) : ℝ :=
  (f (Function.update x i true)-f (Function.update x i false))/2

def realSpinEnergy (g : Disorder n) (h v : Fin n→ℝ) : ℝ :=
  (1/2)*(v ⬝ᵥ (Matrix.of (coupling g) *ᵥ v))+h ⬝ᵥ v

end SKGap

end
end

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators

def pairBaseMass (a b : ℝ) (x y : Bool) : ℝ :=
  (1+a*spinValue x)*(1+b*spinValue y)/4

def pairMean (a b : ℝ) (F : Bool→Bool→ℝ) : ℝ :=
  ∑ x,∑ y,pairBaseMass a b x y*F x y

end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_PairCrossIdentity
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators

def pairDensity (a b u : ℝ) (x y : Bool) : ℝ :=
  (1+u*spinValue x*spinValue y)/(1+u*a*b)
def pairInterMean (a b u : ℝ) (F : Bool→Bool→ℝ) : ℝ :=
  pairMean a b (fun x y=>pairDensity a b u x y*F x y)
def pairResidual (a u : ℝ) (x y : Bool) : ℝ :=
  (spinValue x-a)*(1-u*spinValue x*spinValue y)/(1+u*a*spinValue y)
def pairVariance (a u : ℝ) (y : Bool) : ℝ :=
  (1-a^2)*(1-u^2)/(1+u*a*spinValue y)^2

def pairGrad₁ (b p r : ℝ) (y : Bool) : ℝ := p+r*(spinValue y-b)
def pairGrad₂ (a s r : ℝ) (x : Bool) : ℝ := s+r*(spinValue x-a)

end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_PairBoltzmann
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators

def pairBoltzmannWeight (α γ J : ℝ) (x y : Bool) : ℝ :=
  exp (α*spinValue x+γ*spinValue y+J*spinValue x*spinValue y)
def pairBoltzmannMean (α γ J : ℝ) (F : Bool→Bool→ℝ) : ℝ :=
  (∑ x,∑ y,pairBoltzmannWeight α γ J x y*F x y)/(∑ x,∑ y,pairBoltzmannWeight α γ J x y)

end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_PairConditioning
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators
variable {n : ℕ}

def pairUpdate (i j : Fin n) (x : Spin n) (a b : Bool) : Spin n :=
  Function.update (Function.update x i a) j b

def pairConditionalMean (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n)
    (F : Spin n→ℝ) (x : Spin n) : ℝ :=
  (∑ a : Bool,∑ b : Bool,weight g h (pairUpdate i j x a b)*F (pairUpdate i j x a b))/
    (∑ a : Bool,∑ b : Bool,weight g h (pairUpdate i j x a b))

end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_PairGibbsBound
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators
variable {n : ℕ}

def siteVariance (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) : ℝ :=
  1-tanh (localField g h i x)^2

def weightedGradient (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (f : Spin n→ℝ) (x : Spin n) : ℝ :=
  siteVariance g h i x*spinGradient i f x

end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_SmallFieldCount
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators RealInnerProductSpace
variable {n : ℕ}

lemma conditionalExpectation_add (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f k : Spin n→ℝ) (x : Spin n) :
    conditionalExpectation g h i (f+k) x=conditionalExpectation g h i f x+conditionalExpectation g h i k x := by
  unfold conditionalExpectation
  simp only [Pi.add_apply]
  ring
lemma conditionalExpectation_smul (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (c : ℝ) (f : Spin n→ℝ) (x : Spin n) :
    conditionalExpectation g h i (c • f) x=c*conditionalExpectation g h i f x := by
  unfold conditionalExpectation
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

def heatBathLinear (g : Disorder n) (h : Fin n→ℝ) : (Spin n→ℝ) →ₗ[ℝ] (Spin n→ℝ) where
  toFun := heatBathGenerator g h
  map_add' f k := by
    funext x
    simp only [heatBathGenerator,conditionalExpectation_add,Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _;ring
  map_smul' c f := by
    funext x
    simp only [heatBathGenerator,conditionalExpectation_smul,Pi.smul_apply,smul_eq_mul,
      RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _;ring

def gibbsScale (g : Disorder n) (h : Fin n→ℝ) : (Spin n→ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Spin n) where
  toFun f := WithLp.toLp 2 (fun x=>sqrt (mass g h x)*f x)
  invFun v := fun x=>v x/sqrt (mass g h x)
  left_inv f := by
    funext x
    change sqrt (mass g h x)*f x/sqrt (mass g h x)=f x
    exact mul_div_cancel_left₀ (f x) (sqrt_pos.mpr (mass_pos g h x)).ne'
  right_inv v := by
    ext x
    exact mul_div_cancel₀ (v x) (sqrt_pos.mpr (mass_pos g h x)).ne'
  map_add' f k := by ext x;simp [mul_add]
  map_smul' c f := by ext x;simp [mul_left_comm]

end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_TerminalDeterministic
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

def terminalU (g : Disorder n) : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j=>tanh (coupling g i j))
def terminalQ (g : Disorder n) : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j=>tanh (coupling g i j)^2)

end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_TerminalProbability
attribute [-instance] _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set Matrix
open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

def observationField (T : ℝ) (x : Spin n) (z : Fin n→ℝ) : Fin n→ℝ :=
  fun i=>T*spinValue (x i)+sqrt T*z i

end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_TerminalRates
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Filter Real
open scoped Topology

def terminalEntryScale (n : ℕ) : ℝ := 1/sqrt (sqrt (n:ℝ))

end SKGap

end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set Filter
open scoped BigOperators Topology

variable (j α ε : ℝ) (n : ℕ)
def terminalRowBound : ℝ := 4*j*(log 2+1)

def terminalRawGood (g : MatrixCoordinates (Fin n)→ℝ) : Prop :=
  ‖matrixOperator (goeMatrix (j/(n:ℝ)) g)‖ ≤ 2*sqrt j+1 ∧
  (∀ i,|goeMatrix (j/(n:ℝ)) g i i| ≤ terminalEntryScale n) ∧
  (∀ i k,|coupling (goeDisorder (j/(n:ℝ)) g) i k| ≤ terminalEntryScale n) ∧
  (∀ i,∑ k,coupling (goeDisorder (j/(n:ℝ)) g) i k^2 ≤ terminalRowBound j) ∧
  (∀ S : Finset (Fin n),(S.card:ℝ) ≤ α*(n:ℝ) →
    principalOperatorNorm (goeMatrix (j/(n:ℝ)) g) S ≤ ε/3) ∧
  (∀ (i : Fin n) (S : Finset (Fin n)),(S.card:ℝ) ≤ α*(n:ℝ) →
    ∑ k∈S,coupling (goeDisorder (j/(n:ℝ)) g) i k^2 ≤ ε)

variable (l : ℝ)
def terminalRawTail : ℝ :=
  2*exp (-(n:ℝ)/(π^2*j))+
  2*(n:ℝ)*exp (-sqrt (n:ℝ)/(8*j))+
  2*(n:ℝ)^2*exp (-sqrt (n:ℝ)/(4*j))+
  (n:ℝ)*exp (-(n:ℝ))+
  2*exp (-(n:ℝ)*(ε^2/(36*π^2*j)-(l*α+log (1+exp (-l)))))+
  (n:ℝ)*exp (-(n:ℝ)*(ε/(4*j)-(l*α+log (1+exp (-l))+α*log 2)))

end SKGap

end
end

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

def terminalMatrixBound (j : ℝ) : ℝ := 2*sqrt j+2+terminalRowBound j

def terminalMatrixData (M α ε : ℝ) (g : Disorder n) : Prop :=
  (∀ i k,|coupling g i k| ≤ terminalEntryScale n) ∧
  ‖Matrix.of (coupling g)‖ ≤ M ∧ ‖terminalU g‖ ≤ M ∧ ‖terminalQ g‖ ≤ M ∧
  (∀ i,∑ k,tanh (coupling g i k)^4 ≤ M*terminalEntryScale n^2) ∧
  (∀ S : Finset (Fin n),(S.card:ℝ) ≤ α*(n:ℝ) →
    principalOperatorNorm (terminalU g) S ≤ ε ∧ principalOperatorNorm (terminalQ g) S ≤ ε)

end SKGap

end
end

end OAI
end


