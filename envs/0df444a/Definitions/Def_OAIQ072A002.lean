-- Prove2me | Definitions.Def_OAIQ072A002
-- name    : OAIQ072A002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:19:15.878652+00:00
-- url     : https://prove2.me/theorems/2276c0b5-3c60-479e-aec1-fb8f6476851e
-- title:
--   Definitions bundle OAIQ072A002 of the split of OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 112 declarations of OpenAI's Lean: 103 definitions, 8 inductive types or structures and 1 theorem. The definitions and types are `OAI.SKGapCutoff.Recipe.FiniteLocalRecipeControl`, `OAI.SKGapCutoff.Recipe.FiniteRecipeControl`, `OAI.SKGapCutoff.Recipe.InitialArgs`, `OAI.SKGapCutoff.Recipe.LiteralBudget`, `OAI.SKGapCutoff.Recipe.LiteralEquations`, `OAI.SKGapCutoff.Recipe.LiteralInitialDiagnostics`, `OAI.SKGapCutoff.Recipe.LiteralStableAt`, `OAI.SKGapCutoff.Recipe.LocalOrdinaryInput`, `OAI.SKGapCutoff.Recipe.LocalRecipeResidualRule`, `OAI.SKGapCutoff.Recipe.MarkControl`, `OAI.SKGapCutoff.Recipe.MarkedControl`, `OAI.SKGapCutoff.Recipe.OrdinaryData.appendAuxiliary`, `OAI.SKGapCutoff.Recipe.OrdinaryData.appendFixed`, `OAI.SKGapCutoff.Recipe.OrdinaryData.appendPrimary`, `OAI.SKGapCutoff.Recipe.OrdinaryData.appendProduct`, `OAI.SKGapCutoff.Recipe.OrdinaryData.appendStein`, `OAI.SKGapCutoff.Recipe.OrdinaryData.argumentPullback`, `OAI.SKGapCutoff.Recipe.OrdinaryData.auxiliary`, `OAI.SKGapCutoff.Recipe.OrdinaryData.evaluate`, `OAI.SKGapCutoff.Recipe.OrdinaryData.fieldDerivativeError`, `OAI.SKGapCutoff.Recipe.OrdinaryData.implicitCoefficient`, `OAI.SKGapCutoff.Recipe.OrdinaryData.implicitFieldPrimitive`, `OAI.SKGapCutoff.Recipe.OrdinaryData.implicitPartial`, `OAI.SKGapCutoff.Recipe.OrdinaryData.implicitRetainedField`, `OAI.SKGapCutoff.Recipe.OrdinaryData.implicitRetainedSource`, `OAI.SKGapCutoff.Recipe.OrdinaryData.implicitSourcePrimitive`, `OAI.SKGapCutoff.Recipe.OrdinaryData.markedRecipe`, `OAI.SKGapCutoff.Recipe.OrdinaryData.nodeFieldError`, `OAI.SKGapCutoff.Recipe.OrdinaryData.nodeSourceError`, `OAI.SKGapCutoff.Recipe.OrdinaryData.normalizedPrimary`, `OAI.SKGapCutoff.Recipe.OrdinaryData.retainedField`, `OAI.SKGapCutoff.Recipe.OrdinaryData.retainedSource`, `OAI.SKGapCutoff.Recipe.OrdinaryData.retainedTree`, `OAI.SKGapCutoff.Recipe.OrdinaryData.source`, `OAI.SKGapCutoff.Recipe.OrdinaryData.sourceAtoms`, `OAI.SKGapCutoff.Recipe.OrdinaryData.sourceDerivativeError`, `OAI.SKGapCutoff.Recipe.OrdinaryData.sourcePartial`, `OAI.SKGapCutoff.Recipe.OrdinaryData.startedNodeFieldError`, `OAI.SKGapCutoff.Recipe.OrdinaryData.startedNodeSourceError`, `OAI.SKGapCutoff.Recipe.OrdinaryData.startedSmallTree` and 71 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `SKGap_Entropy_NormalizedWeightedMean`, `SKGap_Entropy_QuenchedWeightedMean`, `SKGap_Gaussian_GaussianRecipeEvent`, `SKGap_Gaussian_SteinRecipeRegularity`, `SKGap_Localization_BufferedSelectionDiagnostics`, `SKGap_Localization_CoefficientFlip`, `SKGap_Localization_ConstantRecipe`, `SKGap_Localization_FiniteRecipeControl`, `SKGap_Localization_FiniteStartedControlGeneral`, `SKGap_Localization_LiteralConstruction`, `SKGap_Localization_LiteralInitialRecipe`, `SKGap_Localization_LiteralInitialSystem`, `SKGap_Localization_LiteralLocalInput`, `SKGap_Localization_LiteralLocalWeak`, `SKGap_Localization_LiteralMargin`, `SKGap_Localization_LiteralRegularity`, `SKGap_Localization_LiteralSystemBridge`, `SKGap_Localization_LiteralWeak`, `SKGap_Localization_LocalCoefficient`, `SKGap_Localization_LocalRecipeClass`, `SKGap_Localization_LocalResidualInduction`, `SKGap_Localization_LocalUniformWeak`, `SKGap_Localization_LocalWeakBase`, `SKGap_Localization_MarkedDiagnostic`, `SKGap_Localization_PhiRegularity`, `SKGap_Localization_PrimaryLocalInput`, `SKGap_Localization_RecipeArgumentPullback`, `SKGap_Localization_RecipeError`, `SKGap_Localization_RecipeGraph`, `SKGap_Localization_RecipeMarked`, `SKGap_Localization_RefreshGenerator`, `SKGap_Localization_ResidualAdmissibility`, `SKGap_Localization_ResidualMultiplier`, `SKGap_Localization_ResidualRecipe2`, `SKGap_Localization_ResidualSelection`, `SKGap_Localization_SmoothSelection`, `SKGap_Localization_StartedFixed`, `SKGap_Localization_StartedMarked`, `SKGap_Localization_StartedPrimary`, `SKGap_Localization_SusceptibilityMiddle`, `SKGap_Localization_UniformResidual`, `SKGap_Localization_UniformSquareInduction`, `SKGap_Matrix_CorrectionTrace`, `SKGap_Matrix_LiteralTrace`, `SKGap_Matrix_NormalizedPrimaryRecipe`, `SKGap_Matrix_PrimaryWordControl`, `SKGap_Matrix_PrimaryWordEventBinding`, `SKGap_Matrix_PrimitiveTrace`, `SKGap_Matrix_RecipeNodeTrace`, `SKGap_Matrix_RecipeWordEvent`, `SKGap_Matrix_StartedMatrixEvent`, `SKGap_Matrix_StartedNodeTrace`, `SKGap_Matrix_Trace`, `SKGap_Stability_ImplicitNode`, `SKGap_Stability_ImplicitPerturb`, `SKGap_Stability_LiteralStableControl`, `SKGap_Stability_OrdinaryClosure`, `SKGap_Stability_OrdinaryRecipe`, `SKGap_Stability_OrdinaryWordEvent`, `SKGap_Terminal_FieldGibbs`, `SKGap_Terminal_GibbsExpectation`, `SKGap_Terminal_ResidualPairMoments`, `SKGap_Terminal_StableLiteralTerminal`.
--
--   **Imports.** It imports the bundles `OAIQ072A000` and `OAIQ072A001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.SKGapCutoff.Recipe.OrdinaryData.implicit_started_diagonal_local`, `OAI.SKGapCutoff.Recipe.OrdinaryData.ordinary_local_closure`, `OAI.SKGapCutoff.Recipe.buffered_posterior_covariance`, `OAI.SKGapCutoff.Recipe.buffered_root_direction_weak`, `OAI.SKGapCutoff.Recipe.buffered_root_source_weak`, `OAI.SKGapCutoff.Recipe.buffered_root_susceptibility_bound`, `OAI.SKGapCutoff.Recipe.disorder_closed_word_event`, `OAI.SKGapCutoff.Recipe.disorder_word_event`, `OAI.SKGapCutoff.Recipe.finite_started_control_seeds`, `OAI.SKGapCutoff.Recipe.gibbs_residual_selection_deficit`, `OAI.SKGapCutoff.Recipe.gibbs_residual_selection_tail`, `OAI.SKGapCutoff.Recipe.literal_complete_diagnostics`, `OAI.SKGapCutoff.Recipe.literal_finite_control`, `OAI.SKGapCutoff.Recipe.literal_implicit_construction`, `OAI.SKGapCutoff.Recipe.literal_local_weak_comparison_targets`, `OAI.SKGapCutoff.Recipe.primary_finite_control` and `OAI.SKGapCutoff.Recipe.uniform_stable_square_mean`; the proofs of `OAI.SKGapCutoff.Recipe.OrdinaryData.implicit_started_diagonal_local`, `OAI.SKGapCutoff.Recipe.OrdinaryData.ordinary_local_closure`, `OAI.SKGapCutoff.Recipe.buffered_posterior_covariance`, `OAI.SKGapCutoff.Recipe.buffered_root_direction_weak`, `OAI.SKGapCutoff.Recipe.buffered_root_source_weak`, `OAI.SKGapCutoff.Recipe.buffered_root_susceptibility_bound`, `OAI.SKGapCutoff.Recipe.disorder_closed_word_event`, `OAI.SKGapCutoff.Recipe.disorder_word_event`, `OAI.SKGapCutoff.Recipe.finite_started_control_seeds`, `OAI.SKGapCutoff.Recipe.gibbs_residual_selection_deficit`, `OAI.SKGapCutoff.Recipe.gibbs_residual_selection_tail`, `OAI.SKGapCutoff.Recipe.literal_complete_diagnostics`, `OAI.SKGapCutoff.Recipe.literal_finite_control`, `OAI.SKGapCutoff.Recipe.literal_implicit_construction`, `OAI.SKGapCutoff.Recipe.literal_local_weak_comparison_targets`, `OAI.SKGapCutoff.Recipe.primary_finite_control`, `OAI.SKGapCutoff.Recipe.uniform_stable_square_mean`, `OAI.SKGap.FullMain.quenched_posterior_covariance` and `OAI.SKGap.sk_main`.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ072A000
import Definitions.Def_OAIQ072A001

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_GibbsExpectation
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
namespace SKGapCutoff
open Filter Topology

def flipEquiv (n : ℕ) (i : Fin n) : Spin n ≃ Spin n where
  toFun x := flip x i
  invFun x := flip x i
  left_inv x := flip_flip x i
  right_inv x := flip_flip x i

end SKGapCutoff

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_CoefficientFlip
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set
namespace SKGapCutoff.Recipe
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def flipHalfDiff (i : Fin n) (P : Spin n→E) (x : Spin n) : E :=
  (spin x i/2) • (P x-P (flip x i))

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RefreshGenerator
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
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory ContinuousLinearMap
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
open Filter Set Metric
open scoped Topology RealInnerProductSpace
open scoped BigOperators
open ContinuousLinearMap
open scoped BigOperators
open ContinuousLinearMap
namespace SKGapCutoff

noncomputable def refreshInfluence {n : ℕ} (m : VectorFields n) (x : Spin n) : Interaction n :=
  fun i j => halfDiff i (fun y => m y j) x

end SKGapCutoff
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalCoefficient
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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

def taylorError (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (x : Spin n) (i k : Fin n) : ℝ :=
  derivativeMatrix (coefficient H θ F) x i k-
    F' i (localArgs H θ x i) (flipHalfDiff k (fun y=>localArgs H θ y i) x)

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

def sourceError (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (s : VectorFields n) (x : Spin n) : Interaction n :=
  derivativeMatrix (fun x i=>coefficient H θ F x i*s x i) x-
    Matrix.diagonal (coefficient H θ F x)*derivativeMatrix s x-
    ∑l,Matrix.diagonal (fun i=>s x i*localPartial H θ F' (.inl l) x i)*derivativeMatrix (H l) x

def primaryIncrement (H : ι→VectorFields n) (x : Spin n) : Interaction n :=
  fun i k=>∑l,|derivativeMatrix (H l) x i k|
def parameterIncrement (θ : κ→Spin n→ℝ) (x : Spin n) : Fin n→ℝ :=
  fun k=>∑α,|halfDiff k (θ α) x|

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PhiRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

def phiSelect (l : ι) (α : κ) : Args (ι:=ι) (κ:=κ)→L[ℝ]Triple :=
  (ContinuousLinearMap.proj (.inl l)).prod
    ((0 : Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ).prod (ContinuousLinearMap.proj (.inr α)))

end SKGapCutoff.Recipe

namespace SKGapCutoff.Recipe
open SKGap.Stein
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

def phiPairSelect (l m : ι) (α : κ) : Args (ι:=ι) (κ:=κ)→L[ℝ]Triple :=
  (ContinuousLinearMap.proj (.inl l)).prod
    ((ContinuousLinearMap.proj (.inl m)).prod (ContinuousLinearMap.proj (.inr α)))
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

namespace OrdinaryData
variable (D : OrdinaryData n ι κ σ)

def evaluate (D : OrdinaryData n ι κ σ) (a : ℕ) : VectorFields n × VectorFields n :=
  let prev := fun b : Fin a=>evaluate D b
  (D.sourceOf a (fun b=>(prev b).2),D.fieldOf a (fun b=>(prev b).1) (fun b=>(prev b).2))
termination_by a

def source (a : ℕ) : VectorFields n := (D.evaluate a).1
def auxiliary (a : ℕ) : VectorFields n := (D.evaluate a).2
def sourcePartial (a : ℕ) (l : ι) : VectorFields n := D.partialOf a l (fun b=>D.auxiliary b)

end OrdinaryData

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ResidualRecipe2
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
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
namespace OrdinaryData

def appendProduct (D : OrdinaryData n ι κ σ) (N : ℕ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ) : OrdinaryData n ι κ σ :=
  { D with
    seedFunction := fun a s i u=>if a=N+1 then F i u*D.seedFunction N s i u else D.seedFunction a s i u
    seedDerivative := fun a s i u=>if a=N+1 then
      F i u • D.seedDerivative N s i u+D.seedFunction N s i u • F' i u else D.seedDerivative a s i u
    auxFunction := fun a b i u=>if a=N+1 then
      if hb:b.val<N then F i u*D.auxFunction N ⟨b.val,hb⟩ i u else 0 else D.auxFunction a b i u
    auxDerivative := fun a b i u=>if a=N+1 then
      if hb:b.val<N then F i u • D.auxDerivative N ⟨b.val,hb⟩ i u+
        D.auxFunction N ⟨b.val,hb⟩ i u • F' i u else 0 else D.auxDerivative a b i u }

end OrdinaryData
end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary Matrix
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

def phiCoefficient (l m : ι) (α : κ) : Fin n→Args (ι:=ι) (κ:=κ)→ℝ :=
  fun _ u=>eval3 (KernelExpr.atom 0 0 false).eval (phiPairSelect l m α u)
def phiDerivative (l m : ι) (α : κ) : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ :=
  fun _ u=>((KernelExpr.atom 0 0 false).gradient (phiPairSelect l m α u)).comp (phiPairSelect l m α)

namespace OrdinaryData

def appendStein (D : OrdinaryData n ι κ σ) (N : ℕ) (l m : ι) (α : κ) : OrdinaryData n ι κ σ :=
  D.appendProduct N (phiCoefficient l m α) (phiDerivative l m α)

end OrdinaryData
end SKGapCutoff.Recipe

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

def appendAuxiliary (D : OrdinaryData n (Fin M) κ σ) (N : ℕ) : OrdinaryData n (Fin M) κ σ :=
  { D with
    seedFunction := fun a s i u=>if a=N+1 then 0 else D.seedFunction a s i u
    seedDerivative := fun a s i u=>if a=N+1 then 0 else D.seedDerivative a s i u
    auxFunction := fun a b i u=>if a=N+1 then if b.val=N then 1 else 0 else D.auxFunction a b i u
    auxDerivative := fun a b i u=>if a=N+1 then 0 else D.auxDerivative a b i u }

end OrdinaryData
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
namespace SKGapCutoff.Recipe.OrdinaryData
open SKGap.Noncrossing.Primary SKGap.Noncrossing.Diagram Primary Matrix
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

def retainedTree (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n)
    (a : ℕ) : SourceTree (Fin n→ℝ) :=
  SourceTree.branches ((Finset.univ.toList.map (fun l=>(D.sourcePartial a l x,T l)))++
    (Finset.univ.toList.map (fun b : Fin a=>(D.auxCoefficient a b x,retainedTree D T x b))))
termination_by a

def retainedSource (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) :=
  SourceTree.sourceMatrix D.j D.J (D.retainedTree T x a)
def retainedField (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) :=
  SourceTree.fieldMatrix D.j D.J (D.retainedTree T x a)

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_CorrectionTrace
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

def averageError (a : Spin n→ℝ) (U : VectorFields n) (x : Spin n) : Interaction n :=
  derivativeMatrix (fun x i=>a x*U x i) x-a x • derivativeMatrix U x

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RecipeError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.Noncrossing.Primary
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

namespace OrdinaryData
variable (D : OrdinaryData n ι κ σ)

def sourceAtoms (a : ℕ) (Y : Fin a→VectorFields n) (x : Spin n) : Interaction n :=
  (∑s,sourceError D.H D.θ (D.seedFunction a s) (D.seedDerivative a s) (fun _=>D.seed s) x)+
  ∑b,sourceError D.H D.θ (D.auxFunction a b) (D.auxDerivative a b) (Y b) x

def sourceDerivativeError (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) : Interaction n :=
  derivativeMatrix (D.source a) x-D.retainedSource T x a

def fieldDerivativeError (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) : Interaction n :=
  derivativeMatrix (D.auxiliary a) x-D.retainedField T x a

end OrdinaryData
end SKGapCutoff.Recipe

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

structure TraceControl (E : Interaction n) (C : ℝ) : Prop where
  nonneg : 0≤C
  bound : ∀P,|trace (P*E)|≤C*testSize P

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Matrix SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Diagram
variable {n : ℕ}

def wordBounded (A : ℝ) (w : OrdinaryWord n) : Prop :=
  ∀l∈w,match l with | .diag p=>∀i,|p i|≤A | .noise=>True

def WordTestBound (J : Interaction n) (A M : ℝ) (L : ℕ) : Prop :=
  ∀w:OrdinaryWord n,w.length≤L→wordBounded A w→testSize (matrixWord J w)≤M

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_RecipeNodeTrace
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

def nodeSourceError (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) : Interaction n :=
  D.sourceAtoms a (fun b=>D.auxiliary b) x+
  ∑l,Matrix.diagonal (D.sourcePartial a l x)*
    (derivativeMatrix (D.H l) x-SourceTree.fieldMatrix D.j D.J (T l))
def nodeFieldError (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) : Interaction n :=
  -(∑l,(D.j*siteMean (D.sourcePartial a l) x) •
    (derivativeMatrix (D.predecessor l) x-SourceTree.sourceMatrix D.j D.J (T l)))-
  D.j • ((∑l,averageError (siteMean (D.sourcePartial a l)) (D.predecessor l) x)+
    ∑b:Fin a,averageError (siteMean (D.auxCoefficient a b)) (D.source b) x)

end SKGapCutoff.Recipe.OrdinaryData

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
namespace SKGapCutoff.Recipe.OrdinaryData
open SKGap.Noncrossing.Primary SKGap.Noncrossing.Diagram MarkedPolynomial
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

def markedRecipe (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) : Pair n :=
  let entries : List (ι⊕Fin a) := Finset.univ.toList.map Sum.inl++Finset.univ.toList.map Sum.inr
  entries.foldr (fun e V=>match e with
    | .inl l => smallBranch D.j (D.sourcePartial a l x) (T l) V
    | .inr b => boundedBranch D.j (D.auxCoefficient a b x) (markedRecipe D T x b) V) zeroPair
termination_by a

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_OrdinaryClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.Noncrossing SKGap.Noncrossing.Primary MarkedPolynomial

variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

structure LocalOrdinaryInput (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ))
    (x : Spin n) (N : ℕ) (c : LocalConstants) : Prop where
  dimension : 0<n
  interaction : SKGap.opNorm D.J ≤ c.L
  primaryShape : ∀l,ShapeBound (derivativeMatrix (D.H l) x) c.P
  primaryFieldError : ∀l,‖derivativeMatrix (D.H l) x-SourceTree.fieldMatrix D.j D.J (T l)‖ ≤ c.E
  primarySourceError : ∀l,‖derivativeMatrix (D.predecessor l) x-SourceTree.sourceMatrix D.j D.J (T l)‖ ≤ c.E
  primaryValue : ∀l i,|D.predecessor l x i|≤1
  primaryDerivative : ∀l,SKGap.opNorm (derivativeMatrix (D.predecessor l) x) ≤ c.P
  seed : (∑s,vectorNorm (D.seed s)) ≤ c.S
  parameter : (∑α,‖derivativeVector (D.θ α) x‖) ≤ c.V
  seedRegular : ∀a≤N,∀s,SegmentRegular D.H D.θ (D.seedFunction a s) (D.seedDerivative a s) x c.C
  auxRegular : ∀a≤N,∀b,SegmentRegular D.H D.θ (D.auxFunction a b) (D.auxDerivative a b) x c.C
  seedValue : ∀a≤N,∀s i,|D.seedCoefficient a s x i| ≤ c.A
  auxValue : ∀a≤N,∀b i,|D.auxCoefficient a b x i| ≤ c.A

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_SteinRecipeRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

def steinCoefficientBudget (R : ℝ) : ℝ :=
  let f:=KernelExpr.atom 0 0 false
  f.mass*Real.exp (R/2)+f.dBudget R+f.ddBudget R
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_NormalizedPrimaryRecipe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary
variable {n M : ℕ} {κ σ : Type*} [Fintype κ] [DecidableEq κ]
namespace OrdinaryData

def normalizedPrimary (D : OrdinaryData n (Fin M) κ σ) (q : Fin M) :
    OrdinaryData n (Fin M) κ Unit where
  J:=D.J
  j:=D.j
  H:=D.H
  predecessor:=D.predecessor
  θ:=D.θ
  seed:=fun _ _=>(Real.sqrt (n:ℝ))⁻¹
  seedFunction:=fun _ _ _ u=>Real.tanh (u (.inl q))
  seedDerivative:=fun _ _ _ u=>(1-(Real.tanh (u (.inl q)))^2) • ContinuousLinearMap.proj (.inl q)
  auxFunction:=fun _ _ _ _=>0
  auxDerivative:=fun _ _ _ _=>0

end OrdinaryData

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ResidualMultiplier
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

def starSquared (P : Spin n→ℝ) (f : Observables n) : ℝ :=
  (∑ x,P x*(f x)^2)+varianceEnergy P f

def starNorm (P : Spin n→ℝ) (f : Observables n) : ℝ := Real.sqrt (starSquared P f)

end SKGapCutoff.Static

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Static
open Primary Recipe
universe u
variable {Ω : Type u} {n : Ω→ℕ}

def UniformMultiplier (θ : ∀a,Observables (n a)) : Prop :=
  ∃B L : ℝ,0≤B ∧ 0≤L ∧ (∀a x,|θ a x|≤B) ∧
    (∀a x,∑i,(halfDiff i (θ a) x)^2≤L^2)

def UniformWeak (P F : ∀a,Observables (n a)) : Prop :=
  ∃C : ℝ,0≤C ∧ ∀a G,|∑x,P a x*G x*F a x|≤C*starNorm (P a) G

end SKGapCutoff.Static

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_MarkedDiagnostic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.MarkedPolynomial
variable {n : ℕ}

def MarkControl (A : ℝ) (L : ℕ) (t : SmallMark n) : Prop :=
  ∀d:Fin n→ℝ,(∀i,|d i|≤1)→ wordBounded A (t.diagnostic d) ∧ (t.diagnostic d).length≤L

def MarkedControl (A : ℝ) (L : ℕ) (P : MarkedPolynomial n) : Prop := ∀t∈P,MarkControl A L t.2

def PairControl (A : ℝ) (L : ℕ) (P : Pair n) : Prop := MarkedControl A L P.1 ∧ MarkedControl A L P.2

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_PrimaryWordControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Noncrossing SKGap.Noncrossing.Primary
variable {n : ℕ}
def PolynomialControl (A : ℝ) (L : ℕ) (P : WordPolynomial (ι:=Fin n)) : Prop :=
  ∀t∈P,wordBounded A t.2 ∧ t.2.length≤L
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_RecipeWordEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.MarkedPolynomial
variable {n : ℕ}

def WordDiagramBound (J : Interaction n) (j A B : ℝ) (L : ℕ) : Prop :=
  ∀w:OrdinaryWord n,w.length≤L→wordBounded A w→
    SKGap.diagonalSeminorm (matrixWord J w-Matrix.diagonal (Diagram.prediction j w))≤B

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_FiniteRecipeControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Static SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.MarkedPolynomial
universe u
variable {Ω : Type u} {n : Ω→ℕ}

structure FiniteRecipeControl (j : ℝ) (J : ∀a,Interaction (n a)) (h : ∀a,Fin (n a)→ℝ)
    (M Nmax : ℕ) (A : ℝ) : Prop where
  small : ∀ {σ : Type} [Fintype σ] (D : ∀a,OrdinaryData (n a) (Fin M) (Fin M) σ)
    (N p : ℕ) (K : ℝ), FamilyRecipe j J h D N p K → N≤Nmax → K≤A →
    ∃C : ℝ,0≤C ∧ ∀a x,SmallBound ((D a).source N) x C ∧
      (∀q,SmallBound ((D a).sourcePartial N q) x C) ∧
      (∑i,|derivativeMatrix ((D a).source N) x i i|)≤C
  means : ∀ {σ : Type} [Fintype σ] (D : ∀a,OrdinaryData (n a) (Fin M) (Fin M) σ)
    (N p : ℕ) (K : ℝ), FamilyRecipe j J h D N p K → N≤Nmax → K≤A →
    ∀b:Fin N,UniformMultiplier (fun a=>siteMean ((D a).auxCoefficient N b))
  parameter : ∀q:Fin M,UniformMultiplier
    (fun a x=>j*(onsager j (J a) (h a) (q.val+1) x-onsager j (J a) (h a) q.val x))

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Static
variable {n M : ℕ}

def emptyRecipe (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (M : ℕ) :
    OrdinaryData n (Fin M) (Fin M) Unit where
  J:=J
  j:=j
  H:=fun q=>fld j J h q.val
  predecessor:=fun q=>mag j J h q.val
  θ:=fun q x=>j*(onsager j J h (q.val+1) x-onsager j J h q.val x)
  seed:=0
  seedFunction:=fun _ _ _ _=>0
  seedDerivative:=fun _ _ _ _=>0
  auxFunction:=fun _ _ _ _=>0
  auxDerivative:=fun _ _ _ _=>0

end SKGapCutoff.Recipe

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
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M Nmax : ℕ} {A j : ℝ}
variable {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {P : ∀a,Observables (n a)}

def RecipeResidualRule (j : ℝ) (J : ∀a,Interaction (n a)) (h : ∀a,Fin (n a)→ℝ)
    (P : ∀a,Observables (n a)) (M Nmax p : ℕ) (B : ℝ) : Prop :=
  ∀ {σ : Type} [Fintype σ] (D : ∀a,OrdinaryData (n a) (Fin M) (Fin M) σ) (N : ℕ),
    FamilyRecipe j J h D N p B → N+2*p≤Nmax →
    UniformWeak P (fun a x=>∑i,residual j (J a) (h a) p x i*(D a).source N x i)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_UniformResidual
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
variable {Ω : Type u} {n : Ω→ℕ} {M Nmax : ℕ} {A j : ℝ}
variable {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {P : ∀a,Observables (n a)}

def residualCoefficientBudget (j K : ℝ) (t p : ℕ) : ℝ :=
  K*(1+4*steinCoefficientBudget |j|)^(t-p)

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
open Primary Recipe
universe u
variable {Ω : Type u} {n : Ω→ℕ}

def UniformSquare (P F : ∀a,Observables (n a)) : Prop :=
  ∀B L:ℝ,0≤B→0≤L→∃C:ℝ,0≤C ∧ ∀a (f θ : Observables (n a)),
    (∀x,|θ x|≤B)→(∀x,∑i,(halfDiff i θ x)^2≤L^2)→
    |∑x,P a x*(f x)^2*θ x*F a x|≤C*starSquared (P a) f

end SKGapCutoff.Static

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_UniformSquareInduction
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
variable {Ω : Type u} {n : Ω→ℕ} {M Nmax : ℕ} {A j : ℝ}
variable {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {P : ∀a,Observables (n a)}

def RecipeSquareResidualRule (j : ℝ) (J : ∀a,Interaction (n a)) (h : ∀a,Fin (n a)→ℝ)
    (P : ∀a,Observables (n a)) (M Nmax p : ℕ) (B : ℝ) : Prop :=
  ∀ {σ : Type} [Fintype σ] (D : ∀a,OrdinaryData (n a) (Fin M) (Fin M) σ) (N : ℕ),
    FamilyRecipe j J h D N p B → N+2*p≤Nmax →
    UniformSquare P (fun a x=>∑i,residual j (J a) (h a) p x i*(D a).source N x i)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_OrdinaryWordEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary MeasureTheory ProbabilityTheory Real Set
variable {n : ℕ}

def WordSeminormBound (J : Interaction n) (j A C : ℝ) (L : ℕ) : Prop :=
  ∀(p : Bool) (w : OrdinaryWord n),w.length≤L→wordBounded A w→
    matrixWordSeminorm p (matrixWord J w-Matrix.diagonal (Diagram.prediction j w))≤C

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_PrimaryWordEventBinding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary MeasureTheory ProbabilityTheory Real Set
variable {n : ℕ}

def primaryEventBudget (j R C : ℝ) (M : ℕ) : ℝ :=
  ∑q:Fin M,(formalOpBound j R (q.val+1)+massBound j (q.val+1)*C)

def RecipeMatrixEvent (j R A B W C : ℝ) (M Nmax : ℕ) (J : Interaction n) : Prop :=
  SKGap.opNorm J≤R ∧
  (∀h x l,l<M→ShapeBound (formalField j J h x l) B) ∧
  WordTestBound J A W (2*Nmax+3) ∧ WordDiagramBound J j A C ((2*M+1)+2*Nmax+2)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianRecipeEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary MeasureTheory ProbabilityTheory Real Set

def ordinaryWordTail (j : ℝ) (L n : ℕ) : ENNReal :=
  2*((wordPatternSet L L).card*ENNReal.ofReal (3*exp (-(n:ℝ)))+
    ENNReal.ofReal (exp (-2*(n:ℝ)/(π^2*(sqrt (2*j))^2)))+
      (ENNReal.ofReal (2*exp (-(n:ℝ)/(π^2*j)))+
        ENNReal.ofReal (2*(n:ℝ)*exp (-1/(8*(j/n))))))

end SKGapCutoff.Recipe

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
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

def vectorPair (U V : VectorFields n) (x : Spin n) : ℝ := ∑i,U x i*V x i

def normalizedPair (U V : VectorFields n) (x : Spin n) : ℝ :=
  vectorPair U V x/Real.sqrt (n:ℝ)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_ResidualPairMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

def primaryPair (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) : Observables n :=
  normalizedPair (residual j J h k) (mag j J h (k+1))

def primaryPairBudget (j R B : ℝ) (k : ℕ) : ℝ :=
  (differentiationBound j R B k+differentiationBound j R B (k+1))+
  differentiationBound j R B (k+1)*2+
  2*(differentiationBound j R B k+differentiationBound j R B (k+1))*differentiationBound j R B (k+1)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ResidualSelection
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
variable {n : ℕ}

def residualEnergy (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) : ℝ :=
  (vectorNorm (residual j J h k x))^2/(n:ℝ)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SmoothSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

def residualStepCutoff (ρ j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) : ℝ :=
  residualScalarCutoff (residualEnergy j J h k x/ρ^2)

def residualCutoff (ρ j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) : ℝ :=
  residualStepCutoff ρ j J h k x*residualStepCutoff ρ j J h (k+1) x

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ConstantRecipe
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
variable {n M : ℕ}

def constantRecipe (j : ℝ) (J : Interaction n) (h e : Fin n→ℝ) (M : ℕ) :
    OrdinaryData n (Fin M) (Fin M) Unit where
  J:=J
  j:=j
  H:=fun q=>fld j J h q.val
  predecessor:=fun q=>mag j J h q.val
  θ:=fun q x=>j*(onsager j J h (q.val+1) x-onsager j J h q.val x)
  seed:=fun _=>e
  seedFunction:=fun _ _ _ _=>1
  seedDerivative:=fun _ _ _ _=>0
  auxFunction:=fun _ _ _ _=>0
  auxDerivative:=fun _ _ _ _=>0

universe u

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

def residualDerivativeBudget (j R B : ℝ) (k : ℕ) : ℝ :=
  differentiationBound j R B k+differentiationBound j R B (k+1)

universe u

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_NormalizedWeightedMean
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
variable {n : ℕ}

def squareMass (P : Observables n) (f : Observables n) (x : Spin n) : ℝ :=
  P x*(f x)^2/(∑y,P y*(f y)^2)

def squareMean (P : Observables n) (f : Observables n) (i : Fin n) : ℝ :=
  ∑x,squareMass P f x*spin x i

universe u

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static

structure StableRecipeInstance (j R B W C c r₀ : ℝ) (m : ℕ) where
  n : ℕ
  positive : 0<n
  J : Interaction n
  field : Fin n→ℝ
  symmetric : J.IsSymm
  diagonal : ∀i,J i i=0
  event : RecipeMatrixEvent j R (residualCoefficientBudget j 2 (2*m) 0) B W C (2*m+1) (2*(2*m)) J
  stability : ∀y,vectorNorm (SKGap.tapField j J field y) ≤ r₀*Real.sqrt (n:ℝ)→∀v,
    c*SKGap.vectorSqNorm v≤SKGap.quadraticForm (SKGap.fieldHessian j J y (SKGap.spinVariance y)) v

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_QuenchedWeightedMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology Matrix
open Filter MeasureTheory ProbabilityTheory Real
namespace SKGapCutoff.Recipe
open SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary Primary Static

def StableSquareMeanProperty {n : ℕ} (j c r₀ ρ C₀ A : ℝ) (J : Interaction n) : Prop :=
  ∀h:Fin n→ℝ,
    (∀y,vectorNorm (SKGap.tapField j J h y) ≤ r₀*Real.sqrt (n:ℝ)→∀v,
      c*SKGap.vectorSqNorm v≤SKGap.quadraticForm (SKGap.fieldHessian j J y (SKGap.spinVariance y)) v)→
    ∃r:Fin n→ℝ,SKGap.tapField j J h r=0 ∧ (∀y,SKGap.tapField j J h y=0→y=r) ∧
      ∀f:Observables n,0<(∑x,fieldGibbs J h x*(f x)^2)→
      vectorNorm (squareMean (fieldGibbs J h) f-SKGap.magnetization r)/Real.sqrt (n:ℝ)≤
        C₀*ρ+A/Real.sqrt (n:ℝ)*
          (1+varianceEnergy (fieldGibbs J h) f/(∑x,fieldGibbs J h x*(f x)^2))

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ImplicitNode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary
open SKGap.Noncrossing.Primary.Tensor.Series
variable {n : ℕ} {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n Unit κ σ)

def implicitPartial (y : VectorFields n) : VectorFields n := D.partialOf 1 () (fun _=>y)
def implicitCoefficient : VectorFields n := D.auxCoefficient 1 0

def implicitSourcePrimitive (t : SourceTree (Fin n→ℝ)) (y : VectorFields n) (x : Spin n) : Interaction n :=
  D.sourceAtoms 1 (fun _=>y) x+Matrix.diagonal (D.implicitPartial y x)*
    (derivativeMatrix (D.H ()) x-t.fieldMatrix D.j D.J)
def implicitFieldPrimitive (t : SourceTree (Fin n→ℝ)) (w y : VectorFields n) (x : Spin n) : Interaction n :=
  -(D.j*siteMean (D.implicitPartial y) x) •
    (derivativeMatrix (D.predecessor ()) x-t.sourceMatrix D.j D.J)-
  D.j • (averageError (siteMean (D.implicitPartial y)) (D.predecessor ()) x+
    averageError (siteMean D.implicitCoefficient) w x)

def implicitRetainedSource (t : SourceTree (Fin n→ℝ)) (y : VectorFields n) (x : Spin n) : Interaction n :=
  GradedWords.matrixValue D.j (D.implicitCoefficient x) D.J
    (GradedWords.implicitSource D.j (D.implicitCoefficient x) (D.implicitPartial y x) t)
def implicitRetainedField (t : SourceTree (Fin n→ℝ)) (y : VectorFields n) (x : Spin n) : Interaction n :=
  GradedWords.matrixValue D.j (D.implicitCoefficient x) D.J
    (GradedWords.implicitField D.j (D.implicitCoefficient x) (D.implicitPartial y x) t)

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralInitialRecipe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ}

abbrev InitialArgs := Args (ι:=Unit) (κ:=Bool)
def initialKernel (f : KernelExpr) (r : ℝ) (u : InitialArgs) : ℝ :=
  f.eval (u (.inl ())) r (u (.inr false))
def initialGradient (f : KernelExpr) (r : ℝ) (u : InitialArgs) : InitialArgs→L[ℝ]ℝ :=
  (f.gradient (phiSelect () false u+(0,(r,0)))).comp (phiSelect () false)
def phiExpr : KernelExpr := .atom 0 0 false

def literalInitial (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) : OrdinaryData n Unit Bool Bool where
  J:=J
  j:=j
  H:=fun _=>z
  predecessor:=fun _=>m
  θ:=fun b x=>if b then d*c x else a x
  seed:=fun b i=>if b then Real.tanh (r i)/d else e i
  seedFunction:=fun _ b i u=>if b then -j*u (.inr true)*initialKernel phiExpr (r i) u else initialKernel f (r i) u
  seedDerivative:=fun _ b i u=>if b then (-j) •
    (u (.inr true) • initialGradient phiExpr (r i) u+
      (initialKernel phiExpr (r i) u) • ContinuousLinearMap.proj (.inr true))
    else initialGradient f (r i) u
  auxFunction:=fun _ _ i u=>initialKernel phiExpr (r i) u
  auxDerivative:=fun _ _ i u=>initialGradient phiExpr (r i) u

end SKGapCutoff.Recipe

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

def phiDiagonal (z r : Fin n→ℝ) (a : ℝ) : Euclid n→L[ℝ]Euclid n :=
  Matrix.toEuclideanCLM (𝕜:=ℝ) (diagonal (fun i=>phi (z i) (r i) a))
def phiSqrt (z r : Fin n→ℝ) (a : ℝ) : Euclid n→L[ℝ]Euclid n :=
  Matrix.toEuclideanCLM (𝕜:=ℝ) (diagonal (fun i=>Real.sqrt (phi (z i) (r i) a)))

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralInitialSystem
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

def initialU (f : KernelExpr) (z : VectorFields n) (a : Spin n→ℝ) (r e : Fin n→ℝ) : VectorFields n :=
  fun x i=>f.eval (z x i) (r i) (a x)/phi (z x i) (r i) (a x)*e i

def initialP (f : KernelExpr) (z : VectorFields n) (a : Spin n→ℝ) (r e : Fin n→ℝ) : VectorFields n :=
  fun x i=>(f.dz.eval (z x i) (r i) (a x)-logSlope (z x i) (r i) (a x)*f.eval (z x i) (r i) (a x))*e i

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem
variable {n : ℕ}

def kernelSmallBudget (f : KernelExpr) (R T : ℝ) : ℝ :=
  f.mass*Real.exp (R/2)+3*((f.dBudget R+f.ddBudget R)*T)
def ratioSmallBudget (f : RatioExpr) (T : ℝ) : ℝ :=
  f.mass+3*((f.dBudget+f.ddBudget)*T)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralSystemBridge
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

def LiteralEquations (J : Interaction n) (j : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n) : Prop :=
  Equations j (siteMean (fun v i=>phi (z v i) (r i) (a v)) x) (n:ℝ)⁻¹
    (siteMean (initialP f z a r e) x) (phiDiagonal (z x) r (a x))
    (toEuclideanCLM (𝕜:=ℝ) J) (WithLp.toLp 2 (initialU f z a r e x))
    (WithLp.toLp 2 (m x)) (WithLp.toLp 2 (fun i=>Real.tanh (r i)))
    (WithLp.toLp 2 (fun i=>logSlope (z x i) (r i) (a x)))
    (WithLp.toLp 2 (w x)) (WithLp.toLp 2 (y x)) (c x)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_LiteralStableControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}

structure LiteralStableAt (J : Interaction n) (j : ℝ)
    (z m : VectorFields n) (a : Spin n→ℝ) (r : Fin n→ℝ)
    (R ρ δ : ℝ) (x : Spin n) : Prop where
  a_bound : |a x|≤R
  a_small : |a x|≤ρ
  z_near : vectorNorm (z x-r)≤ρ*Real.sqrt n
  m_near : vectorNorm (m x-(fun i=>Real.tanh (r i)))≤ρ*Real.sqrt n
  m_bound : ∀i,|m x i|≤1
  stable : ∀v,δ*‖v‖^2≤ inner ℝ v
    (stableMatrix j ((∑i,scalarVariance (z x i))/(n:ℝ)) (n:ℝ)⁻¹
      (phiSqrt (z x) r (a x)) (toEuclideanCLM (𝕜:=ℝ) J)
      (WithLp.toLp 2 (fun i=>Real.tanh (z x i))) v)

structure LiteralBudget (f : KernelExpr) (R T L B : ℝ) : Prop where
  nonneg : 0≤B
  two : 2≤B
  root : Real.sqrt (Real.exp (R/2))≤B
  square : Real.exp (R/2)≤B^2
  matrix : L≤B
  primary : T≤B
  source : ratioSmallBudget (.kernel f) T≤B
  scalar : ratioSmallBudget ((RatioExpr.kernel f).d .z) T*kernelSmallBudget phiExpr R T≤B
  phi_row : (phiExpr.dBudget R+phiExpr.ddBudget R)*T≤B
  slope_row : ((RatioExpr.kernel phiExpr.dz).dBudget+(RatioExpr.kernel phiExpr.dz).ddBudget)*T≤B

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralConstruction
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

def literalSizeBudget (j δ R L : ℝ) (f : KernelExpr) : ℝ :=
  let A:=Real.exp (R/2)
  let P:=A*((RatioExpr.kernel f).d .z).mass
  let W:=(1+A*(δ/2)⁻¹*(L+|j| *A+4*|j|))*A*(f.mass+2*|j| *P)
  W+(2*W+P)+((L+|j| *A)*W+|j| *(2*W+P))

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def initialRegularBudget (f : KernelExpr) (j R B : ℝ) : ℝ :=
  f.dBudget R+f.ddBudget R+(phiExpr.dBudget R+phiExpr.ddBudget R)+
    |j| *(B*(phiExpr.dBudget R+phiExpr.ddBudget R)+phiExpr.mass*Real.exp (R/2)+
      2*(phiExpr.dBudget R+phiExpr.ddBudget R))

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_LiteralTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ}

def initialPartialBudget (f : KernelExpr) (R T B : ℝ) : ℝ :=
  B*ratioSmallBudget (.kernel phiExpr.dz) T+
    ratioSmallBudget ((RatioExpr.kernel f).d .z) T*kernelSmallBudget phiExpr R T

end SKGapCutoff.Recipe

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

namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series
open SKGap.Noncrossing.ClosedMarked
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

def startedSmallTree (D : OrdinaryData n ι κ σ) (w y : VectorFields n)
    (T : ι→SourceTree (Fin n→ℝ)) (t₀ : SmallTree n) (x : Spin n) (a : ℕ) : SmallTree n :=
  match a with
  | 0 => t₀
  | a+1 => SmallTree.smallBranches
      (Finset.univ.toList.map (fun l=>(D.startedPartial w y (a+1) l x,ClosedTree.ofOrdinary (T l))))
      (SmallTree.boundedBranches
        (Finset.univ.toList.map (fun b : Fin (a+1)=>(D.auxCoefficient (a+1) b x,startedSmallTree D w y T t₀ x b))) .zero)
termination_by a

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_StartedNodeTrace
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
variable (D : OrdinaryData n ι κ σ) (w y : VectorFields n)

def startedNodeSourceError (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) : Interaction n :=
  D.sourceAtoms a (fun b=>D.startedAuxiliary w y b) x+
  ∑l,Matrix.diagonal (D.startedPartial w y a l x)*
    (derivativeMatrix (D.H l) x-SourceTree.fieldMatrix D.j D.J (T l))
def startedNodeFieldError (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) : Interaction n :=
  -(∑l,(D.j*siteMean (D.startedPartial w y a l) x) •
    (derivativeMatrix (D.predecessor l) x-SourceTree.sourceMatrix D.j D.J (T l)))-
  D.j • ((∑l,averageError (siteMean (D.startedPartial w y a l)) (D.predecessor l) x)+
    ∑b:Fin a,averageError (siteMean (D.auxCoefficient a b)) (D.startedSource w y b) x)

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_StartedMatrixEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary MeasureTheory ProbabilityTheory Real Set Filter
variable {n : ℕ}

def StartedMatrixEvent (j R A₀ A c B W C : ℝ) (M Nmax : ℕ) (J : Interaction n) : Prop :=
  SKGap.opNorm J≤R ∧ (∀h x l,l<M→ShapeBound (Primary.formalField j J h x l) B) ∧
  ∀a:Fin n→ℝ,(∀i,a i∈Icc 0 A₀)→
    c≤ComplexSpectral.lowerRayleigh (RealComplex.liftMatrix (stabilityMatrix a 1 ((j/n)*∑i,a i) J))→
    ClosedWordTestBound j a J A W (2*Nmax+5) ∧
    ClosedWordDiagramBound j a J A C (2*M+2*Nmax+4)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralMargin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ}

structure LiteralInitialDiagnostics (D : OrdinaryData n Unit Bool Bool)
    (w y : VectorFields n) (t : SKGap.Noncrossing.Primary.SourceTree (Fin n→ℝ))
    (x : Spin n) (B S F A : ℝ) : Prop where
  source : w x=D.sourceOf 1 (fun _=>y) x
  source_flip : ∀k,w (flip x k)=D.sourceOf 1 (fun _=>y) (flip x k)
  field : y x=D.fieldOf 1 (fun _=>w) (fun _=>y) x
  field_flip : ∀k,y (flip x k)=D.fieldOf 1 (fun _=>w) (fun _=>y) (flip x k)
  coefficient_nonneg : ∀i,0≤D.implicitCoefficient x i
  coefficient_bound : ∀i,|D.implicitCoefficient x i|≤A
  inverse_pos : (1-SKGap.pathDiagonal (D.implicitCoefficient x) 1*
    (D.J-(D.j*siteMean D.implicitCoefficient x) • 1)*SKGap.pathDiagonal (D.implicitCoefficient x) 1).PosDef
  source_bound : SmallBound w x B
  field_bound : SmallBound y x B
  partial_bound : SmallBound (D.implicitPartial y) x B
  source_trace : TraceControl (D.implicitSourcePrimitive t y x) S
  field_trace : TraceControl (D.implicitFieldPrimitive t w y x) F

end SKGapCutoff.Recipe

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

def edgeCut (E : Set (Spin n)) (U : VectorFields n) : VectorFields n :=
  fun x i=>if x∈E ∨ flip x i∈E then U x i else 0

end SKGapCutoff.Static

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_BufferedSelectionDiagnostics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ}

def literalCoefficientBudget (f : KernelExpr) (j R B : ℝ) : ℝ :=
  1+|initialRegularBudget f j R B|+f.mass*Real.exp (R/2)+
    (1+|j| *|B|)*phiExpr.mass*Real.exp (R/2)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RecipeArgumentPullback
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
variable {n : ℕ} {ι κ ι₀ κ₀ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Fintype ι₀] [DecidableEq ι₀] [Fintype κ₀] [DecidableEq κ₀]

def argumentSelect (l : ι₀→ι) (p : κ₀→κ) :
    Args (ι:=ι) (κ:=κ)→L[ℝ]Args (ι:=ι₀) (κ:=κ₀) :=
  ContinuousLinearMap.pi (fun q=>ContinuousLinearMap.proj (Sum.map l p q))

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ι₀] [DecidableEq ι₀] [Fintype κ₀] [DecidableEq κ₀] in
@[simp] lemma argumentSelect_apply (l : ι₀→ι) (p : κ₀→κ)
    (u : Args (ι:=ι) (κ:=κ)) (q : ι₀⊕κ₀) :
    argumentSelect l p u q=u (Sum.map l p q) := rfl

namespace OrdinaryData
variable {σ : Type*} [Fintype σ]

def argumentPullback (D : OrdinaryData n ι₀ κ₀ σ) (l : ι₀→ι) (p : κ₀→κ)
    (H U : ι→VectorFields n) (θ : κ→Spin n→ℝ) : OrdinaryData n ι κ σ where
  J:=D.J
  j:=D.j
  H:=H
  predecessor:=U
  θ:=θ
  seed:=D.seed
  seedFunction:=fun a b i u=>D.seedFunction a b i (argumentSelect l p u)
  seedDerivative:=fun a b i u=>(D.seedDerivative a b i (argumentSelect l p u)).comp (argumentSelect l p)
  auxFunction:=fun a b i u=>D.auxFunction a b i (argumentSelect l p u)
  auxDerivative:=fun a b i u=>(D.auxDerivative a b i (argumentSelect l p u)).comp (argumentSelect l p)

end OrdinaryData
end SKGapCutoff.Recipe

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

def LocalUniformWeak (E : ∀a,Set (Spin (n a))) (P F : ∀a,Observables (n a)) : Prop :=
  ∃C : ℝ,0≤C ∧ ∀a G,(∀x,x∉E a→G x=0)→|∑x,P a x*G x*F a x|≤C*starNorm (P a) G

end SKGapCutoff.Static

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_StartedPrimary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary
variable {n M : ℕ} {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]

def appendPrimary (D : OrdinaryData n (Fin M) κ σ) (N : ℕ) (q : Fin M) :
    OrdinaryData n (Fin M) κ (σ⊕Unit) where
  J:=D.J
  j:=D.j
  H:=D.H
  predecessor:=D.predecessor
  θ:=D.θ
  seed:=Sum.elim D.seed (fun _ _=>(Real.sqrt (n:ℝ))⁻¹)
  seedFunction:=fun a s i u=>if a=N+1 then
    Sum.elim (fun _=>0) (fun _=>Real.tanh (u (.inl q))) s
    else Sum.elim (fun s=>D.seedFunction a s i u) (fun _=>0) s
  seedDerivative:=fun a s i u=>if a=N+1 then
    Sum.elim (fun _=>0) (fun _=>(1-(Real.tanh (u (.inl q)))^2) • ContinuousLinearMap.proj (.inl q)) s
    else Sum.elim (fun s=>D.seedDerivative a s i u) (fun _=>0) s
  auxFunction:=fun a b i u=>if a=N+1 then 0 else D.auxFunction a b i u
  auxDerivative:=fun a b i u=>if a=N+1 then 0 else D.auxDerivative a b i u

end SKGapCutoff.Recipe.OrdinaryData

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
variable {Ω : Type u} {n : Ω→ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]

structure FiniteLocalRecipeControl (E : ∀a,Set (Spin (n a))) (j : ℝ)
    (J : ∀a,Interaction (n a)) (h : ∀a,Fin (n a)→ℝ) (Θ : ∀a,κ→Observables (n a))
    (w y : ∀a,VectorFields (n a)) (M Nmax : ℕ) (A : ℝ) : Prop where
  small : ∀ {σ : Type} [Fintype σ] (D : ∀a,OrdinaryData (n a) (Fin M) κ σ)
    (N p : ℕ) (K : ℝ), LocalFamilyRecipe E j J h Θ w y D N p K → N≤Nmax → K≤A →
    ∃C : ℝ,0≤C ∧ ∀a x,x∈flipNeighborhood (E a)→SmallBound ((D a).startedSource (w a) (y a) N) x C ∧
      (∀q,SmallBound ((D a).startedPartial (w a) (y a) N q) x C) ∧
      (∑i,|derivativeMatrix ((D a).startedSource (w a) (y a) N) x i i|)≤C
  means : ∀ {σ : Type} [Fintype σ] (D : ∀a,OrdinaryData (n a) (Fin M) κ σ)
    (N p : ℕ) (K : ℝ), LocalFamilyRecipe E j J h Θ w y D N p K → N≤Nmax → K≤A →
    ∀b:Fin N,LocalUniformMultiplier E (fun a=>siteMean ((D a).auxCoefficient N b))
  parameter : ∀q:Fin M,LocalUniformMultiplier E
    (fun a x=>j*(onsager j (J a) (h a) (q.val+1) x-onsager j (J a) (h a) q.val x))

end SKGapCutoff.Recipe
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_FiniteStartedControlGeneral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary SKGap.Stein Static

variable {n M : ℕ}

def literalFullParameters (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (a c : Spin n→ℝ) : Fin M⊕Bool→Spin n→ℝ :=
  Sum.elim (fun q x=>j*(onsager j J h (q.val+1) x-onsager j J h q.val x))
    (fun b x=>if b then Real.sqrt (n:ℝ)*c x else a x)

def literalFullData (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (l : Fin M) (f : KernelExpr) (a c : Spin n→ℝ) (r e : Fin n→ℝ) :
    OrdinaryData n (Fin M) (Fin M⊕Bool) Bool :=
  (literalInitial J j (Real.sqrt (n:ℝ)) f (fld j J h l.val) (mag j J h l.val) a c r e).argumentPullback (fun _:Unit=>l) Sum.inr (fun q=>fld j J h q.val)
      (fun q=>mag j J h q.val) (literalFullParameters j J h a c)

universe u

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralLocalInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary SKGap.Stein SKGap.Noncrossing.Primary
variable {n M : ℕ}

def literalEnvironmentConstants (j K B A Va Vc : ℝ) (M : ℕ)
    (hK : 0≤K) (hB : 0≤B) (hA : 1≤A) (hVa : 0≤Va) (hVc : 0≤Vc) : LocalConstants :=
  let P:=localPrimaryBudget j K B M
  ⟨A,A,P,K,P,(M:ℝ)*(|j| *(P+P))+Vc+Va,2,hA,by linarith,le_rfl,
    localPrimaryBudget_nonneg hK hB M,hK,localPrimaryBudget_nonneg hK hB M,
    by positivity [localPrimaryBudget_nonneg (j:=j) hK hB M],by norm_num⟩

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalResidualInduction
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
variable {Ω : Type u} {n : Ω→ℕ} {M Nmax : ℕ} {A j : ℝ}
variable {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {P : ∀a,Observables (n a)}
variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {Z : ∀a,Set (Spin (n a))} {Θ : ∀a,κ→Observables (n a)}
variable {w y : ∀a,VectorFields (n a)}

def LocalRecipeResidualRule (Z : ∀a,Set (Spin (n a))) (Θ : ∀a,κ→Observables (n a))
    (w y : ∀a,VectorFields (n a)) (j : ℝ) (J : ∀a,Interaction (n a)) (h : ∀a,Fin (n a)→ℝ)
    (P : ∀a,Observables (n a)) (M Nmax p : ℕ) (B : ℝ) : Prop :=
  ∀ {σ : Type} [Fintype σ] (D : ∀a,OrdinaryData (n a) (Fin M) κ σ) (N : ℕ),
    LocalFamilyRecipe Z j J h Θ w y D N p B → N+2*p≤Nmax →
    LocalUniformWeak Z P (fun a x=>∑i,residual j (J a) (h a) p x i*(D a).startedSource (w a) (y a) N x i)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralLocalWeak
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Static SKGap.Stein SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series SKGap.Noncrossing.ClosedMarked
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M : ℕ}

def literalResidualBudget (j : ℝ) (f : KernelExpr) (R B : ℝ) (p : ℕ) : ℝ :=
  residualCoefficientBudget j (2+|literalCoefficientBudget f j R B|) p 0

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_StartedFixed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary
variable {n M : ℕ} {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]

def appendFixed (D : OrdinaryData n (Fin M) κ σ) (N : ℕ) (v : Fin n→ℝ) :
    OrdinaryData n (Fin M) κ (σ⊕Unit) where
  J:=D.J
  j:=D.j
  H:=D.H
  predecessor:=D.predecessor
  θ:=D.θ
  seed:=Sum.elim D.seed (fun _=>v)
  seedFunction:=fun a s i u=>if a=N+1 then
    Sum.elim (fun _=>0) (fun _=>1) s
    else Sum.elim (fun s=>D.seedFunction a s i u) (fun _=>0) s
  seedDerivative:=fun a s i u=>if a=N+1 then
    Sum.elim (fun _=>0) (fun _=>0) s
    else Sum.elim (fun s=>D.seedDerivative a s i u) (fun _=>0) s
  auxFunction:=fun a b i u=>if a=N+1 then 0 else D.auxFunction a b i u
  auxDerivative:=fun a b i u=>if a=N+1 then 0 else D.auxDerivative a b i u

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_StableLiteralTerminal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Static SKGap.Stein
universe u
variable {Ω : Type u} {n : Ω→ℕ}

 def literalTerminal {n : ℕ} (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ)
    (w : VectorFields n) (c : Observables n) : Observables n := fun x=>
    (∑i,(fld j J h (k+1) x i-h i-J.mulVec (mag j J h (k+2) x) i+
      j*onsager j J h (k+1) x*mag j J h (k+2) x i)*w x i)-
      j*(onsager j J h (k+2) x-onsager j J h (k+1) x)*(n:ℝ)*c x

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralWeak
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static SKGap.Stein
universe u
variable {n : ℕ}

def literalSourceBracket (j : ℝ) (J : Interaction n) (h r e : Fin n→ℝ)
    (k : ℕ) (f : KernelExpr) : Observables n := fun x=>
  ∑i,((fld j J h (k+1) x i-r i-j*(1-onsager j J h (k+1) x-SKGap.overlap r)*
    Real.tanh (fld j J h (k+1) x i))*f.eval (fld j J h (k+1) x i) (r i)
      (j*(1-onsager j J h (k+1) x-SKGap.overlap r))*e i-
    j*(1-onsager j J h (k+1) x-SKGap.overlap r)*f.dz.eval (fld j J h (k+1) x i) (r i)
      (j*(1-onsager j J h (k+1) x-SKGap.overlap r))*e i)

def literalMiddle (j : ℝ) (J : Interaction n) (h r : Fin n→ℝ)
    (k : ℕ) (w : VectorFields n) : Observables n := fun x=>
  j*(1-SKGap.overlap r-siteMean (fun v i=>phi (fld j J h (k+1) v i) (r i)
    (j*(1-onsager j J h (k+1) v-SKGap.overlap r))) x)*
    (∑i,(Real.tanh (fld j J h (k+1) x i)-Real.tanh (r i))*w x i)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SusceptibilityMiddle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ}

def literalSusceptibility (z : VectorFields n) (a : Spin n→ℝ) (r : Fin n→ℝ) : Spin n→ℝ :=
  fun x=>Real.sqrt (n:ℝ)*(siteMean (fun v i=>phi (z v i) (r i) (a v)) x-(1-SKGap.overlap r))

end SKGapCutoff.Recipe

end
end

end OAI
end


