-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_SuffixLaw
-- name    : OAI_MeasureTheory_SelfSimilar_SuffixLaw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:39:12.686989+00:00
-- url     : https://prove2.me/theorems/3d9815c1-21b4-4694-b530-09e3ddb8d3dc
-- title:
--   Suffix laws and windows along a word
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   For a list $W$ of letters:
--
--   1. **List versions.** The typed law, tail and scaled tail of $W$.
--   2. **Suffix law.** For $j\le|W|$, the scaled tail of the suffix $W_{\ge j}$, scaled by the slope of the prefix $W_{<j}$:
--   $$
--   \mathrm{suffixLaw}(W,j)=\bigl(x\mapsto a_{W_{<j}}x\bigr)_*\,\mathrm{tail}(W_{\ge j}).
--   $$
--   3. **Suffix window.** The grid-entropy window of the suffix law between scales $s$ and $Ns$.
--   4. **List depth.** $\sum_{a\in W}-\log_2|r_a|$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/SuffixLaw.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/SuffixLaw.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SelfSimilar mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ErgodicAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TriangularAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallLimits
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadiusGrowth
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadialLimit
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ExactDimension
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_UpperBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Conditioning
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TypedLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TailConvolution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteVariance

namespace OAI

universe uα uβ uγ

namespace EntropyRateDimension.Typed
open MeasureTheory MeasureEntropy FairPairs
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

noncomputable def listLaw (S : System α) (tag : α → β) (W : List α) : Law :=
  law S tag W.get
noncomputable def listTail (S : System α) (tag : α → β) (μ : Measure ℝ) (W : List α) : Measure ℝ :=
  tail S tag μ W.get

noncomputable def listScaledTail (S : System α) (tag : α → β) (μ : Measure ℝ)
    (a : ℝ) (W : List α) : Measure ℝ := (listTail S tag μ W).map (fun x => a*x)

instance listScaledTail_probability (S : System α) (tag : α → β) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (a : ℝ) (W : List α) : IsProbabilityMeasure (listScaledTail S tag μ a W) :=
  scaledTail_probability S tag μ a W.get

noncomputable def suffixLaw (S : System α) (tag : α → β) (μ : Measure ℝ) (W : List α) (j : ℕ) : Measure ℝ :=
  listScaledTail S tag μ (S.wordAffine (W.take j)).1 (W.drop j)

instance suffixLaw_probability (S : System α) (tag : α → β) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (W : List α) (j : ℕ) : IsProbabilityMeasure (suffixLaw S tag μ W j) :=
  listScaledTail_probability S tag μ _ _

noncomputable def suffixWindow (S : System α) (tag : α → β) (μ : Measure ℝ)
    (s : ℝ) (N : ℕ) (W : List α) (j : ℕ) : ℝ :=
  window (suffixLaw S tag μ W j) s (N*s)

end EntropyRateDimension.Typed

namespace EntropyRateDimension.System
open scoped BigOperators
variable {α : Type uα} [Fintype α]

noncomputable def listDepth (S : System α) (W : List α) : ℝ := (W.map S.letterDepth).sum

end EntropyRateDimension.System

end OAI


