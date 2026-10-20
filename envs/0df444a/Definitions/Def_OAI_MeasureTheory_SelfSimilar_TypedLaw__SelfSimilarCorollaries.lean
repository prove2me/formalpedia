-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_TypedLaw__SelfSimilarCorollaries
-- name    : OAI_MeasureTheory_SelfSimilar_TypedLaw__SelfSimilarCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:28:03.203468+00:00
-- url     : https://prove2.me/theorems/23a55f20-f19a-4f89-aa92-bde11eeb5a80
-- title:
--   Laws of words conditioned on their tags
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   Fix a tag map on letters. For a word $w$ of length $n$:
--
--   1. **Tag word.** The word of tags $(\mathrm{tag}(w_j))_j$.
--   2. **Typed probability.** The probability of a word $v$ with the same tags, under the posterior letter by letter:
--   $$
--   P(v\mid w)=\prod_jp\bigl(v_j\mid w_j\bigr).
--   $$
--   3. **Typed law.** The finite law of the offset of the composed map of $v$.
--   4. **Tail measure.** The mixture $\sum_vP(v\mid w)\,(\text{word map of }v)_*\mu$, a probability measure; it is the conditional law of $\mu$ given the tags of the first $n$ letters.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/TypedLaw.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/TypedLaw.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SelfSimilarCorollaries mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Model
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ErgodicAverages__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TriangularAverages__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallLimits__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadiusGrowth__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadialLimit__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ExactDimension__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_UpperBound__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Conditioning__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairGain__SelfSimilarCorollaries

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ uγ uM

namespace EntropyRateDimension.FiniteCondition
open scoped BigOperators ENNReal
open MeasureTheory

end EntropyRateDimension.FiniteCondition

namespace EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι]

end EntropyRateDimension.System

namespace EntropyRateDimension.Typed
open MeasureTheory FairPairs FiniteCondition
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

abbrev tagWord (tag : α → β) {n : ℕ} (w : Fin n → α) : Fin n → β := fun j => tag (w j)

noncomputable def prob (S : System α) (tag : α → β) {n : ℕ} (w v : Fin n → α) : ℝ :=
  ∏ j, posterior S.weight tag (w j) (v j)

theorem prob_nonneg (S : System α) (tag : α → β) {n : ℕ} (w v : Fin n → α) :
    0 ≤ prob S tag w v :=
  Finset.prod_nonneg (fun j _ => posterior_nonneg S.weight S.weight_pos tag (w j) (v j))

theorem prob_sum (S : System α) (tag : α → β) {n : ℕ} (w : Fin n → α) :
    ∑ v, prob S tag w v=1 := by
  classical
  simp only [prob,← Fintype.prod_sum,posterior_sum S.weight S.weight_pos,Finset.prod_const_one]

noncomputable def law (S : System α) (tag : α → β) {n : ℕ} (w : Fin n → α) : Law :=
  FiniteCondition.law S.wordWeight (fun v => S.wordWeight_pos v) (tagWord tag) w
    (fun v => (S.completeMap v).2)

noncomputable def tail (S : System α) (tag : α → β) (μ : Measure ℝ)
    {n : ℕ} (w : Fin n → α) : Measure ℝ :=
  ∑ v, ENNReal.ofReal (prob S tag w v) • μ.map (S.wordMap v)

instance tail_probability (S : System α) (tag : α → β) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {n : ℕ} (w : Fin n → α) : IsProbabilityMeasure (tail S tag μ w) := by
  have h (v : Fin n → α) : IsProbabilityMeasure (μ.map (S.wordMap v)) :=
    (Measure.isProbabilityMeasure_map_iff (S.wordMap_measurable v).aemeasurable).2 inferInstance
  let := h
  exact MeasureEntropy.mixture_probability (fun v => μ.map (S.wordMap v)) (prob S tag w)
    (prob_nonneg S tag w) (prob_sum S tag w)

end EntropyRateDimension.Typed

end OAI


