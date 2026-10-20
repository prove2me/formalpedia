-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_ErgodicAverages__SelfSimilarCorollaries
-- name    : OAI_MeasureTheory_SelfSimilar_ErgodicAverages__SelfSimilarCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:03:21.266984+00:00
-- url     : https://prove2.me/theorems/343495c6-e3de-43c7-87b0-e6d9dad2187c
-- title:
--   Maximal sums for the ergodic theorem
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   For a map $T$ and a function $f$:
--
--   1. **Maximal sums.** $M_0=0$ and
--   $$
--   M_{n+1}(x)=\max\bigl(0,\ f(x)+M_n(Tx)\bigr),
--   $$
--   which dominate the Birkhoff sums $\sum_{k<n}f(T^kx)$ and increase in $n$.
--   2. **Bounded sums.** The set of points whose Birkhoff sums are bounded above. These feed a finite form of Hopf's maximal inequality used for almost sure convergence of ergodic averages under the shift.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/ErgodicAverages.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/ErgodicAverages.lean by skeleton subtraction
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

namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace EntropyRateDimension
namespace ErgodicAux

variable {α : Type uα}

def maxSum (T : α → α) (f : α → ℝ) : ℕ → α → ℝ
  | 0, _ => 0
  | n+1, x => max 0 (f x + maxSum T f n (T x))

@[simp] theorem maxSum_zero (T : α → α) (f : α → ℝ) (x : α) :
    maxSum T f 0 x = 0 := rfl

@[simp] theorem maxSum_succ (T : α → α) (f : α → ℝ) (n : ℕ) (x : α) :
    maxSum T f (n+1) x = max 0 (f x + maxSum T f n (T x)) := rfl

variable [MeasurableSpace α] {μ : Measure α}

def boundedSums (T : α → α) (f : α → ℝ) : Set α :=
  {x | BddAbove (Set.range (fun n : ℕ => birkhoffSum T f n x))}

end ErgodicAux
end EntropyRateDimension

end

end OAI


