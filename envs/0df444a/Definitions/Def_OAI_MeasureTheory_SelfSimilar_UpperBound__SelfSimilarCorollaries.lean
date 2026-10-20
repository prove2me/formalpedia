-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_UpperBound__SelfSimilarCorollaries
-- name    : OAI_MeasureTheory_SelfSimilar_UpperBound__SelfSimilarCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:18:23.038925+00:00
-- url     : https://prove2.me/theorems/a2b3fa44-2461-4120-8c8b-ff69873b8e91
-- title:
--   Composed word maps and their contraction
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   For a word $w$ of length $n$ with composed map recorded as $(a_w,b_w)$, this module defines the word map
--   $$
--   f_w(x)=a_wx+b_w,
--   $$
--   which is measurable. For $n>0$ it is a strict contraction, $|a_w|=\prod_j|r_{w_j}|<1$. The images $f_w(K)$ of the attractor are the cylinders of depth $n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/UpperBound.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/UpperBound.lean by skeleton subtraction
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

namespace OAI

universe uι uM

namespace EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι]

def wordMap (S : System ι) {n : ℕ} (w : Fin n → ι) (x : ℝ) : ℝ :=
  (S.completeMap w).1*x+(S.completeMap w).2

theorem wordMap_measurable (S : System ι) {n : ℕ} (w : Fin n → ι) :
    Measurable (S.wordMap w) := by unfold wordMap; fun_prop

theorem completeMap_abs_lt_one (S : System ι) {n : ℕ} (hn : 0 < n) (w : Fin n → ι) :
    |(S.completeMap w).1| < 1 := by
  rw [completeMap_slope,Finset.abs_prod]
  calc
    _ < ∏ j : Fin n, (1 : ℝ) := Finset.prod_lt_prod_of_nonempty
      (fun j _ => S.ratio_pos (w j)) (fun j _ => S.ratio_lt_one (w j))
      ⟨⟨0,hn⟩,Finset.mem_univ _⟩
    _ = 1 := by simp

end EntropyRateDimension.System

namespace EntropyRateDimension.Coding
open MeasureTheory
open scoped BigOperators
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local instance instMeasurableSpace_oAI_5 : MeasurableSpace ι := ⊤
local instance instMeasurableSingletonClass_oAI_5 : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩

end EntropyRateDimension.Coding

namespace EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local instance instMeasurableSpace_1 : MeasurableSpace ι := ⊤
local instance instMeasurableSingletonClass_1 : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩

end EntropyRateDimension.System

end OAI


