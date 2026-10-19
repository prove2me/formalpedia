-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_UpperBound
-- name    : OAI_MeasureTheory_SelfSimilar_UpperBound
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:26:06.871276+00:00
-- url     : https://prove2.me/theorems/45d02d55-84a1-410e-9801-a062ff2872f0
-- title:
--   Word maps and the compressed system
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   1. **Word maps.** For a word $w$ of length $n$, the composed affine map $x\mapsto a_wx+b_w$, measurable, with $|a_w|<1$ for $n>0$.
--   2. **Compressed system.** For $n>0$, the self-similar system indexed by the distinct composed maps $g=(a,b)$ of length $n$:
--   $$
--   \text{ratio}=a,\qquad\text{offset}=b,\qquad\text{weight}=m_n(g),
--   $$
--   where $m_n(g)$ is the total weight of the words producing $g$. Exact overlaps are merged, so its entropy is the walk entropy $H_n$, which yields the upper bound $\alpha\le H_n/(n\chi)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/UpperBound.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/UpperBound.lean by skeleton subtraction
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

noncomputable def compressed (S : System ι) {n : ℕ} (hn : 0 < n) : System (S.mapSupport n) where
  ratio g := g.val.1
  offset g := g.val.2
  weight g := S.mapMass n g.val
  ratio_pos g := by
    obtain ⟨w,_,hw⟩ := Finset.mem_image.mp g.property
    rw [← hw]
    exact abs_pos.mpr (S.completeMap_slope_ne_zero w)
  ratio_lt_one g := by
    obtain ⟨w,_,hw⟩ := Finset.mem_image.mp g.property
    rw [← hw]
    exact S.completeMap_abs_lt_one hn w
  weight_pos g := S.mapMass_pos g.property
  weight_sum := by
    classical
    rw [← Finset.sum_subtype (S.mapSupport n) (fun _ => Iff.rfl)]
    exact S.mapMass_sum n

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


