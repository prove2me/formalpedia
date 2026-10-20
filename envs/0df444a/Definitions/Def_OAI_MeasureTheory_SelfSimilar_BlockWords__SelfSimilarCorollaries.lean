-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_BlockWords__SelfSimilarCorollaries
-- name    : OAI_MeasureTheory_SelfSimilar_BlockWords__SelfSimilarCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:42:11.076512+00:00
-- url     : https://prove2.me/theorems/654e7ed0-78a1-4c5d-a1f9-7263ed43dd67
-- title:
--   Block systems and word types
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   1. **Block system.** For $b>0$, the self-similar system indexed by words of length $b$, with ratio and offset of the composed map and weight the word weight:
--   $$
--   r_w=a_w,\quad b_w=\text{offset},\quad w_w=\prod_jw_{w_j}.
--   $$
--   It has the same self-similar measures, entropy rate at least $b$ times the original, and Lyapunov exponent $b\chi$.
--   2. **Flattening.** The equivalence between words of $n$ blocks of length $b$ and words of length $nb$.
--   3. **Word type.** The vector of letter counts of a block, with entries in $\{0,\dots,b\}$; blocks of the same type have the same slope.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/BlockWords.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/BlockWords.lean by skeleton subtraction
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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TypedLaw__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TailConvolution__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteVariance__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SuffixLaw__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordAverage__SelfSimilarCorollaries

namespace OAI

universe uι uα uβ uγ

namespace EntropyRateDimension.FiniteEntropy
open scoped BigOperators

end EntropyRateDimension.FiniteEntropy

namespace EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι]

noncomputable def blocks (S : System ι) {b : ℕ} (hb : 0 < b) : System (Fin b → ι) where
  ratio w := (S.completeMap w).1
  offset w := (S.completeMap w).2
  weight w := S.wordWeight w
  ratio_pos w := abs_pos.mpr (S.completeMap_slope_ne_zero w)
  ratio_lt_one w := S.completeMap_abs_lt_one hb w
  weight_pos w := S.wordWeight_pos w
  weight_sum := S.wordWeight_sum b

def flattenWordEquiv (n b : ℕ) : (Fin n → Fin b → ι) ≃ (Fin (n*b) → ι) :=
  (Equiv.curry (Fin n) (Fin b) ι).symm.trans (Equiv.piCongrLeft (fun _ => ι) finProdFinEquiv)

omit [Fintype ι] in
@[simp] theorem flattenWordEquiv_apply (n b : ℕ) (w : Fin n → Fin b → ι)
    (i : Fin n) (j : Fin b) : flattenWordEquiv n b w (finProdFinEquiv (i,j))=w i j := by
  simp [flattenWordEquiv]

noncomputable def wordType {b : ℕ} (w : Fin b → ι) : ι → Fin (b+1) := by
  classical
  exact fun i => ⟨(Finset.univ.filter (fun j => w j=i)).card,
    Nat.lt_succ_of_le ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Fintype.card_fin b))⟩

end EntropyRateDimension.System

end OAI


