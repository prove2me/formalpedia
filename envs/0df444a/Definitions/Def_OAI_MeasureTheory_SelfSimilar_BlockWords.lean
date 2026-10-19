-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_BlockWords
-- name    : OAI_MeasureTheory_SelfSimilar_BlockWords
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:44:17.239989+00:00
-- url     : https://prove2.me/theorems/b257ce55-a41b-4bff-8023-62a59b325e66
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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SuffixLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordAverage

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


