-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_UnweightedAttractor
-- name    : OAI_MeasureTheory_SelfSimilar_UnweightedAttractor
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:13:26.068302+00:00
-- url     : https://prove2.me/theorems/4dd0741e-2239-4f16-9b37-3febe56188be
-- title:
--   Attractors of unweighted similarity families
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   For a nonempty finite family of ratios $r_i$ with $0<|r_i|<1$ and offsets $t_i$:
--
--   1. **Uniform system.** The self-similar system with maps $x\mapsto r_ix+t_i$ and equal weights $1/|\iota|$. The choice of weights is only bookkeeping.
--   2. **Unweighted attractor.** The set of all coding limits $\pi(\omega)$ of this system,
--   $$
--   K=\Bigl\{\sum_{n\ge0}r_{\omega_0}\cdots r_{\omega_{n-1}}\,t_{\omega_n}:\omega\in\iota^{\mathbb N}\Bigr\},
--   $$
--   which does not depend on the weights.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/UnweightedAttractor.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/UnweightedAttractor.lean by skeleton subtraction
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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BlockWords__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_EntropyBudget__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RetainedLoss__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairBands__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowCount__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowGain__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Main__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_NoOverlaps
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Attractor
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_AttractorDimension

namespace OAI

universe uι

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension.Extensions

variable {ι : Type uι} [Fintype ι] [Nonempty ι]

/-- Every nonempty finite family of strict nonzero similarities admits positive
normalized weights. The uniform choice is bookkeeping, not a geometric hypothesis. -/
noncomputable def uniformSystem (r t : ι → ℝ)
    (hr0 : ∀ i, 0 < |r i|) (hr1 : ∀ i, |r i| < 1) : System ι where
  ratio := r
  offset := t
  weight := fun _ => 1 / (Fintype.card ι : ℝ)
  ratio_pos := hr0
  ratio_lt_one := hr1
  weight_pos := fun _ => one_div_pos.mpr (by exact_mod_cast Fintype.card_pos (α := ι))
  weight_sum := by
    have hn : (Fintype.card ι : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := ι)).ne'
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_div]
    exact mul_inv_cancel₀ hn

/-- Literal set of all coding limits for the unweighted similarity family. -/
def unweightedAttractor (r t : ι → ℝ)
    (hr0 : ∀ i, 0 < |r i|) (hr1 : ∀ i, |r i| < 1) : Set ℝ :=
  Set.range (Coding.point (uniformSystem r t hr0 hr1))

end EntropyRateDimension.Extensions

end OAI


