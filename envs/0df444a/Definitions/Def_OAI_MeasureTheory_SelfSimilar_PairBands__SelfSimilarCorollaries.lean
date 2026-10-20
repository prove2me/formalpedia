-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairBands__SelfSimilarCorollaries
-- name    : OAI_MeasureTheory_SelfSimilar_PairBands__SelfSimilarCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:48:19.171393+00:00
-- url     : https://prove2.me/theorems/f8ba23ad-731c-45e0-ab62-b5cadcf4c994
-- title:
--   Pair budgets over a range of bands
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   1. **Pair budget.** For bands $a\le\ell\le B$ and a length $n$, the weighted sum over words of depth at most $A'n$ of the capacities of their typed offset laws in these bands:
--   $$
--   \mathrm{PB}_n=\sum_{|w|=n,\ \mathrm{depth}(w)\le A'n}w(w)\sum_{\ell=a}^{B}\mathrm{cap}\bigl(\nu_w,\ell\bigr).
--   $$
--   The capacity of a band is the largest total weight of a fair pairing of support points at distance about $2^{-\ell}$. A large budget gives many separated pairs, and each pair forces an entropy increase under convolution.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/PairBands.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/PairBands.lean by skeleton subtraction
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

namespace OAI

universe uα uβ

namespace EntropyRateDimension
open scoped BigOperators Topology
open Filter

namespace Typed
open FairPairs
variable {α : Type uα} {β : Type uβ} [Fintype α] [Nonempty α] [DecidableEq β]

noncomputable def pairBudget (S : System α) (tag : α → β) (A' : ℝ)
    (a B : ℤ) (n : ℕ) : ℝ :=
  ∑ w : Fin n → α, if S.wordDepth w ≤ A'*n then S.wordWeight w*
    ∑ ℓ ∈ Finset.Icc a B, capacity (law S tag w) ℓ else 0

end Typed
end EntropyRateDimension

end OAI


