-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowGain
-- name    : OAI_MeasureTheory_SelfSimilar_WindowGain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:54:56.463185+00:00
-- url     : https://prove2.me/theorems/b235c207-1e30-48df-bb6e-0d97a91d381f
-- title:
--   Capacities and window drops at retained positions
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   Let $\sigma(j)$ be the depth of the first $j$ letters of a list $W$. At a retained position $j$, and $0$ otherwise:
--
--   1. **Retained capacity.** The capacity, at the relative band $L-\lceil\sigma(j)\rceil$, of the typed offset law of the segment of $n$ letters starting at $j$.
--   2. **Retained drop.** The decrease of the suffix window from position $j$ to position $j+n$, at scale $s=2^{-L}/M$ and ratio $M^2$:
--   $$
--   \mathrm{drop}_j=\mathrm{SW}_{s,M^2}(W,j)-\mathrm{SW}_{s,M^2}(W,j+n).
--   $$
--   The window gain lemma bounds the capacity below by a multiple of the drop, so the drops telescope along $W$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/WindowGain.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/WindowGain.lean by skeleton subtraction
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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BlockWords
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_EntropyBudget
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RetainedLoss
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairBands
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowCount

namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open MeasureTheory MeasureEntropy FairPairs Windows
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

noncomputable def retainedCapacity (S : System α) (tag : α → β)
    (A' : ℝ) (n : ℕ) (a B L : ℤ) (W : List α) (j : ℕ) : ℝ :=
  if Retained (fun j => S.listDepth (W.take j)) A' n a B L j then
    capacity (listLaw S tag ((W.drop j).take n)) (L-⌈S.listDepth (W.take j)⌉) else 0

noncomputable def retainedDrop (S : System α) (tag : α → β) (μ : Measure ℝ)
    (M : ℕ) (A' : ℝ) (n : ℕ) (a B L : ℤ) (W : List α) (j : ℕ) : ℝ :=
  if Retained (fun j => S.listDepth (W.take j)) A' n a B L j then
    suffixWindow S tag μ ((2 : ℝ)^(-L)/M) (M*M) W j-
      suffixWindow S tag μ ((2 : ℝ)^(-L)/M) (M*M) W (j+n) else 0

end EntropyRateDimension.Typed

end OAI


