-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallLimits
-- name    : OAI_MeasureTheory_SelfSimilar_BallLimits
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:17:46.595817+00:00
-- url     : https://prove2.me/theorems/1035fe9d-2894-412b-9964-9cff526a56c9
-- title:
--   Clipped ball ratios and the information rate
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   Along a coding sequence $\omega$:
--
--   1. **Clipped corrections.** The ball-ratio correction at depth $n$ and its limit, each truncated to $[0,\mathrm{envelope}]$.
--   2. **Weight and contraction observables.** $-\log w_{\omega_0}$ and $-\log|r_{\omega_0}|$.
--   3. **Prefix information.** The information $-\log\mu(B(\pi(\omega),|\mathrm{slope}_n(\omega)|))$ of the ball at the coding point with radius the contraction after $n$ steps.
--   4. **Information rate.** With the Bernoulli address measure,
--   $$
--   \mathrm{IR}=\int-\log w_{\omega_0}\,d\omega-\int\mathrm{clippedLimit}(\omega)\,d\omega .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/BallLimits.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/BallLimits.lean by skeleton subtraction
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

namespace OAI

universe uι

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
namespace EntropyRateDimension.Coding
open MeasureTheory Metric Set Filter
open EntropyRateDimension.Bernoulli EntropyRateDimension.ErgodicAux
open scoped Topology BigOperators
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local instance instMeasurableSpace_oAI_1 : MeasurableSpace ι := ⊤
local instance instMeasurableSingletonClass_oAI_1 : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩

noncomputable def clippedCorr (S : System ι) (n : ℕ) (ω : ℕ → ι) : ℝ :=
  max 0 (min (envelope S ω) (corr S n ω))
noncomputable def clippedLimit (S : System ι) (ω : ℕ → ι) : ℝ :=
  max 0 (min (envelope S ω) (corrLimit S ω))

noncomputable def weightObs (S : System ι) (ω : ℕ → ι) : ℝ := -Real.log (S.weight (ω 0))
noncomputable def contractionObs (S : System ι) (ω : ℕ → ι) : ℝ := -Real.log |S.ratio (ω 0)|

noncomputable def prefixInfo (S : System ι) (n : ℕ) (ω : ℕ → ι) : ℝ :=
  BallRatios.information (law S) (point S ω) |slope S ω n|

noncomputable def infoRate (S : System ι) : ℝ :=
  (∫ ω, weightObs S ω ∂addressMeasure S) - (∫ ω, clippedLimit S ω ∂addressMeasure S)

end EntropyRateDimension.Coding

end

end OAI


