-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals
-- name    : OAI_MeasureTheory_SelfSimilar_CodingIntegrals
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:12:41.933004+00:00
-- url     : https://prove2.me/theorems/f3763a18-44b0-48dd-b253-233309f65d82
-- title:
--   Ball ratio observables along the coding
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   For a sequence $\omega$ with coding point $\pi(\omega)$ and first component $\mu_{\omega_0}=w_{\omega_0}(f_{\omega_0})_*\mu$:
--
--   1. **Envelope.** The log envelope of the maximal ratio between $\mu$ and $\mu_{\omega_0}$ at $\pi(\omega)$.
--   2. **Correction at depth $n$.** The log ratio of $\mu$ and $\mu_{\omega_0}$ on the ball of radius $|\mathrm{slope}_n(\omega)|$ around $\pi(\omega)$.
--   3. **Limit correction.** The logarithm of the Radon–Nikodym derivative
--   $$
--   \log\frac{d\mu}{d\mu_{\omega_0}}\bigl(\pi(\omega)\bigr),
--   $$
--   which is the almost sure limit of the corrections.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/CodingIntegrals.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/CodingIntegrals.lean by skeleton subtraction
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
namespace EntropyRateDimension.Coding
open MeasureTheory Metric Set Filter EntropyRateDimension.Bernoulli
open scoped Topology BigOperators ENNReal
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local instance instMeasurableSpace_oAI : MeasurableSpace ι := ⊤
local instance instMeasurableSingletonClass_oAI : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩

noncomputable def envelope (S : System ι) (ω : ℕ → ι) : ℝ :=
  BallRatios.logEnvelope (law S) (S.component (law S) (ω 0)) (point S ω)

noncomputable def corr (S : System ι) (n : ℕ) (ω : ℕ → ι) : ℝ :=
  BallRatios.logRatio (law S) (S.component (law S) (ω 0)) (point S ω) |slope S ω n|

noncomputable def corrLimit (S : System ι) (ω : ℕ → ι) : ℝ :=
  Real.log ((law S).rnDeriv (S.component (law S) (ω 0)) (point S ω)).toReal

end EntropyRateDimension.Coding

end

end OAI


