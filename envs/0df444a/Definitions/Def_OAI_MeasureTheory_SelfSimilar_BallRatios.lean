-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios
-- name    : OAI_MeasureTheory_SelfSimilar_BallRatios
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:07:41.591621+00:00
-- url     : https://prove2.me/theorems/db23675d-6468-4ddd-a105-0a779a55e561
-- title:
--   Maximal ball ratios between two measures
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   For measures $\mu,\nu$ on $\mathbb R$:
--
--   1. **Rational radii.** The rationals $q$ with $0<q\le1$.
--   2. **Maximal ratio.** $M(x)=\sup_q\mu(B(x,q))/\nu(B(x,q))$ over rational radii, and its log envelope $\max(0,\log M(x))$.
--   3. **Log ratio.** At radius $r$,
--   $$
--   \log\frac{\mu(B(x,r))}{\nu(B(x,r))} .
--   $$
--   These control the comparison of ball masses of $\mu$ and of a component of $\mu$ along the coding.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/BallRatios.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/BallRatios.lean by skeleton subtraction
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

namespace OAI

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace EntropyRateDimension
namespace BallRatios

abbrev Radius := {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) ≤ 1}

noncomputable def maximal (μ ν : Measure ℝ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ q : Radius, μ (closedBall x (q.val : ℝ)) / ν (closedBall x (q.val : ℝ))

noncomputable def logEnvelope (μ ν : Measure ℝ) (x : ℝ) : ℝ :=
  max 0 (Real.log (maximal μ ν x).toReal)

noncomputable def logRatio (μ ν : Measure ℝ) (x r : ℝ) : ℝ :=
  Real.log (μ (closedBall x r) / ν (closedBall x r)).toReal

end BallRatios
end EntropyRateDimension

end

end OAI


