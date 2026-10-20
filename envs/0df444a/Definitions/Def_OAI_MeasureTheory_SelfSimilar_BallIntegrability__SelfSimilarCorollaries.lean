-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability__SelfSimilarCorollaries
-- name    : OAI_MeasureTheory_SelfSimilar_BallIntegrability__SelfSimilarCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T13:56:55.878725+00:00
-- url     : https://prove2.me/theorems/dfedefba-dda1-4931-bece-64fe32c1cc91
-- title:
--   Components of a self-similar measure and ball information
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   1. **Components.** For each map $i$, the component $w_i\,(f_i)_*\mu$, a finite measure; a self-similar measure is the sum of its components.
--   2. **Ball information.** The information content of the ball of radius $r$ at $x$:
--   $$
--   I_\mu(x,r)=-\log\mu\bigl(B(x,r)\bigr).
--   $$
--   Its growth rate as $r\to0$ along the coding gives the local dimension.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/BallIntegrability.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/BallIntegrability.lean by skeleton subtraction
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
namespace EntropyRateDimension
open MeasureTheory Metric Set Filter
open scoped Topology BigOperators
namespace System
variable {ι : Type uι} [Fintype ι]

noncomputable def component (S : System ι) (μ : Measure ℝ) (i : ι) : Measure ℝ :=
  ENNReal.ofReal (S.weight i) • μ.map (S.affine i)

instance component_finite (S : System ι) (μ : Measure ℝ) [IsFiniteMeasure μ] (i : ι) :
    IsFiniteMeasure (S.component μ i) := by
  constructor
  simp only [component,Measure.smul_apply,smul_eq_mul]
  exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)

end System

namespace BallRatios
noncomputable def information (μ : Measure ℝ) (x r : ℝ) : ℝ :=
  -Real.log (μ.real (closedBall x r))

end BallRatios

namespace Coding
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

end Coding
end EntropyRateDimension

end

end OAI


