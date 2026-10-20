-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid__SelfSimilarCorollaries
-- name    : OAI_MeasureTheory_SelfSimilar_RandomGrid__SelfSimilarCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T13:24:07.521987+00:00
-- url     : https://prove2.me/theorems/6e7b485c-17f9-43ea-a17b-ef99af7c0853
-- title:
--   Hit indicators for random grid shifts
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   1. **Hit indicator.** For a point $c$ of the circle $\mathbb R/\mathbb Z$ and a radius $r$, the indicator of the arc of radius $r$ around $c$:
--   $$
--   \mathrm{hit}_{c,r}(u)=\begin{cases}1,&\mathrm{dist}(u,c)\le r,\\0,&\text{otherwise}.\end{cases}
--   $$
--   For a uniformly random grid shift $u$, it counts the probability that a grid boundary falls close to a given point, which controls boundary effects in grid entropies.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/RandomGrid.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/RandomGrid.lean by skeleton subtraction
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

namespace OAI

universe uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteDistribution

attribute [local instance] Classical.propDecidable

end FiniteDistribution
namespace RandomGrid

local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
  ⟨by simp⟩

noncomputable def hit (c : AddCircle (1 : ℝ)) (r : ℝ) (u : AddCircle (1 : ℝ)) : ℝ :=
  if dist u c ≤ r then 1 else 0

end RandomGrid

namespace MeasureEntropy

end MeasureEntropy

end EntropyRateDimension
end

end OAI


