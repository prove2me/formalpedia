-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling__SelfSimilarCorollaries
-- name    : OAI_MeasureTheory_SelfSimilar_GridCoupling__SelfSimilarCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T13:35:45.704779+00:00
-- url     : https://prove2.me/theorems/984add7f-b6fe-4f2a-abdd-9a9ceca6032c
-- title:
--   Grids indexed by points of the circle
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   1. **Uniform circle.** The circle $\mathbb R/\mathbb Z$ with its uniform probability measure.
--   2. **Shift representative.** The representative in $[0,1)$ of a point $u$ of the circle.
--   3. **Cell.** The grid cell of mesh $\delta$ shifted by $u$,
--   $$
--   \mathrm{cell}_{\delta,u}(x)=\Bigl\lfloor\frac x\delta+u\Bigr\rfloor .
--   $$
--   Randomizing $u$ uniformly couples grids of different scales and removes boundary effects on average.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/GridCoupling.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/GridCoupling.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace RandomGrid

attribute [local instance] unitCircleProbability
noncomputable def shift (u : AddCircle (1 : ℝ)) : ℝ := (AddCircle.equivIco 1 0 u).val

noncomputable def cell (δ : ℝ) (u : AddCircle (1 : ℝ)) (x : ℝ) : ℤ :=
  ⌊x / δ + shift u⌋

end RandomGrid

end EntropyRateDimension
end

end OAI


