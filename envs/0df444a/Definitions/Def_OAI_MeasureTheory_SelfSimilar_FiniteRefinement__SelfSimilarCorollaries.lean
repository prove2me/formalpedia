-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement__SelfSimilarCorollaries
-- name    : OAI_MeasureTheory_SelfSimilar_FiniteRefinement__SelfSimilarCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T13:37:28.747015+00:00
-- url     : https://prove2.me/theorems/415bc932-51fc-4243-851a-1837b4a0b236
-- title:
--   Cell means for refining partitions
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   1. **Cell mean.** For weights $p$, a function $v$ and an observable $g$, the conditional mean of $v$ on the cell $g=b$:
--   $$
--   \bar v(b)=\sum_a\frac{p(a)\,[g(a)=b]}{m_g(b)}\,v(a).
--   $$
--   These are used to compare the entropy of a refinement with that of the coarser partition through the variation of $v$ inside cells.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FiniteRefinement.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/FiniteRefinement.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteRefinement

open FiniteEntropy

variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

noncomputable def cellMean (p : α → ℝ) (v : α → ℝ) (g : α → β) (b : β) : ℝ :=
  ∑ a, ((if g a = b then p a else 0) / mass Finset.univ p g b) * v a

end FiniteRefinement

end EntropyRateDimension
end

end OAI


