-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw__SelfSimilarCorollaries
-- name    : OAI_MeasureTheory_SelfSimilar_ProductLaw__SelfSimilarCorollaries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T13:33:10.559327+00:00
-- url     : https://prove2.me/theorems/c0f75ec5-d7d6-48b5-abcc-d89d44781b67
-- title:
--   Product weights and coordinatewise conditioning
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   For coordinate laws $p_i$ on a finite set:
--
--   1. **Product weight.** $p(x)=\prod_ip_i(x_i)$.
--   2. **Cell masses.** For coordinate observables $g_i$ and a cell $c$, $m_i(c)=\sum_{a:\,g_i(a)=c_i}p_i(a)$.
--   3. **Conditional laws.** The law of coordinate $i$ conditioned on its cell,
--   $$
--   p_i(a\mid c)=\frac{p_i(a)\,[g_i(a)=c_i]}{m_i(c)} .
--   $$
--   Conditioning a product law on a product of cells gives the product of the conditional laws.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/ProductLaw.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/ProductLaw.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace ProductLaw

variable {ι : Type uι} {α : Type uα} [Fintype ι] [DecidableEq ι] [Fintype α]

noncomputable def weight (p : ι → α → ℝ) (x : ι → α) : ℝ := ∏ i, p i (x i)

variable {β : Type uβ} [DecidableEq β]

noncomputable def cellMass (p : ι → α → ℝ) (g : ι → α → β) (c : ι → β) (i : ι) : ℝ :=
  ∑ a, if g i a = c i then p i a else 0

noncomputable def conditional (p : ι → α → ℝ) (g : ι → α → β) (c : ι → β) (i : ι) (a : α) : ℝ :=
  (if g i a = c i then p i a else 0) / cellMass p g c i

end ProductLaw

end EntropyRateDimension
end

end OAI


