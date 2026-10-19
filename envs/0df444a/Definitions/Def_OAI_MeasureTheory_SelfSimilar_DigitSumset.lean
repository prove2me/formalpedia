-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset
-- name    : OAI_MeasureTheory_SelfSimilar_DigitSumset
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T02:59:27.274878+00:00
-- url     : https://prove2.me/theorems/e7829c5f-db72-451b-8f0d-478330b7932f
-- title:
--   Letter counts and sumsets of digit choices
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   1. **Counts.** For a family $w$ of $k$ words indexed by positions, the number of $t<k$ with $w_t(j)=a$, for each position $j$ and letter $a$.
--   2. **Sumset.** For a finite set $S\subseteq\mathbb R$, the set of sums of $k$ elements of $S$:
--   $$
--   kS=\{x_1+\dots+x_k:\ x_t\in S\}.
--   $$
--   When every element of $S$ is a sum $\sum_jv_j(w_j)$ of digit contributions, $kS$ is controlled by the possible count vectors, which bounds its size polynomially in $k$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/DigitSumset.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/DigitSumset.lean by skeleton subtraction
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

namespace OAI

universe uα uβ

section

open scoped BigOperators
namespace EntropyRateDimension
namespace DigitSumset

noncomputable def counts {α : Type uα} {β : Type uβ} [Fintype α] [Fintype β] {k : ℕ}
    (w : Fin k → β → α) : β → α → Fin (k+1) := by
  classical
  exact fun j a => ⟨(Finset.univ.filter (fun t => w t j=a)).card,
    Nat.lt_succ_of_le ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Fintype.card_fin k))⟩

noncomputable def sumset (S : Finset ℝ) (k : ℕ) : Finset ℝ := by
  classical
  exact Finset.univ.image (fun w : Fin k → S => ∑ t, (w t : ℝ))

end DigitSumset
end EntropyRateDimension

end

end OAI


