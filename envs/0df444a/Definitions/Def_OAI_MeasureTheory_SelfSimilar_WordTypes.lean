-- Prove2me | Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
-- name    : OAI_MeasureTheory_SelfSimilar_WordTypes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T02:57:20.451666+00:00
-- url     : https://prove2.me/theorems/22e4a185-d6d9-4d9a-95e4-de38effb6099
-- title:
--   Slopes of composed maps
-- statement:
--   These notions belong to a formal proof of the dimension formula for self-similar measures on the line. Let $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$, and let $\mu=\sum_iw_i\,(f_i)_*\mu$ be the self-similar probability measure. The formula states $\underline{\dim}_H\mu=\min(1,h/\chi)$. Here $h$ is the entropy rate of the random walk on composed affine maps, with exact overlaps allowed, $\chi=-\sum_iw_i\log_2|r_i|$ is the Lyapunov exponent, and $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over sets of positive measure. The proof identifies the dimension with an exponent of the symbolic coding, compares entropies of $\mu$ on dyadic grids, and rules out a strict gap by an entropy-increase argument for convolutions.
--
--   1. **Composed affine maps.** A word $w$ gives the composed map $f_{w_1}\circ\cdots\circ f_{w_n}$, stored as its pair (slope, offset). Its slope is
--   $$
--   \prod_jr_{w_j}\ne0 .
--   $$
--   The slope depends only on how many times each letter occurs, which is what makes word types (letter counts) useful for grouping words with equal contraction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/WordTypes.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/WordTypes.lean by skeleton subtraction
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

namespace OAI

universe uι

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

namespace System
variable {ι : Type uι} [Fintype ι]

theorem wordAffine_slope (S : System ι) (w : List ι) :
    (S.wordAffine w).1 = (w.map S.ratio).prod := by
  induction w with
  | nil => rfl
  | cons i w ih => simpa only [wordAffine,List.map_cons,List.prod_cons] using congrArg (S.ratio i * ·) ih

theorem completeMap_slope (S : System ι) {n : ℕ} (w : Fin n → ι) :
    (S.completeMap w).1 = ∏ j, S.ratio (w j) := by
  rw [completeMap,wordAffine_slope,List.map_ofFn,List.prod_ofFn]
  rfl

theorem completeMap_slope_ne_zero (S : System ι) {n : ℕ} (w : Fin n → ι) :
    (S.completeMap w).1 ≠ 0 := by
  rw [completeMap_slope]
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => abs_pos.mp (S.ratio_pos (w j)))

end System
end EntropyRateDimension

end OAI


