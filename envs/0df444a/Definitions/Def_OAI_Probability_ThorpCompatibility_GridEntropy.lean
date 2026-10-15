-- Prove2me | Definitions.Def_OAI_Probability_ThorpCompatibility_GridEntropy
-- name    : OAI_Probability_ThorpCompatibility_GridEntropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:23:07.016971+00:00
-- url     : https://prove2.me/theorems/841abeba-2972-427e-b1f6-7da4e58c214f
-- title:
--   Exposure order on the grid: column histories, earlier columns and the past of an entry
-- statement:
--   Work on the grid $\mathcal G_{A,D}$ of pairs $a=(r,c)$, where $r_i\in S_D$ for each row $i\in[A]$ and $c_k\in S_A$ for each column $k\in[D]$; let $\star$ denote an unrevealed value. Fix a column $k\in[D]$, a row index $i\in[A]$, and an ordering of the columns given by a permutation $e\in S_D$, in which column $l$ precedes column $k$ when $e(l)<e(k)$.
--
--   1. *Column history.* The vector $\mathrm{ch}_{k,i}(a)\in([A]\cup\{\star\})^{[A]}$ reveals the first $i$ values of the column permutation $c_k$:
--   $$
--   \mathrm{ch}_{k,i}(a)_h=\begin{cases}c_k(h),&h<i,\\ \star,&h\ge i.\end{cases}
--   $$
--   2. *Earlier columns.* The vector $\mathrm{pc}_{e,k}(a)\in(S_A\cup\{\star\})^{[D]}$ reveals the permutations of the columns that strictly precede $k$ in the order $e$:
--   $$
--   \mathrm{pc}_{e,k}(a)_l=\begin{cases}c_l,& e(l)<e(k),\\ \star,&\text{otherwise.}\end{cases}
--   $$
--   3. *Past of an entry.* $\mathrm{past}_{e,k,i}(a)=\big((r,\mathrm{pc}_{e,k}(a)),\,\mathrm{ch}_{k,i}(a)\big)$. Suppose one reveals all row permutations first, then the columns one by one in the order $e$, and each column entry by entry. Then $\mathrm{past}_{e,k,i}(a)$ is the information available just before $c_k(i)$ is revealed.
--
--   These random variables organize the chain rule for the entropy of a law $Q$ on the grid. For every $e$ and $k$, the conditional entropies $H_Q\big(c_k(i)\mid\mathrm{past}_{e,k,i}\big)$ summed over $i\in[A]$ give $H_Q\big(c_k\mid r,\mathrm{pc}_{e,k}\big)$. The conditional entropies $H_Q\big(c_k(i)\mid\mathrm{ch}_{k,i}\big)$ summed over $i$ give the entropy of the marginal law of $c_k$.
--
--   **Formalization Note** The definitions are `colHistory k i`, which is the `Law.history` of the entries of `c k` at time `i`, `priorCols e k`, with values in `Fin D → Option (Equiv.Perm (Fin A))`, and `gridPast e k i`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/GridEntropy.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/GridEntropy.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpWeightedCompatibility mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Definitions.Def_OAI_Probability_ThorpCompatibility_RankLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Model
import Definitions.Def_OAI_Probability_ThorpCompatibility_EntropyChain

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

noncomputable def colHistory {A D : ℕ} (k : Fin D) (i : Fin A) (a : Grid A D) :=
  Law.history (fun h : Fin A => fun b : Grid A D => b.2 k h) i a

noncomputable def priorCols {A D : ℕ} (e : Equiv.Perm (Fin D)) (k : Fin D)
    (a : Grid A D) : Fin D → Option (Equiv.Perm (Fin A)) :=
  fun l => if e l < e k then some (a.2 l) else none

noncomputable def gridPast {A D : ℕ} (e : Equiv.Perm (Fin D)) (k : Fin D) (i : Fin A)
    (a : Grid A D) := ((a.1, priorCols e k a), colHistory k i a)

namespace Law
end Law

end ThorpCompatibility

namespace ThorpCompatibility
open Finset

end ThorpCompatibility

end OAI


