-- Prove2me | Definitions.Def_OAI_Probability_ThorpCompatibility_ListIncidence
-- name    : OAI_Probability_ThorpCompatibility_ListIncidence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:28:11.43845+00:00
-- url     : https://prove2.me/theorems/db6032a1-9cfc-420c-8941-75a8b4e21343
-- title:
--   Families of permutations meeting prescribed cell lists
-- statement:
--   Let $I$ and $J$ be sets. Let $S$ assign to each cell $(j,k)\in J\times J$ a finite set $S(j,k)\subseteq I$ of rows, and let $r=(r_i)_{i\in I}$ be a family of permutations of $J$. The family $r$ meets the lists $S$ if
--   $$
--   \forall\,(j,k)\in J\times J,\ \ \forall\,i\in S(j,k):\qquad r_i(j)=k .
--   $$
--   In other words, every row listed at a cell $(j,k)$ really passes through that cell.
--
--   In the bound on the exponential moment of the clump count, $\exp\big(z\,\mathrm{clump}_H(r)\big)$ is expanded as a sum over list families $S$ of weights multiplied by the indicator that $r$ meets $S$. When $I$ and $J$ are finite, $J\neq\varnothing$, and the rows $r_i$ are independent and uniformly random, the probability of meeting $S$ is at most $(e/|J|)^{\sum_{b}|S(b)|}$.
--
--   **Formalization Note** The predicate is `MeetsLists S r` for `S : β × β → Finset α` and `r : α → Equiv.Perm β`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/ListIncidence.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/ListIncidence.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridExposure
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpCost
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability

-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
open Finset
def MeetsLists {α β : Type*} (S : β × β → Finset α) (r : α → Equiv.Perm β) : Prop :=
  ∀ j k i, i ∈ S (j, k) → r i j = k

end ThorpCompatibility

end OAI


