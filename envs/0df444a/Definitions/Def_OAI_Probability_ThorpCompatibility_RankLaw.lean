-- Prove2me | Definitions.Def_OAI_Probability_ThorpCompatibility_RankLaw
-- name    : OAI_Probability_ThorpCompatibility_RankLaw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:17:18.503656+00:00
-- url     : https://prove2.me/theorems/b435cee5-139d-4baf-804e-1f797ab7300e
-- title:
--   Uniform random permutation conditioned on its value at one point
-- statement:
--   Let $D\ge 1$, write $[D]=\{0,1,\dots,D-1\}$, and let $S_D$ be the set of permutations of $[D]$. For $k,t\in[D]$, the rank law $R_{k,t}$ is the uniform law on $S_D$ conditioned on the event $\{e\in S_D: e(k)=t\}$:
--   $$
--   R_{k,t}(e)=\frac{\mathbf 1[e(k)=t]}{(D-1)!},\qquad e\in S_D .
--   $$
--   View a permutation $e$ as a random ordering of $[D]$ in which $e(k)$ is the rank of $k$. Then $R_{k,t}$ is the distribution of a uniformly random ordering, given that $k$ has rank $t$.
--
--   Under the uniform law, $e(k)$ is uniformly distributed on $[D]$. Averaging $R_{k,t}$ over $t\in[D]$ with weight $1/D$ therefore recovers the uniform law on $S_D$. This decomposition lets averages over a uniformly random column order be computed rank by rank, as in the estimates for the probability that a column comes no earlier than a given one.
--
--   **Formalization Note** The definition is `rankLaw k t = Law.uniform.restrict (fun e => e k = t)` on `Equiv.Perm (Fin D)`. The conditioning event has probability $1/D>0$ ($k\in[D]$ forces $D\ge 1$). The fallback of `Law.restrict` for null events is therefore never used, and the displayed formula holds.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/RankLaw.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/RankLaw.lean by skeleton subtraction
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

namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α : Type*} [Fintype α] [Nonempty α]

end Law
open Finset

noncomputable def rankLaw {D : ℕ} (k t : Fin D) : Law (Equiv.Perm (Fin D)) :=
  Law.uniform.restrict (fun e => e k = t)

end ThorpCompatibility

end OAI


