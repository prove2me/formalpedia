-- Prove2me | Definitions.Def_OAI_Probability_ThorpCompatibility_HeavyColumns
-- name    : OAI_Probability_ThorpCompatibility_HeavyColumns
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:38:06.717141+00:00
-- url     : https://prove2.me/theorems/0e780e2b-483d-4b96-bfe5-4710c658c5e7
-- title:
--   Values of a permutation not yet revealed
-- statement:
--   Let $A\in\mathbb{N}$, let $\sigma$ be a permutation of $[A]=\{0,\dots,A-1\}$, and let $i\in[A]$. The set of remaining values is
--   $$
--   \mathrm{rem}(\sigma,i)=\sigma\big(\{i,i+1,\dots,A-1\}\big)=\{\sigma(h):\ i\le h<A\}.
--   $$
--   It has exactly $A-i$ elements, and $w\in\mathrm{rem}(\sigma,i)$ holds if and only if $\sigma^{-1}(w)\ge i$.
--
--   Suppose a column permutation $c_k$ is exposed entry by entry. After $c_k(0),\dots,c_k(i-1)$ have been revealed, the next value $c_k(i)$ lies in $\mathrm{rem}(c_k,i)$. The conditional law of $c_k(i)$ given this history is therefore supported on a set of size $A-i$, which makes $H/(A-i)$ the natural threshold for heavy values.
--
--   **Formalization Note** The definition is `remainingValues σ i`, the image of the interval `Finset.Ici i` under `σ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/HeavyColumns.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/HeavyColumns.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_ThorpCompatibility_ListIncidence
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpMoments
import Definitions.Def_OAI_Probability_ThorpCompatibility_HeavyEntries
import Definitions.Def_OAI_Probability_ThorpCompatibility_ExposureEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_UniformSupport

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
noncomputable def remainingValues {A : ℕ} (σ : Equiv.Perm (Fin A)) (i : Fin A) : Finset (Fin A) :=
  (Finset.Ici i).map σ.toEmbedding

end ThorpCompatibility

end OAI


