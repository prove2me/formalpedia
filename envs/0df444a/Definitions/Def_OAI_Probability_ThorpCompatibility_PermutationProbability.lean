-- Prove2me | Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability
-- name    : OAI_Probability_ThorpCompatibility_PermutationProbability
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:27:39.826469+00:00
-- url     : https://prove2.me/theorems/457b8d0c-a039-4184-924f-58964a0ae0ff
-- title:
--   Uniform probability of a property on a finite set
-- statement:
--   Let $\Omega$ be a finite set and let $P$ be a property of elements of $\Omega$. The uniform probability of $P$ is
--   $$
--   \Pr\nolimits_{\mathrm{unif}}[P]=\frac{\big|\{x\in\Omega: P(x)\}\big|}{|\Omega|},
--   $$
--   the probability that a uniformly random element of $\Omega$ satisfies $P$.
--
--   It is used with $\Omega$ a set of permutations or of families of permutations. One example is bounding the probability that a uniformly random permutation takes prescribed values on a given set. The uniform probability factorizes over product sets: for a uniformly random function $f$ on a finite index set, $\Pr[\,P_i(f(i))\text{ for all }i\,]=\prod_i\Pr[P_i]$.
--
--   **Formalization Note** The definition is `uniformProbability P`, computed with classical decidability of `P`. For empty $\Omega$ the formula reads $0/0$, which is $0$ under Lean's division convention.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/PermutationProbability.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/PermutationProbability.lean by skeleton subtraction
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

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
open Finset
noncomputable def uniformProbability {α : Type*} [Fintype α] (P : α → Prop) : ℝ := by
  classical
  exact (Finset.univ.filter P).card / (Fintype.card α : ℝ)

end ThorpCompatibility

end OAI


