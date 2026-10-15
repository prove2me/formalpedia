-- Prove2me | Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpMoments
-- name    : OAI_Probability_ThorpCompatibility_ClumpMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:30:15.112306+00:00
-- url     : https://prove2.me/theorems/71969508-ba8a-4c93-9fa8-f73c050d53b6
-- title:
--   Clump weights for expanding the exponential moment of the clump count
-- statement:
--   Let $H,z\in\mathbb{R}$ and let $s$ be a finite set (of rows). The clump weight of $s$ is
--   $$
--   \phi_{H,z}(s)=\begin{cases}1,& s=\varnothing,\\ e^{z|s|},& s\ne\varnothing\ \text{and}\ |s|>H,\\ 0,&\text{otherwise.}\end{cases}
--   $$
--
--   Suppose $H\ge 0$ and consider a cell whose set of rows is $C$. Taking $s=C$ when $|C|>H$ and $s=\varnothing$ otherwise gives $\exp\big(z|C|\,\mathbf 1[|C|>H]\big)\le\sum_{s}\phi_{H,z}(s)\,\mathbf 1[s\subseteq C]$, where the sum runs over all subsets $s$ of the row set. Multiplying over all cells and expanding turns the exponential moment of the clump count into a sum over families of cell lists. Each family is weighted by a product of clump weights and by the probability that uniformly random rows meet the lists.
--
--   **Formalization Note** The definition is `clumpWeight H z s` for `s : Finset α`. The comparison of $|s|$ with $H$ is made in $\mathbb{R}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/ClumpMoments.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/ClumpMoments.lean by skeleton subtraction
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

-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
open Finset
noncomputable def clumpWeight {α : Type*} (H z : ℝ) (s : Finset α) : ℝ :=
  if s = ∅ then 1 else if H < s.card then Real.exp (z * s.card) else 0

end ThorpCompatibility

end OAI


