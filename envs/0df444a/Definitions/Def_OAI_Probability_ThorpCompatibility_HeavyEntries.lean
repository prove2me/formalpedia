-- Prove2me | Definitions.Def_OAI_Probability_ThorpCompatibility_HeavyEntries
-- name    : OAI_Probability_ThorpCompatibility_HeavyEntries
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:31:25.234236+00:00
-- url     : https://prove2.me/theorems/6f5cddca-e094-4927-bd2d-ff2147974dbc
-- title:
--   Predicted mass of the heavy values of a column entry
-- statement:
--   Let $Q$ be a law on the grid $\mathcal G_{A,D}$ of pairs $a=(r,c)$ (row permutations $r_i\in S_D$, column permutations $c_k\in S_A$). Let $H\in\mathbb{R}$, let $k\in[D]$ be a column and $i\in[A]$ a row index, and let $a=(r,c)\in\mathcal G_{A,D}$. Let $v=\mathrm{ch}_{k,i}(a)$ be the history that reveals $c_k(0),\dots,c_k(i-1)$, and let $\widehat Q_{k,i,v}$ be the conditional law under $Q$ of the entry $c_k(i)$ given this history. The heavy mass of the entry is
--   $$
--   \mathrm{hm}_{k,i}(a)=\widehat Q_{k,i,v}\Big(\Big\{w\in[A]:\ \widehat Q_{k,i,v}(w)>\frac{H}{A-i}\Big\}\Big),
--   $$
--   the predicted probability of the values that are not light at level $H$.
--
--   A value is heavy when its predicted probability exceeds $H$ times the uniform probability $1/(A-i)$ over the $A-i$ values still available to $c_k$. The heavy mass measures how much of the prediction is unavailable to the light-value cost. For $H>0$ it is controlled by the entropy deficit of the column: $(\log H-1)\sum_{i\in[A]}\mathbb{E}_Q[\mathrm{hm}_{k,i}]$ is at most the uniform deficit $\log A!-H(c_k)$ of the law of $c_k$.
--
--   **Formalization Note** The definition is `entryHeavyMass Q H k i a`. It is the `Law.prob` under `columnPrediction Q k i (colHistory k i a)` of the complement of `columnLight`. As elsewhere, $A-i$ is a natural-number subtraction that does not truncate because $i<A$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/HeavyEntries.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/HeavyEntries.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
noncomputable def entryHeavyMass {A D : ℕ} (Q : Law (Grid A D)) (H : ℝ)
    (k : Fin D) (i : Fin A) (a : Grid A D) : ℝ :=
  (columnPrediction Q k i (colHistory k i a)).prob
    (fun w => ¬columnLight Q H k i (colHistory k i a) w)

end ThorpCompatibility

end OAI


