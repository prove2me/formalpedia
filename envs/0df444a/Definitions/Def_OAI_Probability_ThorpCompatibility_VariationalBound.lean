-- Prove2me | Definitions.Def_OAI_Probability_ThorpCompatibility_VariationalBound
-- name    : OAI_Probability_ThorpCompatibility_VariationalBound
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:41:22.1827+00:00
-- url     : https://prove2.me/theorems/336ef906-590c-4816-b225-4f466fafb9d9
-- title:
--   Compatibility weight of a row–column permutation grid
-- statement:
--   Fix natural numbers $A$ and $D$, write $[A]=\{0,1,\dots,A-1\}$ and $[D]=\{0,1,\dots,D-1\}$, and let $S_m$ denote the group of permutations of $[m]$. A *grid* is a pair $(r,c)$ consisting of a row family $r=(r_i)_{i\in[A]}$ with $r_i\in S_D$ and a column family $c=(c_k)_{k\in[D]}$ with $c_k\in S_A$. The grid is *compatible* if for every $j\in[D]$ the map $i\mapsto c_{r_i(j)}(i)$ is injective on $[A]$ (hence a permutation of $[A]$).
--
--   Given real weight families $w=(w_i)_{i\in[A]}$ with $w_i:S_D\to\mathbb{R}$ and $v=(v_k)_{k\in[D]}$ with $v_k:S_A\to\mathbb{R}$, the *compatibility weight* of a grid $(r,c)$ is the product weight of its rows and columns, restricted to compatible grids:
--
--   $$
--   \mathrm{wt}_{w,v}(r,c)=\begin{cases}\displaystyle\prod_{i\in[A]}w_i(r_i)\,\prod_{k\in[D]}v_k(c_k), & \text{if } (r,c) \text{ is compatible},\\ 0, & \text{otherwise.}\end{cases}
--   $$
--
--   By construction, the weighted compatibility quantity of the main problem equals $\frac{(AD)!}{(D!)^A(A!)^D}$ times the average of $\mathrm{wt}_{w,v}$ over all $(D!)^A(A!)^D$ grids. When the weights are nonnegative and the total weight is positive, normalizing $\mathrm{wt}_{w,v}$ gives a probability law on grids that is supported on compatible grids; this tilted law is the trial law in the entropy (variational) upper bound for that average.
--
--   **Formalization Note** Grids are elements of the product type `Grid A D = Rows A D × Cols A D`, compatibility is the proposition `Compatible` (decided classically), and `compatibilityWeight w v` is a real-valued function on grids. No sign condition on $w$ or $v$ is built into the definition; nonnegativity is assumed separately where needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/VariationalBound.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/VariationalBound.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_ThorpCompatibility_HeavyColumns
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridDeficits

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

noncomputable def compatibilityWeight {A D : ℕ}
    (w : Fin A → Equiv.Perm (Fin D) → ℝ)
    (v : Fin D → Equiv.Perm (Fin A) → ℝ) (a : Grid A D) : ℝ :=
  if Compatible a.1 a.2 then (∏ i, w i (a.1 i)) * (∏ k, v k (a.2 k)) else 0

end ThorpCompatibility

end OAI


