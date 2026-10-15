-- Prove2me | Definitions.Def_OAI_Probability_ThorpCompatibility_Model
-- name    : OAI_Probability_ThorpCompatibility_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:18:50.191704+00:00
-- url     : https://prove2.me/theorems/64f23d1e-e960-445e-8cfe-4b453fb9b189
-- title:
--   The grid of row and column permutations
-- statement:
--   Fix natural numbers $A$ and $D$. Write $[A]=\{0,\dots,A-1\}$, $[D]=\{0,\dots,D-1\}$, and $S_n$ for the set of permutations of $[n]$. A row configuration $r$ assigns to each row $i\in[A]$ a permutation $r_i\in S_D$. A column configuration $c$ assigns to each column $k\in[D]$ a permutation $c_k\in S_A$. The grid is the finite set of all such pairs:
--   $$
--   \mathcal G_{A,D}=\mathrm{Rows}_{A,D}\times\mathrm{Cols}_{A,D}=(S_D)^{[A]}\times(S_A)^{[D]} .
--   $$
--   Its elements are written $a=(r,c)$, and it has $(D!)^A(A!)^D$ elements.
--
--   The weighted compatibility quantity is a uniform average over $\mathcal G_{A,D}$. A pair is compatible when, for every $j\in[D]$, the values $c_{r_i(j)}(i)$ with $i\in[A]$ are pairwise distinct. The entropy method studies laws on this set, especially the law obtained by tilting the uniform law by the weight $\mathbf 1[(r,c)\text{ compatible}]\prod_i w_i(r_i)\prod_k v_k(c_k)$.
--
--   **Formalization Note** `Grid A D` is an abbreviation for `Rows A D × Cols A D`. The types `Rows A D = Fin A → Equiv.Perm (Fin D)` and `Cols A D = Fin D → Equiv.Perm (Fin A)`, and the predicate `Compatible`, come from the project's base definitions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/Model.lean by skeleton subtraction
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

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

abbrev Grid (A D : ℕ) := Rows A D × Cols A D

end ThorpCompatibility

end OAI


