-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingEntropy_Coupling
-- name    : OAI_Combinatorics_MatchingEntropy_Coupling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:27:25.046989+00:00
-- url     : https://prove2.me/theorems/c69f6eb0-b6af-4427-bd3e-bcae62d02a0f
-- title:
--   Pushforward of a weight vector along a map
-- statement:
--   Let $A$ be a finite set, $C$ any set with decidable equality, $p\in\mathbb{R}^A$ a real weight vector and $f:A\to C$ a map. The *fiber mass* of a point $c\in C$ is the total weight of its fiber $f^{-1}(c)$:
--   $$
--   (f_*p)(c)=\sum_{a\in A:\ f(a)=c}p_a .
--   $$
--   In particular $(f_*p)(c)=0$ when $c$ is not a value of $f$, and when $C$ is finite the masses $(f_*p)(c)$ add up to $\sum_{a\in A}p_a$.
--
--   If $p$ is a probability vector, i.e. the law of a random element $\mathbf a$ of $A$, then $f_*p$ is the law of $f(\mathbf a)$, the pushforward (image) distribution. In the matching setting it transports a law on the perfect matchings of one graph to a law on the perfect matchings of another graph along a map between the two sets of matchings, which is how laws are moved between a graph and a modified version of it.
--
--   **Formalization Note** The definition is `fiberMass p f c`. The weight $p$ is an arbitrary real function, so nonnegativity and normalization are not built into the definition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingEntropy/Coupling.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingEntropy/Coupling.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangleFace mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangleFace
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Model
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Simplex

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def fiberMass {A : Type uA} {C : Type uC} [Fintype A] [DecidableEq C]
    (p : A → ℝ) (f : A → C) (c : C) : ℝ := ∑ a, if f a = c then p a else 0

end MatchingEntropyBounds

end

end OAI


