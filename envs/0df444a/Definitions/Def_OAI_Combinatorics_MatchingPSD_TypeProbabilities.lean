-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
-- name    : OAI_Combinatorics_MatchingPSD_TypeProbabilities
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T03:30:41.384986+00:00
-- url     : https://prove2.me/theorems/32985312-8bf1-4732-805a-814d66f7009b
-- title:
--   Maps with prescribed types factor as products of fibers
-- statement:
--   Let $H$, $A$ and $T$ be sets, let $\eta : A \to T$ assign to each element of $A$ a type in $T$, and let $k : H \to T$ prescribe a type for each $i \in H$. The module defines the canonical bijection
--
--   $$
--   \bigl\{ f : H \to A \;:\; \eta \circ f = k \bigr\} \;\longrightarrow\; \prod_{i \in H} \eta^{-1}\bigl(k(i)\bigr), \qquad f \longmapsto \bigl(f(i)\bigr)_{i \in H},
--   $$
--
--   whose inverse assembles a family $(a_i)_{i \in H}$ with $\eta(a_i) = k(i)$ into the map $i \mapsto a_i$. In words, choosing a map whose composition with $\eta$ equals $k$ is the same as choosing, independently for every $i \in H$, an element of the fiber of $\eta$ over $k(i)$.
--
--   For finite sets this yields the count $|\{f : \eta \circ f = k\}| = \prod_{i \in H} |\eta^{-1}(k(i))|$, which is used to reorganize sums over all maps $f : H \to A$ according to their type $\eta \circ f$, and from there to express the probabilities of type classes under product measures through multinomial coefficients.
--
--   **Formalization Note** The definition is `functionFiberEquiv η k`, an `Equiv` from the subtype `{f : H → A // η ∘ f = k}` to the dependent function type `(i : H) → {a : A // η a = k i}`. It uses no finiteness or decidability assumptions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/TypeProbabilities.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/TypeProbabilities.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingPSD mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds

-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace MatchingSmoothing

section ProductTypes
variable {H : Type u_5} {A : Type u_6} {T : Type u_7} [Fintype H] [DecidableEq H] [Fintype A] [Fintype T]
  [DecidableEq A] [DecidableEq T]

noncomputable def functionFiberEquiv (η : A → T) (k : H → T) :
    {f : H → A // η ∘ f = k} ≃ ((i : H) → {a : A // η a = k i}) where
  toFun f i := ⟨f.1 i, congrFun f.2 i⟩
  invFun g := ⟨fun i => (g i).1, funext (fun i => (g i).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

end ProductTypes

end MatchingSmoothing

end OAI


