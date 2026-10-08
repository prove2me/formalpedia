-- Prove2me | Definitions.Def_SimpleOvergroups
-- name    : SimpleOvergroups
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:22.147976+00:00
-- url     : https://prove2.me/theorems/ffc54ca0-1f82-48b4-aa35-99315137810c
-- statement:
--   For a group G, a tuple g of n elements of G, and a word w given as a list of pairs (i,b) with i in Fin n and b a Boolean, evalWord(g,w) is the product in G, in list order, of the letters g_i when b is true and g_i⁻¹ when b is false. HasDecidableWordProblem(G) is the proposition that there exist n and a family g : Fin n → G whose range generates G (the closure of the range is the whole group) such that the set of words w with evalWord(g,w)=1 is a computable predicate on lists of such letters. HasTypeFInfty(H) is the proposition that, within the same universe as H, there exist a topological space X carrying a CW complex structure on the whole space, such that X is Hausdorff, connected, and the CW complex is of finite type in Mathlib's sense, together with a point x of X and a group isomorphism from H to the fundamental group of X at x, and also a space E with a topology and a surjective covering map p : E → X with E contractible. These are defined propositions about groups; the block states no theorem about them.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SimpleOvergroups.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SimpleOvergroups.lean; bytes 16..1077
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace SimpleFInftyOvergroups
universe u

def evalWord {G : Type u} [Group G] {n : ℕ} (g : Fin n → G)
    (w : List (Fin n × Bool)) : G :=
  (w.map fun x => if x.2 then g x.1 else (g x.1)⁻¹).prod

def HasDecidableWordProblem (G : Type u) [Group G] : Prop :=
  ∃ (n : ℕ) (g : Fin n → G), Subgroup.closure (Set.range g) = ⊤ ∧
    ComputablePred (fun w : List (Fin n × Bool) => evalWord g w = 1)

def HasTypeFInfty (H : Type u) [Group H] : Prop :=
  ∃ (X : Type u) (topology : TopologicalSpace X),
    letI : TopologicalSpace X := topology
    ∃ (cw : Topology.CWComplex (Set.univ : Set X)),
      letI : Topology.CWComplex (Set.univ : Set X) := cw
      T2Space X ∧ ConnectedSpace X ∧
      Topology.CWComplex.FiniteType (Set.univ : Set X) ∧
      ∃ (x : X), Nonempty (H ≃* FundamentalGroup X x) ∧
        ∃ (E : Type u) (coverTopology : TopologicalSpace E),
          letI : TopologicalSpace E := coverTopology
          ∃ (p : E → X), IsCoveringMap p ∧ Function.Surjective p ∧ ContractibleSpace E



end SimpleFInftyOvergroups
end OAI


