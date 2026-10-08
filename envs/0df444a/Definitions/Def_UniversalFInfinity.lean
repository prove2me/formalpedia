-- Prove2me | Definitions.Def_UniversalFInfinity
-- name    : UniversalFInfinity
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:36.931132+00:00
-- url     : https://prove2.me/theorems/8d4141ad-d152-487a-b004-941735c5b3b8
-- statement:
--   HasTypeFInfinity(G) is a defined proposition about a group G in a given universe. It asserts that there exist a Hausdorff (T2), connected topological space X carrying the structure of a CW complex whose underlying set is all of X, with only finitely many cells in each dimension n, together with a base point x of X whose fundamental group is isomorphic as a group to G (some multiplicative equivalence exists), and a contractible topological space E with a surjective covering map p from E to X. In other words, G is the fundamental group of such a connected Hausdorff CW complex of finite type, which has a contractible covering space. The statement is a defined predicate, not a proved theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/UniversalFInfinity.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/UniversalFInfinity.lean; bytes 16..497
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace UniversalFInfinity
universe u

def HasTypeFInfinity (G : Type u) [Group G] : Prop :=
  ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X)
    (_ : ConnectedSpace X) (cw : Topology.CWComplex (Set.univ : Set X)),
    (∀ n : ℕ, Finite (cw.cell n)) ∧
    (∃ x : X, Nonempty (FundamentalGroup X x ≃* G)) ∧
    ∃ (E : Type u) (_ : TopologicalSpace E) (_ : ContractibleSpace E)
      (p : E → X), Function.Surjective p ∧ IsCoveringMap p



end UniversalFInfinity
end OAI


