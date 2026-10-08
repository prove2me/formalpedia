-- Prove2me | Definitions.Def_SimpleAmenable
-- name    : SimpleAmenable
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:21.94052+00:00
-- url     : https://prove2.me/theorems/7887f1e7-5daa-46ec-8b68-226782f2357a
-- statement:
--   FolnerAmenable(G) is a defined proposition, not an established theorem, for a group G with no topology or additional structure assumed. It says that for every finite subset K of G and every real ε>0 there is a nonempty finite subset D of G such that, for every g in K, the symmetric difference between the left translate gD = {g·d : d ∈ D} and D has cardinality strictly less than ε times the cardinality of D. This is the Følner-set condition for amenability of the discrete group, stated with left multiplication, and it is defined here as a proposition without any proof of its truth for particular groups.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SimpleAmenable.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SimpleAmenable.lean; bytes 16..329
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open scoped symmDiff

namespace SimpleAmenable

noncomputable def FolnerAmenable (G : Type*) [Group G] : Prop := by
  classical
  exact ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
    ∃ D : Finset G, D.Nonempty ∧ ∀ g ∈ K,
      (((D.image (fun d => g * d)) ∆ D).card : ℝ) < ε * D.card



end SimpleAmenable
end OAI


