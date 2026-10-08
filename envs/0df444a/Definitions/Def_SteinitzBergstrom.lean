-- Prove2me | Definitions.Def_SteinitzBergstrom
-- name    : SteinitzBergstrom
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:39.144464+00:00
-- url     : https://prove2.me/theorems/e83c735c-87a2-4736-9cfe-d86de3b67837
-- statement:
--   Vector(d) is d-dimensional real Euclidean space. SignedPrefixBound(C) is the defined proposition that, for all integers d≥1 and N≥1 and every family v₀,…,v_{N-1} of vectors in Vector(d) each of norm at most 1, there exist signs ε_i ∈ {−1,1} such that for every k with 0≤k≤N, the Euclidean norm of the partial sum of ε_i v_i over indices i<k is at most C√d. OrderingPrefixBound(C) is the defined proposition that, for all d≥1 and N≥1 and every such family of vectors of norm at most 1 whose total sum is zero, there exists a permutation π of the N indices such that for every k with 0≤k≤N, the norm of the sum of v_{π(i)} over i<k is at most C√d. These are the signed (Bergström-type) and reordering (Steinitz-type) prefix-sum bounds with a constant C independent of d and N; they are propositions about a real parameter C, not asserted as established theorems.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SteinitzBergstrom.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SteinitzBergstrom.lean; bytes 16..836
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace EuclideanSteinitzBergstrom

abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)

def SignedPrefixBound (C : ℝ) : Prop :=
  ∀ (d N : ℕ), 1 ≤ d → 1 ≤ N →
    ∀ (v : Fin N → Vector d), (∀ i, ‖v i‖ ≤ 1) →
      ∃ ε : Fin N → ℝ, (∀ i, ε i = -1 ∨ ε i = 1) ∧
        ∀ k : ℕ, k ≤ N →
          ‖∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k), ε i • v i‖ ≤
            C * Real.sqrt d

def OrderingPrefixBound (C : ℝ) : Prop :=
  ∀ (d N : ℕ), 1 ≤ d → 1 ≤ N →
    ∀ (v : Fin N → Vector d), (∀ i, ‖v i‖ ≤ 1) → (∑ i, v i) = 0 →
      ∃ π : Equiv.Perm (Fin N), ∀ k : ℕ, k ≤ N →
        ‖∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k), v (π i)‖ ≤
          C * Real.sqrt d



end EuclideanSteinitzBergstrom
end OAI


