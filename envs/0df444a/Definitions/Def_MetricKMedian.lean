-- Prove2me | Definitions.Def_MetricKMedian
-- name    : MetricKMedian
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:19.171959+00:00
-- url     : https://prove2.me/theorems/c2d3e722-0b26-4222-a1d6-d1d56b61209f
-- statement:
--   This block formalizes the metric k-median problem on a finite point set {0,…,n−1}. An Instance consists of n, a rational-valued distance function on pairs of points that is nonnegative, vanishes exactly on equal points, is symmetric and satisfies the triangle inequality, together with a set of clients, a set of candidate facilities, and a bound k with 1 ≤ k ≤ the number of facilities. encodeNat writes a natural number in a self-delimiting binary form: a unary prefix of ones whose length is the bit-length, a zero separator, then the bits. encodeRat encodes a rational as a sign bit followed by the encodings of the absolute numerator and the denominator, and encodeInstance concatenates the encodings of n and k, the client and facility indicator vectors, and all n² pairwise distances in row-major order. For a set S of points, nearest gives the real distance from a client j to its closest member of S (zero if S is empty), and cost(S) sums this over all clients. feasibleSets are the nonempty subsets of the facilities of size at most k, and optimum is the minimum cost over them (zero if there are none, which cannot happen for valid instances). Correct(ε, I, output) is the proposition that output is exactly the indicator bit-vector, of length n, of some nonempty set S of at most k facilities whose cost is at most (1 + 2/e + ε) times the optimum. This is only a specification of approximate solutions, not a theorem about an algorithm.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MetricKMedian.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MetricKMedian.lean; bytes 16..1912
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI




section
section
namespace MetricKMedian

structure Instance where
  n : ℕ
  distance : Fin n → Fin n → ℚ
  clients : Finset (Fin n)
  facilities : Finset (Fin n)
  k : ℕ
  distance_nonneg : ∀ i j, 0 ≤ distance i j
  distance_eq_zero : ∀ i j, distance i j = 0 ↔ i = j
  distance_symm : ∀ i j, distance i j = distance j i
  distance_triangle : ∀ i j h, distance i h ≤ distance i j + distance j h
  k_pos : 1 ≤ k
  k_le : k ≤ facilities.card

def encodeNat (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

def encodeRat (q : ℚ) : List Bool :=
  [decide (q.num < 0)] ++ encodeNat q.num.natAbs ++ encodeNat q.den

def encodeInstance (I : Instance) : List Bool :=
  encodeNat I.n ++ encodeNat I.k ++
    List.ofFn (fun i : Fin I.n => decide (i ∈ I.clients)) ++
    List.ofFn (fun i : Fin I.n => decide (i ∈ I.facilities)) ++
    (List.ofFn (fun i : Fin I.n =>
      (List.ofFn (fun j : Fin I.n => encodeRat (I.distance i j))).flatten)).flatten

noncomputable def nearest (I : Instance) (j : Fin I.n) (S : Finset (Fin I.n)) : ℝ :=
  if h : S.Nonempty then
    (S.image (fun i => (I.distance j i : ℝ))).min' (h.image _)
  else 0

noncomputable def cost (I : Instance) (S : Finset (Fin I.n)) : ℝ :=
  ∑ j ∈ I.clients, nearest I j S

def feasibleSets (I : Instance) : Finset (Finset (Fin I.n)) :=
  I.facilities.powerset.filter (fun S => S.Nonempty ∧ S.card ≤ I.k)

noncomputable def optimum (I : Instance) : ℝ :=
  if h : (feasibleSets I).Nonempty then
    ((feasibleSets I).image (cost I)).min' (h.image _)
  else 0

def Correct (epsilon : ℝ) (I : Instance) (output : List Bool) : Prop :=
  ∃ S : Finset (Fin I.n), S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k ∧
    output = List.ofFn (fun i : Fin I.n => decide (i ∈ S)) ∧
    cost I S ≤ (1 + 2 / Real.exp 1 + epsilon) * optimum I



end MetricKMedian
end
end
end OAI


