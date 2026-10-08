-- Prove2me | Definitions.Def_EgyptianFractions
-- name    : EgyptianFractions
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:09.347978+00:00
-- url     : https://prove2.me/theorems/35b94a65-7d55-451e-a3f5-d68a5d55cedf
-- statement:
--   An Egyptian expansion of a rational number x of length k is a strictly increasing sequence of k natural-number denominators, each at least 2, whose reciprocals sum to x. For natural numbers a and b, egyptianLengths(a,b) is the set of all such lengths for a/b, and egyptianLength(a,b) is its least element, with value 0 if this set is empty. The quantity maxEgyptianLength(b) is the maximum of egyptianLength(a,b) over 1 ≤ a < b, taking value 0 when there are no such numerators. A separate notion of an expansion of 1 allows denominators at least 1, still strictly increasing, and requires their reciprocals to sum to 1. OneExpansions(k) is the set of these sequences of length k, and F(k) is its natural-number cardinality; this cardinality convention gives 0 for an infinite set. The set D(k) consists of all integers m ≥ 2 occurring as a denominator in some such expansion of 1 of length k. The missing denominators are the integers at least 2 outside D(k), and v(k) is their least element, with value 0 if none are missing. Finally, prescribedSlope(k) is the real quantity log(log(v(k)))/k. These are definitions, without accompanying existence or finiteness assertions.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EgyptianFractions.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EgyptianFractions.lean; bytes 16..1205
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem337

def IsEgyptianExpansion {k : ℕ} (x : ℚ) (n : Fin k → ℕ) : Prop :=
  (∀ i, 2 ≤ n i) ∧ StrictMono n ∧
    (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) = x

def egyptianLengths (a b : ℕ) : Set ℕ :=
  {k | ∃ n : Fin k → ℕ,
    IsEgyptianExpansion ((a : ℚ) / (b : ℚ)) n}

def egyptianLength (a b : ℕ) : ℕ :=
  sInf (egyptianLengths a b)

def maxEgyptianLength (b : ℕ) : ℕ :=
  (Finset.range b).sup (fun a => if 1 ≤ a then egyptianLength a b else 0)

def IsOneExpansion {k : ℕ} (n : Fin k → ℕ) : Prop :=
  (∀ i, 1 ≤ n i) ∧ StrictMono n ∧
    (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) = 1

def OneExpansions (k : ℕ) : Set (Fin k → ℕ) :=
  {n | IsOneExpansion n}

def F (k : ℕ) : ℕ :=
  (OneExpansions k).ncard

def D (k : ℕ) : Set ℕ :=
  {m | 2 ≤ m ∧ ∃ n : Fin k → ℕ,
    IsOneExpansion n ∧ ∃ i : Fin k, n i = m}

def missingDenominators (k : ℕ) : Set ℕ :=
  {m : ℕ | 2 ≤ m} \ D k

def v (k : ℕ) : ℕ :=
  sInf (missingDenominators k)

def prescribedSlope (k : ℕ) : ℝ :=
  Real.log (Real.log (v k : ℝ)) / (k : ℝ)



end Problem337
end
end OAI


