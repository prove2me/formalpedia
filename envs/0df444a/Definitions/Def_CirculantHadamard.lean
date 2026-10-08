-- Prove2me | Definitions.Def_CirculantHadamard
-- name    : CirculantHadamard
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:03.90111+00:00
-- url     : https://prove2.me/theorems/ba8ac9c9-c76b-4f19-a015-bbefd5f4df2a
-- statement:
--   An element is a sign if it equals 1 or −1, a definition available in any type equipped with a distinguished element 1 and negation. For a nonnegative integer n, a real matrix of order n is an n × n matrix with real entries. Such a matrix H is circulant if there is a function h on the indices modulo n such that Hᵢⱼ = h(j − i), with subtraction taken modulo n. It is a sign Hadamard matrix if every entry is 1 or −1 and HHᵀ = nI; equivalently, distinct rows are orthogonal and each row has squared length n. ExistsRealCirculantHadamard(n) is the defined proposition that a real matrix of order n exists satisfying both conditions. The definitions allow n = 0, for which the matrix conditions are vacuous.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CirculantHadamard.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CirculantHadamard.lean; bytes 16..575
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace CirculantHadamard

universe u

def IsSign {R : Type u} [One R] [Neg R] (x : R) : Prop :=
  x = 1 ∨ x = -1

abbrev RealMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def IsCirculant {n : ℕ} (H : RealMatrix n) : Prop :=
  ∃ h : Fin n → ℝ, ∀ i j, H i j = h (j - i)

def IsSignHadamard {n : ℕ} (H : RealMatrix n) : Prop :=
  (∀ i j, IsSign (H i j)) ∧
    H * H.transpose = (n : ℝ) • (1 : RealMatrix n)

def ExistsRealCirculantHadamard (n : ℕ) : Prop :=
  ∃ H : RealMatrix n, IsCirculant H ∧ IsSignHadamard H



end CirculantHadamard
end OAI


