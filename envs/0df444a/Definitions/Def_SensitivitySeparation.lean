-- Prove2me | Definitions.Def_SensitivitySeparation
-- name    : SensitivitySeparation
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:00.305985+00:00
-- url     : https://prove2.me/theorems/641a29d6-5fe9-45d5-a3cd-f88a8ee1259d
-- statement:
--   For a finite index type I and Boolean inputs x : I → Bool, flip(x,B) negates the coordinates of x lying in the set B and leaves the other coordinates unchanged. For a Boolean function f on I → Bool, sensitivityAt(f,x) is the number of single coordinates i such that flipping only i changes the value, f(flip(x,{i})) ≠ f(x), and sensitivity(f) is the maximum of this count over all inputs x. blockSensitivityAt(f,x) is the largest cardinality of a collection of blocks (subsets of I) that are pairwise disjoint, where distinct blocks have empty intersection, and such that every block is nonempty and flipping exactly that block changes the value of f at x; the value is taken as zero for collections failing these conditions, so the empty collection contributes zero. blockSensitivity(f) is the maximum of blockSensitivityAt(f,x) over all inputs x. These are only definitions of the two complexity measures, with no theorem relating them.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SensitivitySeparation.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SensitivitySeparation.lean; bytes 16..927
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open scoped Classical

namespace Paper320

def flip {I : Type} (x : I → Bool) (B : Finset I) : I → Bool :=
  fun i => if i ∈ B then !(x i) else x i

def sensitivityAt {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) : ℕ :=
  (Finset.univ.filter fun i => f (flip x {i}) ≠ f x).card

def sensitivity {I : Type} [Fintype I] (f : (I → Bool) → Bool) : ℕ :=
  Finset.univ.sup (sensitivityAt f)

def blockSensitivityAt {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) : ℕ :=
  Finset.univ.sup fun blocks : Finset (Finset I) =>
    if (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
        (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x)
    then blocks.card else 0

def blockSensitivity {I : Type} [Fintype I] (f : (I → Bool) → Bool) : ℕ :=
  Finset.univ.sup (blockSensitivityAt f)



end Paper320
end
end OAI


