-- Prove2me | Definitions.Def_BulteauTranspositions_NPHard_Sorting
-- name    : BulteauTranspositions_NPHard_Sorting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T21:51:23.214634+00:00
-- url     : https://prove2.me/theorems/d4753c1c-b873-4f28-b624-078db7e81cdc
-- title:
--   Permutations, block transpositions, breakpoints and sorting distance
-- statement:
--   For positive n, a permutation is a bijection of {0,…,n} fixing 0 and n. A legal cut 0<i<j<k≤n exchanges the adjacent blocks [i,j) and [j,k), preserving internal order. Composition is on the right. The inverse cut is (i,k+i−j,k). An adjacency at x means π(x)=π(x−1)+1, and the breakpoint count includes all x from 1 through n. A sorting sequence is a finite list of legal cuts whose successive right-compositions give the identity on {0,…,n}. Distance is the infimum of actual sequence lengths in the extended natural numbers, with the empty sequence allowed. For the valid permutations considered here this is the ordinary finite minimum: adjacent one-entry block exchanges sort every permutation. The extended value avoids assigning zero to an empty feasible set. Sorting within a signed integer budget requires an actual sequence of length at most that budget; negative budgets therefore reject. Natural-valued functions outside {0,…,n} are immaterial.
-- source:
--   Bulteau, Fertin and Rusu, Sorting by Transpositions is Difficult, supplied PDF arXiv:1011.1157v1, definitions and constructions, printed/PDF pp. 2–3; https://arxiv.org/abs/1011.1157v1

import Mathlib

namespace BulteauTranspositions.NPHard

/-- A finite permutation with the two sentinels of §1. Values outside [0,n] are unused. -/
def IsPermutation (n : ℕ) (p : ℕ → ℕ) : Prop :=
  0 < n ∧ Set.BijOn p (Set.Icc 0 n) (Set.Icc 0 n) ∧ p 0 = 0 ∧ p n = n

structure Cut where
  i : ℕ
  j : ℕ
  k : ℕ
  deriving DecidableEq, Inhabited

def Cut.Legal (c : Cut) (n : ℕ) : Prop := 0 < c.i ∧ c.i < c.j ∧ c.j < c.k ∧ c.k ≤ n

/-- Right-composition exchanges the two adjacent, nonempty blocks. -/
def Cut.tau (c : Cut) (x : ℕ) : ℕ :=
  if x < c.i then x else if x < c.k + c.i - c.j then x + c.j - c.i
  else if x < c.k then x + c.j - c.k else x

def Cut.inv (c : Cut) : Cut := ⟨c.i, c.k + c.i - c.j, c.k⟩

def applyMove (p : ℕ → ℕ) (c : Cut) : ℕ → ℕ := p ∘ c.tau

def adjacency (p : ℕ → ℕ) (x : ℕ) : Prop := p x = p (x - 1) + 1

def breakpoints (n : ℕ) (p : ℕ → ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter fun x => p x ≠ p (x - 1) + 1).card

def movesResult (p : ℕ → ℕ) (cs : List Cut) : ℕ → ℕ := cs.foldl applyMove p

def SortingSequence (n : ℕ) (p : ℕ → ℕ) (cs : List Cut) : Prop :=
  (∀ c ∈ cs, c.Legal n) ∧ ∀ x ≤ n, movesResult p cs x = x

/-- The infimum of actual sequence lengths; +∞ if no sequence exists, never default zero. -/
noncomputable def distance (n : ℕ) (p : ℕ → ℕ) : ℕ∞ :=
  sInf {k | ∃ cs : List Cut, SortingSequence n p cs ∧ k = (cs.length : ℕ∞)}

def SortsWithin (n : ℕ) (p : ℕ → ℕ) (k : ℤ) : Prop :=
  ∃ cs : List Cut, SortingSequence n p cs ∧ (cs.length : ℤ) ≤ k

end BulteauTranspositions.NPHard


