-- Prove2me | Definitions.Def_CSL_Circuit_MemoryAccess_HelperFrameChain
-- name    : CSL_Circuit_MemoryAccess_HelperFrameChain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:58:14.288795+00:00
-- url     : https://prove2.me/theorems/184a0a05-ca3d-4cca-b73a-a981cbcf1df5
-- title:
--   Coded sorting library: Circuit / MemoryAccess / HelperFrameChain
-- statement:
--   Module `CodedSorting.Circuit.MemoryAccess.HelperFrameChain` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Matrix boundaries for three cyclic tensor copies. The paired projectors are idempotent and mutually orthogonal in each factor. In the processed coordinate order, the boundaries are 0, I⊗B⊗C, I⊗B⊗(I-C'), I⊗B⊗I, I-I⊗B'⊗C', I. The sum of the ranks of consecutive differences equals the ambient dimension.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.MemoryAccess.HelperFrameChain

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Labels_Framework_TensorLabels

/-! Matrix boundaries for three cyclic tensor copies. The paired projectors are idempotent and mutually orthogonal in each factor. In the processed coordinate order, the boundaries are 0, I⊗B⊗C, I⊗B⊗(I-C'), I⊗B⊗I, I-I⊗B'⊗C', I. The sum of the ranks of consecutive differences equals the ambient dimension. 











-/

namespace CSL.Construction.HelperFrameChain

open CSL.TensorLabels
open scoped Matrix Kronecker

abbrev SmallMatrix (d : Nat) := Matrix (Fin d) (Fin d) ℚ

variable {d : Nat}

def firstExit (B C : SmallMatrix d) : Label d := tensor3 1 B C
def secondEntry (B C' : SmallMatrix d) : Label d := tensor3 1 B (1 - C')
def secondExit (B : SmallMatrix d) : Label d := tensor3 1 B 1
def thirdEntry (B' C' : SmallMatrix d) : Label d := 1 - tensor3 1 B' C'

private theorem complement_idempotent {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℚ) (hP : P * P = P) : (1 - P) * (1 - P) = 1 - P := by
  simp [mul_sub, sub_mul, hP]

theorem firstExit_idempotent (B C : SmallMatrix d)
    (hB : B * B = B) (hC : C * C = C) :
    firstExit B C * firstExit B C = firstExit B C := by
  simp [firstExit, tensor3_mul, hB, hC]

theorem secondEntry_idempotent (B C' : SmallMatrix d)
    (hB : B * B = B) (hC' : C' * C' = C') :
    secondEntry B C' * secondEntry B C' = secondEntry B C' := by
  simp [secondEntry, tensor3_mul, hB, complement_idempotent C' hC']

theorem secondExit_idempotent (B : SmallMatrix d) (hB : B * B = B) :
    secondExit B * secondExit B = secondExit B := by
  simp [secondExit, tensor3_mul, hB]

theorem thirdEntry_idempotent (B' C' : SmallMatrix d)
    (hB' : B' * B' = B') (hC' : C' * C' = C') :
    thirdEntry B' C' * thirdEntry B' C' = thirdEntry B' C' := by
  apply complement_idempotent
  simp [tensor3_mul, hB', hC']

theorem first_to_second (B C C' : SmallMatrix d)
    (hB : B * B = B) (hCC' : C * C' = 0) (hC'C : C' * C = 0) :
    Nested (firstExit B C) (secondEntry B C') := by
  constructor
  · simp [firstExit, secondEntry, tensor3_mul, hB, mul_sub, hCC']
  · simp [firstExit, secondEntry, tensor3_mul, hB, sub_mul, hC'C]

theorem second_entry_to_exit (B C' : SmallMatrix d) (hB : B * B = B) :
    Nested (secondEntry B C') (secondExit B) := by
  constructor <;> simp [secondEntry, secondExit, tensor3_mul, hB]

theorem second_to_third (B B' C' : SmallMatrix d)
    (hBB' : B * B' = 0) (hB'B : B' * B = 0) :
    Nested (secondExit B) (thirdEntry B' C') := by
  constructor
  · simp only [secondExit, thirdEntry, mul_sub, mul_one, tensor3_mul]
    simp [hBB', tensor3]
  · simp only [secondExit, thirdEntry, sub_mul, one_mul, tensor3_mul]
    simp [hB'B, tensor3]

def boundaries (B C B' C' : SmallMatrix d) : List (Label d) :=
  [firstExit B C, secondEntry B C', secondExit B, thirdEntry B' C', 1]

theorem boundary_chain (B C B' C' : SmallMatrix d)
    (hB : B * B = B) (hC : C * C = C)
    (hB' : B' * B' = B') (hC' : C' * C' = C')
    (hBB' : B * B' = 0) (hB'B : B' * B = 0)
    (hCC' : C * C' = 0) (hC'C : C' * C = 0) :
    IsNestedChain 0 (boundaries B C B' C') := by
  exact ⟨by simp, nested_zero _, firstExit_idempotent B C hB hC,
    first_to_second B C C' hB hCC' hC'C,
    secondEntry_idempotent B C' hB hC', second_entry_to_exit B C' hB,
    secondExit_idempotent B hB, second_to_third B B' C' hBB' hB'B,
    thirdEntry_idempotent B' C' hB' hC', nested_one _, by simp [IsNestedChain]⟩

theorem boundary_rank_cost (B C B' C' : SmallMatrix d)
    (hB : B * B = B) (hC : C * C = C)
    (hB' : B' * B' = B') (hC' : C' * C' = C')
    (hBB' : B * B' = 0) (hB'B : B' * B = 0)
    (hCC' : C * C' = 0) (hC'C : C' * C = 0) :
    chainCost 0 (boundaries B C B' C') = d ^ 3 := by
  have h := chainCost_telescope
    (boundary_chain B C B' C' hB hC hB' hC' hBB' hB'B hCC' hC'C)
  simpa [boundaries, chainLast, rank_identity, pow_succ, Nat.mul_assoc] using h

theorem boundary_rank_cost_eight (B C B' C' : SmallMatrix 8)
    (hB : B * B = B) (hC : C * C = C)
    (hB' : B' * B' = B') (hC' : C' * C' = C')
    (hBB' : B * B' = 0) (hB'B : B' * B = 0)
    (hCC' : C * C' = 0) (hC'C : C' * C = 0) :
    chainCost 0 (boundaries B C B' C') = 512 := by
  exact boundary_rank_cost B C B' C' hB hC hB' hC' hBB' hB'B hCC' hC'C

private theorem last_idempotent {P : Label d} {xs : List (Label d)}
    (h : IsNestedChain P xs) :
    chainLast P xs * chainLast P xs = chainLast P xs := by
  induction xs generalizing P with
  | nil => exact h
  | cons Q qs ih => exact ih h.2.2

/-- Insert the actual monotone local helper visits between the boundaries.
    The two additional entries are explicitly charged transitions. -/
theorem refined_rank_cost (B C B' C' : SmallMatrix d)
    (xs ys zs : List (Label d))
    (hxs : IsNestedChain 0 xs) (hxsLast : chainLast 0 xs = firstExit B C)
    (hys : IsNestedChain (secondEntry B C') ys)
    (hysLast : chainLast (secondEntry B C') ys = secondExit B)
    (hzs : IsNestedChain (thirdEntry B' C') zs)
    (hzsLast : chainLast (thirdEntry B' C') zs = 1)
    (h12 : Nested (firstExit B C) (secondEntry B C'))
    (h23 : Nested (secondExit B) (thirdEntry B' C')) :
    chainCost 0 ((xs ++ (secondEntry B C' :: ys)) ++ (thirdEntry B' C' :: zs)) =
      d ^ 3 := by
  have hfirst : firstExit B C * firstExit B C = firstExit B C := by
    simpa [hxsLast] using last_idempotent hxs
  have hsecond : secondExit B * secondExit B = secondExit B := by
    simpa [hysLast] using last_idempotent hys
  have hnext : IsNestedChain (firstExit B C) (secondEntry B C' :: ys) :=
    ⟨hfirst, h12, hys⟩
  have hjoined : IsNestedChain 0 (xs ++ (secondEntry B C' :: ys)) :=
    nested_chain_append hxs (by simpa [hxsLast] using hnext)
  have hjoinedLast : chainLast 0 (xs ++ (secondEntry B C' :: ys)) = secondExit B := by
    rw [chainLast_append]
    exact hysLast
  have hlast : IsNestedChain (secondExit B) (thirdEntry B' C' :: zs) :=
    ⟨hsecond, h23, hzs⟩
  have hfull : IsNestedChain 0
      ((xs ++ (secondEntry B C' :: ys)) ++ (thirdEntry B' C' :: zs)) :=
    nested_chain_append hjoined (by simpa [hjoinedLast] using hlast)
  have hcost := chainCost_telescope hfull
  simpa [chainLast_append, chainLast, hzsLast, rank_identity, pow_succ,
    Nat.mul_assoc] using hcost

theorem refined_rank_cost_of_orthogonal (B C B' C' : SmallMatrix d)
    (xs ys zs : List (Label d))
    (hxs : IsNestedChain 0 xs) (hxsLast : chainLast 0 xs = firstExit B C)
    (hys : IsNestedChain (secondEntry B C') ys)
    (hysLast : chainLast (secondEntry B C') ys = secondExit B)
    (hzs : IsNestedChain (thirdEntry B' C') zs)
    (hzsLast : chainLast (thirdEntry B' C') zs = 1)
    (hB : B * B = B)
    (hBB' : B * B' = 0) (hB'B : B' * B = 0)
    (hCC' : C * C' = 0) (hC'C : C' * C = 0) :
    chainCost 0 ((xs ++ (secondEntry B C' :: ys)) ++ (thirdEntry B' C' :: zs)) =
      d ^ 3 :=
  refined_rank_cost B C B' C' xs ys zs hxs hxsLast hys hysLast hzs hzsLast
    (first_to_second B C C' hB hCC' hC'C)
    (second_to_third B B' C' hBB' hB'B)

end CSL.Construction.HelperFrameChain


