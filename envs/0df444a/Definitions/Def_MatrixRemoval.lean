-- Prove2me | Definitions.Def_MatrixRemoval
-- name    : MatrixRemoval
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:18.712982+00:00
-- url     : https://prove2.me/theorems/757d5fed-8109-4324-bdf9-6c2daa8b57f0
-- statement:
--   A binary n×n matrix is a function from pairs of indices in Fin n to Bool. An increasing map from Fin k to Fin n is a strictly monotone function. For a k×k pattern H and an n×n matrix A, orderedCopies(H,A) is the finite set of pairs (r,c) of increasing maps Fin k → Fin n such that A(r(i),c(j)) = H(i,j) for all i,j, so a copy is an order-preserving choice of k rows and k columns on which A matches H exactly, including its zero entries; copyCount is the number of such pairs, and HFree(H,A) means copyCount is zero. hammingDistance(A,B) counts the positions where two n×n matrices differ. The block then fixes a specific 66×66 pattern fixedH. On indices below 64 it is given by anchor64: for rows u≥32 and columns v≥59 the entry is the (v−58)th binary digit, counted from the most significant of five digits, of u−32 (etaBit); elsewhere the entry is true exactly when u≠v. Pairing an index below 64 with 64 or 65, the entry is true only for the pairs (0,64), (1,65) and their transposes, and among indices 64 and 65 the entry is true exactly when u=65 or v=64. fixedMinEdits(A) is the minimum, over all n×n matrices B that are fixedH-free, of the Hamming distance from A to B (non-free B are assigned the penalty n²+1, so for n large enough this is the least number of entry changes making A free of fixedH), and fixedDistance(A) is this minimum divided by n² as a real number. These are definitions only; no removal-lemma bound is stated.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/MatrixRemoval.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/MatrixRemoval.lean; bytes 16..1765
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

namespace Problem348

abbrev BinaryMatrix (n : ℕ) := Fin n → Fin n → Bool

abbrev IncreasingMap (k n : ℕ) := {f : Fin k → Fin n // StrictMono f}

def orderedCopies {k n : ℕ} (H : BinaryMatrix k) (A : BinaryMatrix n) :
    Finset (IncreasingMap k n × IncreasingMap k n) := by
  classical
  exact Finset.univ.filter (fun rc =>
    ∀ i j, A ((rc.1).val i) ((rc.2).val j) = H i j)

def copyCount {k n : ℕ} (H : BinaryMatrix k) (A : BinaryMatrix n) : ℕ :=
  (orderedCopies H A).card

def HFree {k n : ℕ} (H : BinaryMatrix k) (A : BinaryMatrix n) : Prop :=
  copyCount H A = 0

def hammingDistance {n : ℕ} (A B : BinaryMatrix n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun rc : Fin n × Fin n =>
    A rc.1 rc.2 ≠ B rc.1 rc.2)).card

def etaBit (a b : ℕ) : Bool :=
  decide (((a / (2 ^ (5 - b))) % 2) = 1)

def anchor64 (u v : Fin 64) : Bool :=
  if 32 ≤ u.val ∧ 59 ≤ v.val then
    etaBit (u.val - 32) (v.val - 58)
  else
    decide (u.val ≠ v.val)

def fixedH : BinaryMatrix 66 := fun u v =>
  if hu : u.val < 64 then
    if hv : v.val < 64 then
      anchor64 ⟨u.val, hu⟩ ⟨v.val, hv⟩
    else
      decide ((v.val = 64 ∧ u.val = 0) ∨
        (v.val = 65 ∧ u.val = 1))
  else
    if v.val < 64 then
      decide ((u.val = 64 ∧ v.val = 0) ∨
        (u.val = 65 ∧ v.val = 1))
    else
      decide (u.val = 65 ∨ v.val = 64)

def fixedMinEdits {n : ℕ} (A : BinaryMatrix n) : ℕ := by
  classical
  exact
    (Finset.univ.image (fun B : BinaryMatrix n =>
      if HFree fixedH B then hammingDistance A B else n * n + 1)).min'
      (by simp)

def fixedDistance {n : ℕ} (A : BinaryMatrix n) : ℝ :=
  (fixedMinEdits A : ℝ) / ((n : ℝ) ^ 2)



end Problem348
end
end OAI


