-- Prove2me | Definitions.Def_RequestProject_PathLeaf
-- name    : RequestProject_PathLeaf
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T11:23:01.045052+00:00
-- url     : https://prove2.me/theorems/6ed6ee79-654a-4765-9324-b11f4d0c715f
-- title:
--   Path Leaf
-- statement:
--   Definitions and structural lemmas for Path Leaf, from sawan201 (sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees; see pinned CC0-1.0 LICENSE)'s pinned First-derivative chromatic symmetric function reconstruction for proper trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeaf.lean

import Definitions.Def_RequestProject_Forest
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
namespace ChromaticReconstruction
def vx (n x : ℕ) : Fin (n + 1) := ⟨min x n, by omega⟩
def PL (n c : ℕ) : SimpleGraph (Fin (n + 1)) where
  Adj x y := (x.val + 1 = y.val ∧ y.val < n) ∨ (y.val + 1 = x.val ∧ x.val < n) ∨
    (x.val = c ∧ y.val = n ∧ c < n) ∨ (y.val = c ∧ x.val = n ∧ c < n)
  symm := ⟨fun x y h => by
    rcases h with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))⟩
  loopless := ⟨fun x h => by
    rcases h with h | h | h | h <;> omega⟩
def pe (n i : ℕ) : Sym2 (Fin (n + 1)) := s(vx n i, vx n (i + 1))
def lf (n p : ℕ) : Sym2 (Fin (n + 1)) := s(vx n p, vx n n)
end ChromaticReconstruction


