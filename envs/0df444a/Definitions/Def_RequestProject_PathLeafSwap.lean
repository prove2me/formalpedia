-- Prove2me | Definitions.Def_RequestProject_PathLeafSwap
-- name    : RequestProject_PathLeafSwap
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T12:38:18.68443+00:00
-- url     : https://prove2.me/theorems/426eaa2a-9381-454e-8302-62ebc04b0d00
-- title:
--   Path Leaf Swap
-- statement:
--   Definitions and structural lemmas for Path Leaf Swap, from sawan201 (sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees; see pinned CC0-1.0 LICENSE)'s pinned First-derivative chromatic symmetric function reconstruction for proper trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
namespace ChromaticReconstruction
variable {n c : ℕ}
def rfv (c s x : ℕ) : ℕ := if c + 1 ≤ x + s ∧ x ≤ c + s then 2 * c + 1 - x else x
def rf (n c s : ℕ) (x : Fin (n + 1)) : Fin (n + 1) := vx n (rfv c s x.val)
def brk (n c : ℕ) (F : Finset (Sym2 (Fin (n + 1)))) (j : ℕ) : Prop :=
  (j = c + 1 ∨ pe n (c - j) ∉ F) ∧ pe n (c + j) ∉ F
def HasBrk (n c : ℕ) (F : Finset (Sym2 (Fin (n + 1)))) : Prop :=
  ∃ j, 1 ≤ j ∧ j ≤ c + 1 ∧ brk n c F j
def sB (n c : ℕ) (F : Finset (Sym2 (Fin (n + 1)))) : ℕ :=
  if h : HasBrk n c F then Nat.find h else 0
section Swap
variable {p : ℕ} {F : Finset (Sym2 (Fin (n + 1)))}
end Swap
section Reach
variable {V : Type*} [Fintype V]
end Reach
def psiMap (n c p : ℕ) (F : Finset (Sym2 (Fin (n + 1)))) : Finset (Sym2 (Fin (n + 1))) :=
  if lf n p ∉ F then F
  else if pe n c ∈ F then insert (lf n (2 * c + 1 - p)) (F.erase (lf n p))
  else F.image (Sym2.map (rf n c (sB n c F)))
end ChromaticReconstruction


