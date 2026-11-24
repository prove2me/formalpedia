-- Prove2me | Definitions.Def_RequestProject_WeightedIso
-- name    : RequestProject_WeightedIso
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T11:26:33.150298+00:00
-- url     : https://prove2.me/theorems/f8236b47-6bd9-4998-b7b3-92e369ddd6eb
-- title:
--   Weighted Iso
-- statement:
--   Definitions and structural lemmas for Weighted Iso, from sawan201 (sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees; see pinned CC0-1.0 LICENSE)'s pinned First-derivative chromatic symmetric function reconstruction for proper trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean

import Definitions.Def_RequestProject_RecoveryThm
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
namespace ChromaticReconstruction
section DartCount
variable {K : Type*} [Fintype K] (S : SimpleGraph K)
def pairCount (Q : K → K → Prop) [DecidableRel Q] : Sym2 K → ℕ :=
  Sym2.lift ⟨fun x y => (if Q x y then 1 else 0) + (if Q y x then 1 else 0),
    fun _ _ => Nat.add_comm _ _⟩
variable (w : K → ℕ)
end DartCount
section Weights
variable {K : Type*} [Fintype K]
def wts (w : K → ℕ) : Multiset ℕ := univ.val.map w
end Weights
section TreeFacts
variable {K : Type*} [Fintype K] {S : SimpleGraph K}
def MIso (S : SimpleGraph K) (w : K → ℕ) : Prop :=
  ∀ u v, u ≠ v → w u = w v → S.degree u = 1 ∧ S.degree v = 1
end TreeFacts
section Keys
variable {K : Type*} [Fintype K]
def keyOf (S : SimpleGraph K) (w : K → ℕ) (x : K) : ℕ × Multiset ℕ :=
  (w x, if Multiset.count (w x) (wts w) = 1 then 0 else (S.neighborFinset x).val.map w)
def fiberInv (W : Multiset ℕ) (E : Multiset (Sym2 ℕ)) (a : ℕ) (M : Multiset ℕ) : ℕ :=
  if W.count a = 1 then (if M = 0 then 1 else 0)
  else if M = {M.sum} ∧ M.sum ≠ a then E.count s(a, M.sum) else 0
variable {S : SimpleGraph K} {w : K → ℕ}
end Keys
section Iso
variable {K K' : Type*} [Fintype K] [Fintype K'] {S : SimpleGraph K} {S' : SimpleGraph K'}
  {w : K → ℕ} {w' : K' → ℕ}
end Iso
end ChromaticReconstruction


