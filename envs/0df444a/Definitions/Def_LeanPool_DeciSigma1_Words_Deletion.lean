-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
-- name    : LeanPool_DeciSigma1_Words_Deletion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:41:37.795616+00:00
-- url     : https://prove2.me/theorems/0205c6d0-cfc0-4033-bf9f-76cfd8395952
-- title:
--   Deletion
-- statement:
--   Definitions and structural lemmas for Deletion, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
def deletePositions (w : List α) (D : Finset ℕ) : List α :=
  (w.zipIdx.filter (fun p => p.2 ∉ D)).map Prod.fst
def retainedCount (D : Finset ℕ) (a : ℕ) : ℕ := ((Finset.range a).filter (· ∉ D)).card
variable {D : Finset ℕ}
def greatestPreimage (D : Finset ℕ) (a : ℕ) : ℕ :=
  Nat.findGreatest (fun p => retainedCount D p ≤ a) (a + D.card)
section Interval
variable {c δ : ℕ}
end Interval
end DeciSigma1.Words


