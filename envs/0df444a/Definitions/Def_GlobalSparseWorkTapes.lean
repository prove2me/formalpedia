-- Prove2me | Definitions.Def_GlobalSparseWorkTapes
-- name    : GlobalSparseWorkTapes
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-26T22:22:43.273954+00:00
-- url     : https://prove2.me/theorems/bf544fb6-5ea9-4883-9ac8-5a982922ac70
-- title:
--   One sparse budget for all native work-tape halves
-- statement:
--   Store a nonblank work-tape cell as its tape index, zipper side, relative position, and symbol code. Concatenate the entries from every tape and both sides, then pad to one shared entry budget.
-- source:
--   The universal multitape work-tape zipper and trailing-blank normalization in the Prove2Me definition library.

import Definitions.Def_TrimmedNativeWorkTape

namespace GlobalSparseNativeWork

open Turing.MultiTapeTM.Universal TrimmedWorkTape

def boundedSymbol (alphabet a : ℕ) : Fin (alphabet+1) :=
  ⟨a % (alphabet+1),Nat.mod_lt _ (Nat.succ_pos _)⟩

/-- The profile stores one index and symbol for each nonblank in the bounded
window. Explicit blank padding does not contribute an entry. -/
def sparseHalf (window alphabet : ℕ) (tape : List (Option ℕ)) :
    List (Fin window × Fin (alphabet+1)) :=
  (List.finRange window).filterMap fun i => (tape[i.val]?.join).map
    (fun a => (i,boundedSymbol alphabet a))

abbrev GlobalSparseEntry (count window alphabet : ℕ) :=
  (Fin count × Bool) × (Fin window × Fin (alphabet+1))

def zipperHalf (t : Tape) (right : Bool) : List (Option ℕ) :=
  if right then t.right else t.left

/-- Enumerate nonblank work cells with their tape index, side, and relative position.
The length of this list counts all entries against one budget. -/
def globalSparseProfile (count window alphabet : ℕ) (tapes : List Tape) :
    List (GlobalSparseEntry count window alphabet) :=
  ((List.finRange count).product [false,true]).flatMap fun address =>
    (sparseHalf window alphabet
      (zipperHalf ((tapes[address.1.val]?).getD default) address.2)).map fun entry => (address,entry)

abbrev GlobalSparseWorkCode (count window alphabet entries : ℕ) :=
  Fin entries → Option (GlobalSparseEntry count window alphabet)

def packGlobalSparseWork (count window alphabet entries : ℕ) (tapes : List Tape) :
    GlobalSparseWorkCode count window alphabet entries :=
  fun i => (globalSparseProfile count window alphabet tapes)[i.val]?

def GlobalSparseHalfFits (window alphabet : ℕ) (cells : List (Option ℕ)) : Prop :=
  cells.length ≤ window ∧ ∀ a, some a ∈ cells → a ≤ alphabet

def GlobalSparseWorkFits (count window alphabet entries : ℕ) (tapes : List Tape) : Prop :=
  tapes.length = count ∧
  (∀ t ∈ tapes, GlobalSparseHalfFits window alphabet t.left ∧ GlobalSparseHalfFits window alphabet t.right) ∧
  (globalSparseProfile count window alphabet tapes).length ≤ entries

end GlobalSparseNativeWork


