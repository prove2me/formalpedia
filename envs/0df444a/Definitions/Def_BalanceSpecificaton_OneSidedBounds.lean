-- Prove2me | Definitions.Def_BalanceSpecificaton_OneSidedBounds
-- name    : BalanceSpecificaton_OneSidedBounds
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:38:18.27927+00:00
-- url     : https://prove2.me/theorems/08dc3592-5e85-412b-bf9e-2c2948143e5c
-- title:
--   One Sided Bounds
-- statement:
--   Definitions and structural lemmas for One Sided Bounds, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedBounds.lean

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace BalanceSpecification.OneSidedExample
def vertexWords (s : Vertex) (n : ℕ) : Finset (Word Alphabet) :=
  (allWords (A := Bool) n).image (runWord s)
def pCover : ℕ → Finset (Word Alphabet)
  | 0 => {[]}
  | n + 1 => ((vertexWords (.q 0) n).image (a :: ·) ∪
      (pCover n).image (b :: ·)) ∪ (vertexWords (.p 0) n).image (c :: ·)
def qCover : ℕ → Finset (Word Alphabet)
  | 0 => {[]}
  | n + 1 => (qCover n).image (a :: ·) ∪ (pCover n).image (b :: ·)
def positiveWordCover (n : ℕ) : Finset (Word Alphabet) :=
  ((qCover n).image (a :: ·) ∪ (pCover n).image (b :: ·)) ∪
    (vertexWords (.p 0) n).image (c :: ·)
def probeWord (n : ℕ) : Word Alphabet := a :: List.replicate (n + 1) b
end BalanceSpecification.OneSidedExample


