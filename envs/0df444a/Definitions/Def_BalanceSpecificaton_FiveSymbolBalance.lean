-- Prove2me | Definitions.Def_BalanceSpecificaton_FiveSymbolBalance
-- name    : BalanceSpecificaton_FiveSymbolBalance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:50:58.886282+00:00
-- url     : https://prove2.me/theorems/2ec06444-7803-421a-8961-01d18b40e785
-- title:
--   Five Symbol Balance
-- statement:
--   Definitions and structural lemmas for Five Symbol Balance, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification.FiveSymbol
def terminalObstructions (l : ℕ) : Finset (Word Alphabet) :=
  {List.replicate (l - 1) 1 ++ [4]} ∪
    (Finset.range (l - 1)).image
      (fun j => (forbiddenWord j).drop ((forbiddenWord j).length - l))
def initialObstructions (l : ℕ) : Finset (Word Alphabet) :=
  {[0] ++ List.replicate (l - 1) 1} ∪
    (Finset.range (l - 1)).image (fun j => (forbiddenWord j).take l)
def rightCrossingCover (n l : ℕ) : Finset (Word Alphabet) :=
  (terminalObstructions l).biUnion (fun s =>
    (wordFinset (language shift) (n - l)).image (fun t => s ++ t))
def leftCrossingCover (n l : ℕ) : Finset (Word Alphabet) :=
  (initialObstructions l).biUnion (fun s =>
    (wordFinset (language shift) (n - l)).image (fun t => t ++ s))
end BalanceSpecification.FiveSymbol


