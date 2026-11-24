-- Prove2me | Definitions.Def_BalanceSpecificaton_SGapRenewal
-- name    : BalanceSpecificaton_SGapRenewal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:38:56.547038+00:00
-- url     : https://prove2.me/theorems/77f5a26e-9ace-48b9-8d36-8df1b839f844
-- title:
--   SGap Renewal
-- statement:
--   Definitions and structural lemmas for SGap Renewal, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGapRenewal.lean

module
public import Definitions.Def_BalanceSpecificaton_SGap
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification
def sGapListConcat (ss : List ℕ) : Word Bool :=
  (ss.map (fun s => true :: List.replicate s false)).flatten
def sGapConcat {r : ℕ} (f : Fin r → ℕ) : Word Bool := sGapListConcat (List.ofFn f)
def renewalFinset (S : Set ℕ) (n : ℕ) : Finset (Word Bool) :=
  wordFinset (generatedWords (sGapCode S)) n
def renewalCount (S : Set ℕ) (n : ℕ) : ℕ := (renewalFinset S n).card
def renewalPiece (S : Set ℕ) (n s : ℕ) : Finset (Word Bool) := by
  classical
  exact (renewalFinset S (n - s - 1)).image
    (fun v => (true :: List.replicate s false) ++ v)
def renewalGaps (S : Set ℕ) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (· ∈ S)
end BalanceSpecification


