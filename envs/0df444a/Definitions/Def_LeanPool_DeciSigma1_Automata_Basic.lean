-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
-- name    : LeanPool_DeciSigma1_Automata_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:32:46.537048+00:00
-- url     : https://prove2.me/theorems/2e934550-5395-43c3-9412-11e780e7f151
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Automata/Basic.lean

module
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Card
public import Mathlib.Computability.DFA
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1
variable {α S : Type*}
def runFrom (δ : S → α → S) (q : S) (w : List α) : S := w.foldl δ q
end DeciSigma1
namespace DeciSigma1.Automata
abbrev Word (α : Type*) := List α
structure Semiautomaton (α S : Type*) where
  /-- State before reading any input. -/
  start : S
  /-- Transition for one input symbol. -/
  step : S → α → S
variable {α : Type*}
namespace Semiautomaton
variable {S : Type*}
def run (M : Semiautomaton α S) (w : Word α) : S := runFrom M.step M.start w
def PathSafe (M : Semiautomaton α S) (G : S → Prop) (q : S) : Word α → Prop
  | [] => G q
  | c :: w => G q ∧ M.PathSafe G (M.step q c) w
end Semiautomaton
def wordsUpTo [Fintype α] [DecidableEq α] : ℕ → Finset (Word α)
  | 0 => {[]}
  | n + 1 => insert [] (Finset.univ.biUnion fun a : α =>
      (wordsUpTo n).image (List.cons a))
end DeciSigma1.Automata


