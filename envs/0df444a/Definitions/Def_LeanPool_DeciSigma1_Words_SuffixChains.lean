-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
-- name    : LeanPool_DeciSigma1_Words_SuffixChains
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:41:42.21502+00:00
-- url     : https://prove2.me/theorems/bd8f8844-5805-4246-8142-2754662f8129
-- title:
--   Suffix Chains
-- statement:
--   Definitions and structural lemmas for Suffix Chains, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Interval.Finset.Nat
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Words
open DeciSigma1.Readers
variable {α : Type}
def suffixOfLength (t : List α) (b : ℕ) : List α := t.drop (t.length - b)
variable [DecidableEq α]
def occurrences (x t : List α) (b : ℕ) : Finset ℕ :=
  (Finset.range (x.length + 1)).filter (fun e => b ≤ t.length ∧ suffixOfLength t b <:+ x.take e)
def suffixReturnGap (t : List α) (b : ℕ) : Option ℕ :=
  if b ≤ t.length then
    ((List.range t.length).find? (fun h => suffixOfLength t b <:+ t.take (t.length - (h + 1)))).map
        (· + 1)
  else none
def SuffixStep (t : List α) (b b' : ℕ) : Prop := suffixReturnGap t b = some (b' - b) ∧ b < b'
def SuffixChain (t : List α) (bs : List ℕ) : Prop := bs.IsChain (SuffixStep t)
def ChainBound (t : List α) (Sb : ℕ) : Prop := ∀ bs, SuffixChain t bs → bs.length ≤ Sb + 1
def ChainBoundFrom (t : List α) (b₀ Sb : ℕ) : Prop :=
  ∀ b bs, b₀ ≤ b → SuffixChain t (b :: bs) → bs.length ≤ Sb
section Mortal
variable {S : Type} [Fintype S] {k : ℕ} (M : StructuralReader α S k)
  {W : Fin k → List α} {j : Fin k}
variable {M}
end Mortal
end DeciSigma1.Words


