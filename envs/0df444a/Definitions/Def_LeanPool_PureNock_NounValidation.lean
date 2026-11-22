-- Prove2me | Definitions.Def_LeanPool_PureNock_NounValidation
-- name    : LeanPool_PureNock_NounValidation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:59:10.47618+00:00
-- url     : https://prove2.me/theorems/c0d4afcd-3a72-460b-8e05-002e30ac6fa8
-- title:
--   Noun Validation
-- statement:
--   Definitions and structural lemmas for Noun Validation, from Pure Nock formalization contributors; LeanPool contributors's pinned Pure Nock semantics, trace certificates, and polynomial fingerprints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Ring.Nat
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Nock
namespace Noun
end Noun
abbrev Transcript := List (Noun × Option (Noun × Noun))
def stepMset (m : Multiset Noun) (n : Noun) (ch : Option (Noun × Noun)) :
    Option (Multiset Noun) :=
  match n, ch with
  | Noun.atom k, none => if Noun.atom k ∈ m then some (m.erase (Noun.atom k)) else none
  | Noun.cell a b, some (a', b') =>
      if Noun.cell a b ∈ m ∧ a = a' ∧ b = b' then
        some (a ::ₘ b ::ₘ m.erase (Noun.cell a b)) else none
  | _, _ => none
def runMset : Multiset Noun → Transcript → Option (Multiset Noun)
  | m, [] => some m
  | m, (n, ch) :: ts =>
      match stepMset m n ch with
      | some m' => runMset m' ts
      | none => none
inductive Result where
  | accept : Result
  | reject : Result
deriving DecidableEq, Repr
def checkValidNoun (n₀ : Noun) (T : Transcript) : Result :=
  match runMset {n₀} T with
  | some m => if m = 0 then Result.accept else Result.reject
  | none => Result.reject
def msize (m : Multiset Noun) : ℕ := (m.map Noun.size).sum
def transcript : Noun → Transcript
  | Noun.atom k => [(Noun.atom k, none)]
  | Noun.cell l r => (Noun.cell l r, some (l, r)) :: (transcript l ++ transcript r)
end Nock


