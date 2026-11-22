-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalChoice
-- name    : LeanPool_MatchingLogic_EntryIII_CanonicalChoice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:24:13.848416+00:00
-- url     : https://prove2.me/theorems/f15327b4-45fd-424e-be51-0389653c8be8
-- title:
--   Canonical Choice
-- statement:
--   Definitions and structural lemmas for Canonical Choice, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalChoice.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
variable {S : Signature}
def pfNot (p : PForm) : PForm := .imp p .bot
def pfOr (p q : PForm) : PForm := .imp (pfNot p) q
def pfAnd (p q : PForm) : PForm := pfNot (.imp p (pfNot q))
def Pattern.choiceArgs {n : Nat} (selected : Finset (Fin n))
    (choose : Fin n -> Bool) (Phi : Fin n -> Pattern S Nat)
    (psi : Pattern S Nat) : Fin n -> Pattern S Nat :=
  fun i => if i ∈ selected then
    Pattern.and (Phi i) (if choose i then psi else Pattern.nt psi)
  else Phi i
end MatchingLogic


