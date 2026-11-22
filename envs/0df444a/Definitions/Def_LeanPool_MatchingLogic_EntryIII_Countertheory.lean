-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_Countertheory
-- name    : LeanPool_MatchingLogic_EntryIII_Countertheory
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:16:42.892225+00:00
-- url     : https://prove2.me/theorems/62e762e3-b0ca-41cc-b367-4b970d3ac57d
-- title:
--   Countertheory
-- statement:
--   Definitions and structural lemmas for Countertheory, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Countertheory.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_FiniteReduction
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.NeZero
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.SetLike
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
def FiniteLocalModelExistence (S : Signature) (Var : Type) [DecidableEq Var] : Prop :=
  ∀ l : List (Pattern S Var), LocConsistent {delta | delta ∈ l} →
    ∃ (M : Model S) (rho : Var → M.carrier) (u : M.carrier),
      u ∈ M.denoteSet rho {delta | delta ∈ l}
end MatchingLogic


