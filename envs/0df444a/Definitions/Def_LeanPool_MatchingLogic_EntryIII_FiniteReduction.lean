-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_FiniteReduction
-- name    : LeanPool_MatchingLogic_EntryIII_FiniteReduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:15:43.283445+00:00
-- url     : https://prove2.me/theorems/b4405abb-5410-4b14-bfd1-922dd17fcbdd
-- title:
--   Finite Reduction
-- statement:
--   Definitions and structural lemmas for Finite Reduction, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/FiniteReduction.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Compactness
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
def FiniteLocalCompleteness (S : Signature) (Var : Type) [DecidableEq Var] : Prop :=
  ∀ (l : List (Pattern S Var)) (phi : Pattern S Var),
    LocalCons {delta | delta ∈ l} phi →
      Provable (∅ : Set (Pattern S Var)) (.imp (conj l) phi)
end MatchingLogic


