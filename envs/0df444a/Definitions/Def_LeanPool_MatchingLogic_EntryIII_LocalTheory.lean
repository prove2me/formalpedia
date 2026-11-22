-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
-- name    : LeanPool_MatchingLogic_EntryIII_LocalTheory
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:15:27.271797+00:00
-- url     : https://prove2.me/theorems/d70d8c0e-6e30-492f-8d67-3dffd358f30a
-- title:
--   Local Theory
-- statement:
--   Definitions and structural lemmas for Local Theory, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/LocalTheory.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Mathlib.Data.Set.BooleanAlgebra
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
noncomputable section
local instance instDecidableEqPatternLocalTheory : DecidableEq (Pattern S Var) :=
  Classical.decEq _
attribute [local instance] instDecidableEqPatternLocalTheory
def LocProvable (Gamma : Set (Pattern S Var)) (phi : Pattern S Var) : Prop :=
  ∃ l : List (Pattern S Var), (∀ delta ∈ l, delta ∈ Gamma) ∧
    Provable (∅ : Set (Pattern S Var)) (.imp (conj l) phi)
def LocConsistent (Gamma : Set (Pattern S Var)) : Prop :=
  ¬ LocProvable Gamma (.bot : Pattern S Var)
def IsMCS (Gamma : Set (Pattern S Var)) : Prop :=
  LocConsistent Gamma ∧ ∀ {Delta : Set (Pattern S Var)}, Gamma ⊂ Delta → ¬ LocConsistent Delta
namespace LocProvable
end LocProvable
namespace IsMCS
end IsMCS
end
end MatchingLogic


