-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_CanonicalCore
-- name    : LeanPool_MatchingLogic_EntryIII_CanonicalCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:24:34.999358+00:00
-- url     : https://prove2.me/theorems/d06b61b7-fcd9-4745-99d2-10fdd24a031e
-- title:
--   Canonical Core
-- statement:
--   Definitions and structural lemmas for Canonical Core, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/CanonicalCore.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_MCSAlpha
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
open Set
variable {S : Signature}
noncomputable section
local instance instDecidableEqPatternNatCanonicalCore : DecidableEq (Pattern S Nat) :=
  Classical.decEq _
def CanonicalCarrier (S : Signature) :=
  {Gamma : Set (Pattern S Nat) // IsMCS Gamma ∧ FreshWitnessed Gamma}
instance CanonicalCarrier.coeSet :
    Coe (CanonicalCarrier S) (Set (Pattern S Nat)) where
  coe Gamma := Gamma.val
namespace CanonicalCarrier
end CanonicalCarrier
def canonicalInterp (sigma : S.Sym)
    (components : Fin (S.arity sigma) → CanonicalCarrier S) :
    Set (CanonicalCarrier S) :=
  {Gamma | ∀ args : Fin (S.arity sigma) → Pattern S Nat,
    (∀ i, args i ∈ (components i).val) →
      Pattern.app sigma args ∈ Gamma.val}
abbrev canonicalModel (root : CanonicalCarrier S) : Model S where
  carrier := CanonicalCarrier S
  nonempty := ⟨root⟩
  interp := canonicalInterp
end
end MatchingLogic


