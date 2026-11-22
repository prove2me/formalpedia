-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessSupply
-- name    : LeanPool_MatchingLogic_EntryIII_WitnessSupply
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:27:49.710628+00:00
-- url     : https://prove2.me/theorems/2b771a9a-f8e4-424a-929f-c083c181f0d7
-- title:
--   Witness Supply
-- statement:
--   Definitions and structural lemmas for Witness Supply, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessSupply.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessedCollapse
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Lindenbaum
public import Mathlib.Data.Set.Finite.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
open Set
variable {S : Signature}
def InfiniteWitnessSupply (Gamma : Set (Pattern S Nat)) : Prop :=
  ∀ {x : Nat} {p : Pattern S Nat}, .ex x p ∈ Gamma →
    Set.Infinite
      {y : Nat |
        .imp (.ex x p) (Pattern.captureAvoidingSubst x y p) ∈ Gamma}
def InfiniteFreshVariableSupply (Gamma : Set (Pattern S Nat)) : Prop :=
  Set.Infinite {y : Nat | ∀ q ∈ Gamma, y ∉ FV q}
noncomputable section
local instance witnessSupplyDecidableEqPattern : DecidableEq (Pattern S Nat) :=
  Classical.decEq _
def supplyStageTheory (Gamma : Set (Pattern S Nat))
    (l : List (Pattern S Nat)) : Set (Pattern S Nat) :=
  Gamma ∪ {q | q ∈ l}
noncomputable def Pattern.supplyFresh
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (l : List (Pattern S Nat)) (p : Pattern S Nat) : Nat :=
  Classical.choose
    (hSupply.exists_notMem_finset
      ((listSupport l).allVars ∪ p.allVars))
def supplyAddWitness
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (l : List (Pattern S Nat)) : Pattern S Nat → List (Pattern S Nat)
  | .ex x p =>
      let y := Pattern.supplyFresh Gamma hSupply l p
      .imp (.ex x p) (Pattern.captureAvoidingSubst x y p) :: l
  | _ => l
abbrev supplyWitnessStages
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (enum : Nat → Pattern S Nat) : Nat → List (Pattern S Nat) :=
  henkinStages (supplyAddWitness Gamma hSupply) enum []
def suppliedHenkinTheory
    (Gamma : Set (Pattern S Nat)) (hSupply : InfiniteFreshVariableSupply Gamma)
    (enum : Nat → Pattern S Nat) : Set (Pattern S Nat) :=
  henkinLimit (supplyStageTheory Gamma) (supplyAddWitness Gamma hSupply) enum []
end
end MatchingLogic


