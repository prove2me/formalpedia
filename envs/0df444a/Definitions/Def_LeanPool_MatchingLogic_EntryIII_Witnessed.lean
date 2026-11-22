-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
-- name    : LeanPool_MatchingLogic_EntryIII_Witnessed
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:23:58.904934+00:00
-- url     : https://prove2.me/theorems/a55ae4df-c898-4a59-ac5b-6e92a2cf422e
-- title:
--   Witnessed
-- statement:
--   Definitions and structural lemmas for Witnessed, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/Witnessed.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_CaptureAvoiding
public import Mathlib.Data.Countable.Defs
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_LocalTheory
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Alpha
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Lindenbaum
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
open Set
variable {S : Signature}
noncomputable section
local instance instDecidableEqPatternNatWitnessed : DecidableEq (Pattern S Nat) :=
  Classical.decEq _
def Witnessed (Gamma : Set (Pattern S Nat)) : Prop :=
  ∀ {x : Nat} {p : Pattern S Nat}, .ex x p ∈ Gamma →
    ∃ y : Nat, .imp (.ex x p) (Pattern.captureAvoidingSubst x y p) ∈ Gamma
def FreshWitnessed (Gamma : Set (Pattern S Nat)) : Prop :=
  ∀ {x : Nat} {p : Pattern S Nat}, .ex x p ∈ Gamma →
    ∃ y : Nat, y ∉ p.allVars ∧
      .imp (.ex x p) (Pattern.captureAvoidingSubst x y p) ∈ Gamma
def henkinStages {α : Type} (step : List α → α → List α)
    (enum : Nat → α) (base : List α) : Nat → List α
  | 0 => base
  | n + 1 => step (henkinStages step enum base n) (enum n)
def henkinLimit {α : Type} (stageTheory : List α → Set α)
    (step : List α → α → List α) (enum : Nat → α) (base : List α) : Set α :=
  {q | ∃ n, q ∈ stageTheory (henkinStages step enum base n)}
def Pattern.listSupport : List (Pattern S Nat) → Pattern S Nat
  | [] => .bot
  | p :: l => .imp p (listSupport l)
def Pattern.henkinFresh (l : List (Pattern S Nat)) (p : Pattern S Nat) : Nat :=
  (Pattern.imp (listSupport l) p).fresh
def addWitness (l : List (Pattern S Nat)) : Pattern S Nat → List (Pattern S Nat)
  | .ex x p =>
      let y := Pattern.henkinFresh l p
      .imp (.ex x p) (Pattern.captureAvoidingSubst x y p) :: l
  | _ => l
abbrev witnessStages (enum : Nat → Pattern S Nat)
    (base : List (Pattern S Nat)) : Nat → List (Pattern S Nat) :=
  henkinStages addWitness enum base
def henkinTheory (enum : Nat → Pattern S Nat)
    (base : List (Pattern S Nat)) : Set (Pattern S Nat) :=
  henkinLimit (fun l => {q | q ∈ l}) addWitness enum base
end
end MatchingLogic


