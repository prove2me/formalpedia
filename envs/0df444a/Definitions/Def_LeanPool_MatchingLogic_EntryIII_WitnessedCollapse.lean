-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_EntryIII_WitnessedCollapse
-- name    : LeanPool_MatchingLogic_EntryIII_WitnessedCollapse
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:27:15.471036+00:00
-- url     : https://prove2.me/theorems/28d795fc-093b-42e7-aa13-7e4b7441780d
-- title:
--   Witnessed Collapse
-- statement:
--   Definitions and structural lemmas for Witnessed Collapse, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/EntryIII/WitnessedCollapse.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_EntryIII_Witnessed
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Theorems.Thm_MatchingLogic_Pattern_IsCaptureAvoidingSubst_denote

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
open Set
noncomputable section
variable {S : Signature}
def pointedTheory (M : Model S) (rho : Nat → M.carrier) (u : M.carrier) :
    Set (Pattern S Nat) :=
  {p | u ∈ M.denote rho p}
abbrev WitnessCollapseSig : Signature where
  Sym := Empty
  arity e := Empty.elim e
abbrev witnessCollapseModel : Model WitnessCollapseSig where
  carrier := Bool
  nonempty := ⟨false⟩
  interp e := Empty.elim e
def witnessCollapseRho : Nat → witnessCollapseModel.carrier := fun n => n = 0
def witnessCollapseTheory : Set (Pattern WitnessCollapseSig Nat) :=
  pointedTheory witnessCollapseModel witnessCollapseRho true
end
end MatchingLogic


