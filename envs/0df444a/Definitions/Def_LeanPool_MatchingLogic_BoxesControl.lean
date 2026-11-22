-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_BoxesControl
-- name    : LeanPool_MatchingLogic_BoxesControl
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:15:17.009885+00:00
-- url     : https://prove2.me/theorems/731bae0b-65c2-4109-b273-37e08f5162ec
-- title:
--   Boxes Control
-- statement:
--   Definitions and structural lemmas for Boxes Control, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/BoxesControl.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Logic.IsEmpty.Defs
public import Mathlib.Order.BooleanAlgebra.Set
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
namespace BoxesControl
abbrev Sg : Signature := ⟨Unit, fun _ => 2⟩
abbrev SgConst : Signature := ⟨Unit, fun _ => 0⟩
abbrev Mo : Model Sg :=
  { carrier := Fin 4
    nonempty := ⟨0⟩
    interp := fun _ a =>
      if a 0 = 1 ∧ a 1 = 1 then ({0} : Set (Fin 4))
      else if a 0 = 2 ∧ a 1 = 3 then ({1} : Set (Fin 4))
      else ∅ }
abbrev e0 : Coord Sg := ⟨(), 0⟩
abbrev e1 : Coord Sg := ⟨(), 1⟩
end BoxesControl
end MatchingLogic


