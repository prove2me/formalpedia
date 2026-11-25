-- Prove2me | Definitions.Def_KneserLovasz_Solution
-- name    : KneserLovasz_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:52:59.377959+00:00
-- url     : https://prove2.me/theorems/7c122424-ff4f-530c-87ec-eac9f42cb826
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Juan Pablo Traverso Gianini (jtraverso/kneser-lovasz; see pinned Apache-2.0 LICENSE and source headers)'s pinned Kneser's conjecture and the octahedral Tucker lemma development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/kneser-lovasz/blob/6699c87d87f4ddb159fc42271263fc429e63004a/Solution.lean

module
public import Mathlib
public import Definitions.Def_KneserLib_Kneser
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace KneserTheorem
def kneserGraph (n k : ℕ) : SimpleGraph {s : Finset (Fin n) // s.card = k} where
  Adj s t := s ≠ t ∧ Disjoint s.1 t.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
end KneserTheorem


