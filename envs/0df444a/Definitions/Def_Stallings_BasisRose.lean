-- Prove2me | Definitions.Def_Stallings_BasisRose
-- name    : Stallings_BasisRose
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:06:41.049914+00:00
-- url     : https://prove2.me/theorems/8c17adec-d2b9-40c3-8ed7-fa45731d0d62
-- title:
--   Basis Rose
-- statement:
--   Definitions and structural lemmas for Basis Rose, from Arthur Freitas Ramos (Arthur742Ramos/stallings-folding; see pinned Apache-2.0 LICENSE and PROVENANCE.md)'s pinned Verified Stallings folding for finitely generated subgroups of F2 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/stallings-folding/blob/117dde0a8415d3da1787e15ad22a6223a744432d/Stallings/BasisRose.lean

import Definitions.Def_Stallings_InverseAutomaton
set_option autoImplicit true
namespace Stallings
def basisRose (S : Finset (Fin 2)) : InverseAutomaton (Fin 1) where
  base := 0
  next _ x := if x.1 ∈ S then some 0 else none
  inverse_next := by
    intro v x w h
    have hv : v = (0 : Fin 1) := Subsingleton.elim _ _
    have hw : w = (0 : Fin 1) := Subsingleton.elim _ _
    subst v
    subst w
    cases x with
    | mk i b =>
        exact h
def basisSubgroup (S : Finset (Fin 2)) : Subgroup Free :=
  Subgroup.closure (Set.image FreeGroup.of (S : Set (Fin 2)))
end Stallings


