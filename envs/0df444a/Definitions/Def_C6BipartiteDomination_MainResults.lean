-- Prove2me | Definitions.Def_C6BipartiteDomination_MainResults
-- name    : C6BipartiteDomination_MainResults
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T21:58:34.625839+00:00
-- url     : https://prove2.me/theorems/16d61037-029b-53a1-bb71-36fb33d04e32
-- title:
--   Main Results
-- statement:
--   Definitions and structural lemmas for Main Results, from shouanrenhechun and contributors (shouanrenhechun/Myproofone; see pinned Apache-2.0 LICENSE and source headers)'s pinned Bipartite domination constant c_6 = 8/15 for graphs of maximum degree at most six development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/MainResults.lean

import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
namespace C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
noncomputable def liftFinsetToSubtype (S E : Finset V)
    (hES : E ⊆ S) : Finset {v // v ∈ S} := by
  classical
  exact E.attach.image fun x => (⟨x.1, hES x.2⟩ : {v // v ∈ S})
noncomputable def projectFinsetFromSubtype {S : Finset V}
    (F : Finset {v // v ∈ S}) : Finset V := by
  classical
  exact F.image Subtype.val
end C6BipartiteDomination


