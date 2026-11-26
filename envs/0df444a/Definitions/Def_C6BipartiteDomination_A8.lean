-- Prove2me | Definitions.Def_C6BipartiteDomination_A8
-- name    : C6BipartiteDomination_A8
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T21:46:58.147323+00:00
-- url     : https://prove2.me/theorems/faad4859-e879-410f-b17a-92c01e5cead4
-- title:
--   A8
-- statement:
--   Definitions and structural lemmas for A8, from shouanrenhechun and contributors (shouanrenhechun/Myproofone; see pinned Apache-2.0 LICENSE and source headers)'s pinned Bipartite domination constant c_6 = 8/15 for graphs of maximum degree at most six development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A8.lean

import Definitions.Def_C6BipartiteDomination_A7
set_option autoImplicit true
namespace C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
def IsRepairVertex (D : Finset V) (w u : V) : Prop :=
  u ∈ BPart G D ∧ G.Adj w u ∧
    IsBipartiteOn G ((BPart G D).erase u ∪ {w})
def ChosenRepairRelation (D : Finset V) (w : V) (R : Finset V) (u : V) : Prop :=
  u ∈ R ∧ IsRepairVertex G D w u
end C6BipartiteDomination


