-- Prove2me | Definitions.Def_C6BipartiteDomination_A3
-- name    : C6BipartiteDomination_A3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T21:40:53.705182+00:00
-- url     : https://prove2.me/theorems/7c7afb15-0868-49d7-9551-fece2e795140
-- title:
--   A3
-- statement:
--   Definitions and structural lemmas for A3, from shouanrenhechun and contributors (shouanrenhechun/Myproofone; see pinned Apache-2.0 LICENSE and source headers)'s pinned Bipartite domination constant c_6 = 8/15 for graphs of maximum degree at most six development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean

import Definitions.Def_C6BipartiteDomination_A2
set_option autoImplicit true
namespace C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
def HasNoIsolatedVertices : Prop := ∀ v, ∃ u, G.Adj v u
def Independent (D : Finset V) : Prop :=
  ∀ ⦃u v⦄, u ∈ D → v ∈ D → G.Adj u v → False
noncomputable def neighborsIn (S T : Finset V) : Finset V := by
  classical
  exact T.filter fun w => ∃ v ∈ S, G.Adj v w
end C6BipartiteDomination


