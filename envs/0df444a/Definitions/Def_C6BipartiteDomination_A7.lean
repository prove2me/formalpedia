-- Prove2me | Definitions.Def_C6BipartiteDomination_A7
-- name    : C6BipartiteDomination_A7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T21:46:00.854877+00:00
-- url     : https://prove2.me/theorems/40cae2be-3093-4634-8226-422c4322eb05
-- title:
--   A7
-- statement:
--   Definitions and structural lemmas for A7, from shouanrenhechun and contributors (shouanrenhechun/Myproofone; see pinned Apache-2.0 LICENSE and source headers)'s pinned Bipartite domination constant c_6 = 8/15 for graphs of maximum degree at most six development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean

import Definitions.Def_C6BipartiteDomination_A6
set_option autoImplicit true
namespace C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
noncomputable def supportX (D : Finset V) (w : V) : Finset V := by
  classical
  exact (Z0Part G D).filter fun z => G.Adj w z
noncomputable def supportB (D : Finset V) (w : V) : Finset V := by
  classical
  exact (BPart G D).filter fun b => G.Adj w b
end C6BipartiteDomination


