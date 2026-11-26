-- Prove2me | Definitions.Def_C6BipartiteDomination_A9
-- name    : C6BipartiteDomination_A9
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T21:48:21.413247+00:00
-- url     : https://prove2.me/theorems/8ab89ecc-2cf7-4676-863e-31c1a6ed435f
-- title:
--   A9
-- statement:
--   Definitions and structural lemmas for A9, from shouanrenhechun and contributors (shouanrenhechun/Myproofone; see pinned Apache-2.0 LICENSE and source headers)'s pinned Bipartite domination constant c_6 = 8/15 for graphs of maximum degree at most six development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A9.lean

import Definitions.Def_C6BipartiteDomination_A8
set_option autoImplicit true
namespace C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
noncomputable def neighborhoodIn (D : Finset V) (q : V) : Finset V := by
  classical
  exact D.filter fun d => G.Adj q d
noncomputable def compensationRegion (D X : Finset V) (u w : V) : Finset V :=
  responsibilityRegion G D (X ∪ {u}) \ X
noncomputable def privateCompensation (D : Finset V) (u : V) : Finset V :=
  privateExternalNeighbors G D u
noncomputable def sharedCompensation (D X : Finset V) (u : V) : Finset V := by
  classical
  exact (Finset.univ \ D).filter fun q =>
    ∃ z ∈ X, neighborhoodIn G D q = {u, z}
end C6BipartiteDomination


