-- Prove2me | Definitions.Def_C6BipartiteDomination_A4
-- name    : C6BipartiteDomination_A4
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T21:41:48.23883+00:00
-- url     : https://prove2.me/theorems/2d74880f-561f-4c87-bc76-05f7d270d9fa
-- title:
--   A4
-- statement:
--   Definitions and structural lemmas for A4, from shouanrenhechun and contributors (shouanrenhechun/Myproofone; see pinned Apache-2.0 LICENSE and source headers)'s pinned Bipartite domination constant c_6 = 8/15 for graphs of maximum degree at most six development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A4.lean

import Definitions.Def_C6BipartiteDomination_A3
set_option autoImplicit true
namespace C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
noncomputable def internalArcs (D : Finset V) : Finset (V × V) := by
  classical
  exact Finset.univ.filter fun p => p.1 ∈ D ∧ p.2 ∈ D ∧ G.Adj p.1 p.2
def CanonicalTwoLevelOptimum (D : Finset V) : Prop :=
  IsBipartiteDominatingSet G D ∧
    (∀ E, IsBipartiteDominatingSet G E → D.card ≤ E.card) ∧
    (∀ E, IsBipartiteDominatingSet G E → E.card = D.card →
      (internalArcs G D).card ≤ (internalArcs G E).card)
def NonisolatedIn (D : Finset V) (b : V) : Prop :=
  b ∈ D ∧ ∃ u ∈ D, G.Adj b u
noncomputable def privateExternalNeighbors (D : Finset V) (b : V) : Finset V := by
  classical
  exact (Finset.univ \ D).filter fun w => ∀ u ∈ D, G.Adj u w ↔ u = b
end C6BipartiteDomination


