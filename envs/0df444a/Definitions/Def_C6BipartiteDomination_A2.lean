-- Prove2me | Definitions.Def_C6BipartiteDomination_A2
-- name    : C6BipartiteDomination_A2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T21:39:54.708679+00:00
-- url     : https://prove2.me/theorems/b77f2644-3c53-47bd-98c2-359915a68333
-- title:
--   A2
-- statement:
--   Definitions and structural lemmas for A2, from shouanrenhechun and contributors (shouanrenhechun/Myproofone; see pinned Apache-2.0 LICENSE and source headers)'s pinned Bipartite domination constant c_6 = 8/15 for graphs of maximum degree at most six development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A2.lean

import Definitions.Def_C6BipartiteDomination_Basic
set_option autoImplicit true
namespace C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
noncomputable def responsibilityRegion (D X : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter (Responsible G D X)
def BipartiteDominatingOn (R Y : Finset V) : Prop :=
  Y ⊆ R ∧
    (∀ ⦃v⦄, v ∈ R → v ∉ Y → ∃ y ∈ Y, G.Adj y v) ∧
    IsBipartiteOn G Y
def MinimumBipartiteDominatingSet (D : Finset V) : Prop :=
  IsBipartiteDominatingSet G D ∧
    ∀ E, IsBipartiteDominatingSet G E → D.card ≤ E.card
def MinimumBipartiteDominatingOn (R Y : Finset V) : Prop :=
  BipartiteDominatingOn G R Y ∧
    ∀ E, BipartiteDominatingOn G R E → Y.card ≤ E.card
def IsolatedSubset (D X : Finset V) : Prop :=
  X ⊆ D ∧ ∀ ⦃x u⦄, x ∈ X → u ∈ D → ¬ G.Adj x u
end C6BipartiteDomination


