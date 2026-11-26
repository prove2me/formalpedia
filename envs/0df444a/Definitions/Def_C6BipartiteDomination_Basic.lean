-- Prove2me | Definitions.Def_C6BipartiteDomination_Basic
-- name    : C6BipartiteDomination_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T21:39:31.020887+00:00
-- url     : https://prove2.me/theorems/df809123-c7f3-5566-847a-adcb941fefbf
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from shouanrenhechun and contributors (shouanrenhechun/Myproofone; see pinned Apache-2.0 LICENSE and source headers)'s pinned Bipartite domination constant c_6 = 8/15 for graphs of maximum degree at most six development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/Basic.lean

import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Tactic
set_option autoImplicit true
namespace C6BipartiteDomination
open Finset
variable {V : Type*} [DecidableEq V]
variable (G : SimpleGraph V)
def IsBipartiteOn (D : Finset V) : Prop :=
  ∃ colour : V → Bool,
    ∀ ⦃u v⦄, u ∈ D → v ∈ D → G.Adj u v → colour u ≠ colour v
def Dominates (D : Finset V) : Prop :=
  ∀ ⦃v⦄, v ∉ D → ∃ u ∈ D, G.Adj u v
def IsBipartiteDominatingSet (D : Finset V) : Prop :=
  Dominates G D ∧ IsBipartiteOn G D
def Responsible (D X : Finset V) (v : V) : Prop :=
  v ∉ D \ X ∧ ∀ u ∈ D \ X, ¬ G.Adj u v
end C6BipartiteDomination


