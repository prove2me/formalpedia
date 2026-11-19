-- Prove2me | Definitions.Def_DeletionCode_BipartiteSelection
-- name    : DeletionCode_BipartiteSelection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:29:07.231874+00:00
-- url     : https://prove2.me/theorems/507acd2e-10c7-46f3-9173-c950c8ee3a27
-- title:
--   Bipartite Selection
-- statement:
--   Definitions and structural lemmas for Bipartite Selection, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BipartiteSelection.lean

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega
set_option autoImplicit true
namespace DeletionCode.BipartiteSelection
open SimpleGraph
open scoped BigOperators
variable {V : Type*} (G : SimpleGraph V)
def Good (v : V) : Prop := (G.connectedComponentMk v).toSimpleGraph.Colorable 2
noncomputable def componentColor (C : G.ConnectedComponent) : C → Fin 2 := by
  classical
  exact if h : C.toSimpleGraph.Colorable 2 then fun v => h.some v else fun _ => 0
noncomputable def color (v : V) : Fin 2 :=
  componentColor G (G.connectedComponentMk v) ⟨v, rfl⟩
variable [Fintype V]
noncomputable def goodVertices : Finset V := by
  classical
  exact Finset.univ.filter (Good G)
end DeletionCode.BipartiteSelection


