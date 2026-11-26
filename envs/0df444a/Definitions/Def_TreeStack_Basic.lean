-- Prove2me | Definitions.Def_TreeStack_Basic
-- name    : TreeStack_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T22:05:04.221223+00:00
-- url     : https://prove2.me/theorems/5ca5faa1-bcf3-5407-acc4-db9791697455
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from jfairfaxball-348 (jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees; see pinned Apache-2.0 LICENSE and README.md)'s pinned TreeStack: Csernák-Soukup stacking number equality stack(T) = estim(T) for nontrivial trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Basic.lean

import Mathlib.Combinatorics.SimpleGraph.Acyclic
set_option autoImplicit false
namespace TreeStack
abbrev Configuration (V : Type*) := V → ℕ
def mass {V : Type*} [Fintype V] (C : Configuration V) : ℕ :=
  ∑ v, C v
def support {V : Type*} (C : Configuration V) : Set V :=
  {v | 0 < C v}
structure FiniteTree (V : Type*) [Fintype V] where
  graph : SimpleGraph V
  isTree : graph.IsTree
end TreeStack


