-- Prove2me | Definitions.Def_LeanPool_ListEdgeColoringComplete_Main
-- name    : LeanPool_ListEdgeColoringComplete_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T16:36:32.00552+00:00
-- url     : https://prove2.me/theorems/247abbf0-7047-4b97-b898-c5013422e0ad
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Juan Pablo Traverso Gianini (jtraverso/haggkvist-janssen; see pinned Apache-2.0 LICENSE and source headers)'s pinned Haggkvist-Janssen bound on the list chromatic index of complete graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/haggkvist-janssen/blob/807e08bd7c480d4fae80c1b78377d23989d39ab0/LeanPool/ListEdgeColoringComplete/Main.lean

module
public import Definitions.Def_LeanPool_ListEdgeColoringComplete_Polynomial
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LeanPool.ListEdgeColoringComplete
open MvPolynomial Finset
variable {V : Type*} [DecidableEq V] {n : ℕ}
end LeanPool.ListEdgeColoringComplete


