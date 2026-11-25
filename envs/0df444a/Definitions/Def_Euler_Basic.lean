-- Prove2me | Definitions.Def_Euler_Basic
-- name    : Euler_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T17:24:47.276179+00:00
-- url     : https://prove2.me/theorems/0f80fcb4-5389-5e29-9899-afb28835846b
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Juan Pablo Traverso Gianini (jtraverso/euler-petersen; see pinned Apache-2.0 LICENSE and source headers)'s pinned Euler's theorem on Eulerian circuits and trails, and Petersen's 2-factor theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Basic.lean

module
public import Mathlib.Combinatorics.SimpleGraph.Trails
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace SimpleGraph
open Walk
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
end SimpleGraph


