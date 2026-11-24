-- Prove2me | Definitions.Def_MaderLib_MaderAux
-- name    : MaderLib_MaderAux
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T04:51:02.365976+00:00
-- url     : https://prove2.me/theorems/34197503-8880-436d-a136-f417ca484e10
-- title:
--   Mader Aux
-- statement:
--   Definitions and structural lemmas for Mader Aux, from Juan Pablo Traverso Gianini (jtraverso/mader-connectivity; see pinned Apache-2.0 LICENSE and source headers)'s pinned Mader theorem on highly connected subgraphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/MaderAux.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Finset
namespace Mader
variable {V : Type*}
open Classical in
/-- Twice the number of edges of `G[S]`: the number of ordered adjacent pairs in `S`. -/
noncomputable def dbl (G : SimpleGraph V) (S : Finset V) : ℕ :=
  ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2)).card
open Classical in
/-- The number of neighbours of `v` inside `S`. -/
noncomputable def ndeg (G : SimpleGraph V) (S : Finset V) (v : V) : ℕ :=
  (S.filter (G.Adj v)).card
variable (G : SimpleGraph V)
end Mader


