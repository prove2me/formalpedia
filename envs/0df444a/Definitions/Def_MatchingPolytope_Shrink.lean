-- Prove2me | Definitions.Def_MatchingPolytope_Shrink
-- name    : MatchingPolytope_Shrink
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:20:59.773655+00:00
-- url     : https://prove2.me/theorems/a009d995-bd55-400b-be8d-b8b5d71a0470
-- title:
--   Shrink
-- statement:
--   Definitions and structural lemmas for Shrink, from Juan Pablo Traverso Gianini (jtraverso/edmonds-matching-polytope; see pinned Apache-2.0 LICENSE and source headers)'s pinned Edmonds perfect matching polytope and matching polytope theorems development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean

module
public import Definitions.Def_MatchingPolytope_Multigraph
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingPolytope.Multi
open Finset
variable {V E : Type*}
open Classical in
/-- Edges after shrinking `R`: those not inside `R`. -/
noncomputable def shrinkF (ends : E → Sym2 V) (F : Finset E) (R : Finset V) : Finset E :=
  F.filter fun e => ∃ u ∈ ends e, u ∉ R
section NoDec
variable {ends : E → Sym2 V} {F : Finset E}
end NoDec
variable [DecidableEq V]
def collapse (R : Finset V) (r : V) (u : V) : V := if u ∈ R then r else u
def shrinkEnds (ends : E → Sym2 V) (R : Finset V) (r : V) : E → Sym2 V :=
  fun e => (ends e).map (collapse R r)
def shrinkW (W R : Finset V) (r : V) : Finset V := insert r (W \ R)
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
end MatchingPolytope.Multi


