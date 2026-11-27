-- Prove2me | Definitions.Def_MatchingPolytope_Glue
-- name    : MatchingPolytope_Glue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:23:23.164625+00:00
-- url     : https://prove2.me/theorems/6f65a273-ae65-4439-9962-b69ecc90acbc
-- title:
--   Glue
-- statement:
--   Definitions and structural lemmas for Glue, from Juan Pablo Traverso Gianini (jtraverso/edmonds-matching-polytope; see pinned Apache-2.0 LICENSE and source headers)'s pinned Edmonds perfect matching polytope and matching polytope theorems development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean

module
public import Definitions.Def_MatchingPolytope_Shrink
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingPolytope.Multi
open Finset
variable {V E : Type*}
noncomputable def gw (C : Finset E) (x : E → ℝ) (w1 w2 : Finset E → ℝ)
    (p : Finset E × Finset E) : ℝ :=
  ∑ g ∈ C, chi p.1 g * chi p.2 g * w1 p.1 * w2 p.2 / x g
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
variable [DecidableEq V]
end MatchingPolytope.Multi


