-- Prove2me | Definitions.Def_MatchingPolytope_Induction
-- name    : MatchingPolytope_Induction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:25:41.381423+00:00
-- url     : https://prove2.me/theorems/2ef28f4a-0c56-4dee-9e98-316f8cac6863
-- title:
--   Induction
-- statement:
--   Definitions and structural lemmas for Induction, from Juan Pablo Traverso Gianini (jtraverso/edmonds-matching-polytope; see pinned Apache-2.0 LICENSE and source headers)'s pinned Edmonds perfect matching polytope and matching polytope theorems development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean

module
public import Definitions.Def_MatchingPolytope_Glue
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
def Reducible [DecidableEq V] (ends : E → Sym2 V) (W : Finset V) (F : Finset E)
    (y : E → ℝ) : Prop :=
  (∃ e ∈ F, y e = 0) ∨
    ∃ S ⊆ W, Odd S.card ∧ 1 < S.card ∧ 1 < (W \ S).card ∧ ∑ e ∈ gcut ends F S, y e = 1
section Reducible
end Reducible
end MatchingPolytope.Multi


