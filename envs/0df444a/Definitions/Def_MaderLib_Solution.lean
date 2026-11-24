-- Prove2me | Definitions.Def_MaderLib_Solution
-- name    : MaderLib_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T04:52:45.351683+00:00
-- url     : https://prove2.me/theorems/2edb6a63-39a5-4452-affa-f43aaa8a7f4f
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Juan Pablo Traverso Gianini (jtraverso/mader-connectivity; see pinned Apache-2.0 LICENSE and source headers)'s pinned Mader theorem on highly connected subgraphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/Solution.lean

module
public import Mathlib
public import Definitions.Def_MaderLib_Mader
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace MaderTheorem
variable {V : Type*}
def IsKConnected [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧ ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected
end MaderTheorem


