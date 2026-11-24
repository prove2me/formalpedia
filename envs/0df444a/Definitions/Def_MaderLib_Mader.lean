-- Prove2me | Definitions.Def_MaderLib_Mader
-- name    : MaderLib_Mader
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T04:52:07.458197+00:00
-- url     : https://prove2.me/theorems/27785bc6-e678-47a8-8077-f4f58e55f14c
-- title:
--   Mader
-- statement:
--   Definitions and structural lemmas for Mader, from Juan Pablo Traverso Gianini (jtraverso/mader-connectivity; see pinned Apache-2.0 LICENSE and source headers)'s pinned Mader theorem on highly connected subgraphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/Mader.lean

module
public import Mathlib
public import Definitions.Def_MaderLib_MaderSteps
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace Mader
variable {V : Type*}
def IsKConnected [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧ ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected
end Mader


