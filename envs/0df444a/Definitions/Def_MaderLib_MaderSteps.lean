-- Prove2me | Definitions.Def_MaderLib_MaderSteps
-- name    : MaderLib_MaderSteps
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T04:51:31.51081+00:00
-- url     : https://prove2.me/theorems/0cb621c7-ce7b-4d9b-bde3-fbdd8f478424
-- title:
--   Mader Steps
-- statement:
--   Definitions and structural lemmas for Mader Steps, from Juan Pablo Traverso Gianini (jtraverso/mader-connectivity; see pinned Apache-2.0 LICENSE and source headers)'s pinned Mader theorem on highly connected subgraphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/mader-connectivity/blob/b471abcdfbb303aabc1af26f4531e080729bb469/MaderLib/MaderSteps.lean

module
public import Mathlib
public import Definitions.Def_MaderLib_MaderAux
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Finset
namespace Mader
variable {V : Type*} (G : SimpleGraph V)
end Mader


