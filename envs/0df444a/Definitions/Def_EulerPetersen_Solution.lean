-- Prove2me | Definitions.Def_EulerPetersen_Solution
-- name    : EulerPetersen_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T17:46:58.8319+00:00
-- url     : https://prove2.me/theorems/a91de4f8-71df-4462-849b-cad16338f84e
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Juan Pablo Traverso Gianini (jtraverso/euler-petersen; see pinned Apache-2.0 LICENSE and source headers)'s pinned Euler's theorem on Eulerian circuits and trails, and Petersen's 2-factor theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Solution.lean

module
public import Definitions.Def_Euler
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace EulerPetersen
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
end EulerPetersen


