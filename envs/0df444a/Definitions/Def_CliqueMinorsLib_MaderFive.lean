-- Prove2me | Definitions.Def_CliqueMinorsLib_MaderFive
-- name    : CliqueMinorsLib_MaderFive
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:39:19.682924+00:00
-- url     : https://prove2.me/theorems/94ea43c4-309e-4b36-8451-ee4bbe96ecae
-- title:
--   Mader Five
-- statement:
--   Definitions and structural lemmas for Mader Five, from Juan Pablo Traverso Gianini (jtraverso/hadwiger-mader; see pinned Apache-2.0 LICENSE and source headers)'s pinned Mader's theorem and Hadwiger's conjecture for t at most 4 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/MaderFive.lean

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace CliqueMinors
variable {V : Type*}
section MaderFive
open scoped Classical
variable [Fintype V]
end MaderFive
end CliqueMinors


