-- Prove2me | Definitions.Def_ErdosPosaLib_EPMain
-- name    : ErdosPosaLib_EPMain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:29:38.436278+00:00
-- url     : https://prove2.me/theorems/c5d5b074-47d8-5dae-b689-e3036b0a038a
-- title:
--   EPMain
-- statement:
--   Definitions and structural lemmas for EPMain, from Juan Pablo Traverso Gianini (jtraverso/erdos-posa-cycles; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Erdos-Posa theorem for cycles development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMain.lean

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPPin
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace ErdosPosa
variable {V : Type*}
def gEP (k : ℕ) : ℕ := 64 * k * (Nat.log 2 k + 1)
end ErdosPosa


