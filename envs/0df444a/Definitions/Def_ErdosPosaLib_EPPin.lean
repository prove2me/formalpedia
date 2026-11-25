-- Prove2me | Definitions.Def_ErdosPosaLib_EPPin
-- name    : ErdosPosaLib_EPPin
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:29:08.37949+00:00
-- url     : https://prove2.me/theorems/04f0cb2e-3ef1-4a37-898b-932a94777e27
-- title:
--   EPPin
-- statement:
--   Definitions and structural lemmas for EPPin, from Juan Pablo Traverso Gianini (jtraverso/erdos-posa-cycles; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Erdos-Posa theorem for cycles development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPin.lean

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMaximal
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace ErdosPosa
variable {V : Type*}
variable [Finite V] {G H : SimpleGraph V}
end ErdosPosa


