-- Prove2me | Definitions.Def_ErdosPosaLib_EPShort
-- name    : ErdosPosaLib_EPShort
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:22:43.044335+00:00
-- url     : https://prove2.me/theorems/aaa1c8c0-bfcf-45f5-aaa2-103c559a1672
-- title:
--   EPShort
-- statement:
--   Definitions and structural lemmas for EPShort, from Juan Pablo Traverso Gianini (jtraverso/erdos-posa-cycles; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Erdos-Posa theorem for cycles development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPShort.lean

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMoore
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph
namespace ErdosPosa
variable {V : Type*}
def suppress (H : SimpleGraph V) (x a b : V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u w => (H.Adj u w ∧ u ≠ x ∧ w ≠ x) ∨ (u = a ∧ w = b))
end ErdosPosa


