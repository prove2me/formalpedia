-- Prove2me | Definitions.Def_BrooksLib_BrooksLow
-- name    : BrooksLib_BrooksLow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:32:22.023802+00:00
-- url     : https://prove2.me/theorems/32eac6e9-7f63-44d4-9f7a-7086f786fa96
-- title:
--   Brooks Low
-- statement:
--   Definitions and structural lemmas for Brooks Low, from Juan Pablo Traverso Gianini (jtraverso/brooks; see pinned Apache-2.0 LICENSE and source headers)'s pinned Erdos-Rubin-Taylor degree-choosability, block-cut trees, and Brooks' theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksLow.lean

module
public import Definitions.Def_BrooksLib_BrooksCore
public import Definitions.Def_BrooksLib_Cycle
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Finset
namespace BrooksTheorem
namespace Aux
variable {V : Type*} [Fintype V]
end Aux
end BrooksTheorem


