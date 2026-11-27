-- Prove2me | Definitions.Def_SizeRamsey_Deletion
-- name    : SizeRamsey_Deletion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:18:00.107308+00:00
-- url     : https://prove2.me/theorems/93797f41-1d8f-5da0-88dc-8e0e0b0554e7
-- title:
--   Deletion
-- statement:
--   Definitions and structural lemmas for Deletion, from benkeene (benkeene/size-ramsey; see pinned Apache-2.0 LICENSE and source headers)'s pinned Connected size-Ramsey number of a four-edge matching versus a quadrilateral equals 17 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean

module
public import Definitions.Def_SizeRamsey_Basic
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
section Squares
variable {V : Type*} {W : Type*}
end Squares
section Counting
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
end Counting
section FiniteGraph
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
end FiniteGraph
end SizeRamsey.Plan


