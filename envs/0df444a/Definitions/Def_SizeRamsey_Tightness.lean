-- Prove2me | Definitions.Def_SizeRamsey_Tightness
-- name    : SizeRamsey_Tightness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:20:48.264703+00:00
-- url     : https://prove2.me/theorems/7292553b-8544-4ba5-aab3-ce29a8128781
-- title:
--   Tightness
-- statement:
--   Definitions and structural lemmas for Tightness, from benkeene (benkeene/size-ramsey; see pinned Apache-2.0 LICENSE and source headers)'s pinned Connected size-Ramsey number of a four-edge matching versus a quadrilateral equals 17 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Tightness.lean

module
public import Definitions.Def_SizeRamsey_Universal
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
section FiniteGraph
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
end FiniteGraph
end SizeRamsey.Plan


