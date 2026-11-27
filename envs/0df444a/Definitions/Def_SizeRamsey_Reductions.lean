-- Prove2me | Definitions.Def_SizeRamsey_Reductions
-- name    : SizeRamsey_Reductions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:19:58.521665+00:00
-- url     : https://prove2.me/theorems/b21eaa36-b4ba-5528-b5d7-0035dc8e6b7f
-- title:
--   Reductions
-- statement:
--   Definitions and structural lemmas for Reductions, from benkeene (benkeene/size-ramsey; see pinned Apache-2.0 LICENSE and source headers)'s pinned Connected size-Ramsey number of a four-edge matching versus a quadrilateral equals 17 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean

module
public import Definitions.Def_SizeRamsey_Components
public import Definitions.Def_SizeRamsey_SmallGraphs
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


