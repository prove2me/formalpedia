-- Prove2me | Definitions.Def_SizeRamsey_Basic
-- name    : SizeRamsey_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:17:46.096165+00:00
-- url     : https://prove2.me/theorems/2069dad2-2886-562d-ab07-3b944727b02f
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from benkeene (benkeene/size-ramsey; see pinned Apache-2.0 LICENSE and source headers)'s pinned Connected size-Ramsey number of a four-edge matching versus a quadrilateral equals 17 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Basic.lean

module
public import Definitions.Def_SizeRamsey_Shared
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace SizeRamsey
instance {n : ℕ} (es : Finset (Fin n × Fin n)) : DecidableRel (graphOfEdges es).Adj := by
  unfold graphOfEdges
  infer_instance
instance : DecidableRel F17.Adj := by
  unfold F17
  infer_instance
end SizeRamsey
namespace SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
end SizeRamsey.Plan


