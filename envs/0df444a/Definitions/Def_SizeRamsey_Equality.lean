-- Prove2me | Definitions.Def_SizeRamsey_Equality
-- name    : SizeRamsey_Equality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:22:32.829211+00:00
-- url     : https://prove2.me/theorems/4a449549-8927-5338-ae97-819298633163
-- title:
--   Equality
-- statement:
--   Definitions and structural lemmas for Equality, from benkeene (benkeene/size-ramsey; see pinned Apache-2.0 LICENSE and source headers)'s pinned Connected size-Ramsey number of a four-edge matching versus a quadrilateral equals 17 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Equality.lean

module
public import Definitions.Def_SizeRamsey_Equality_DegreeFour
public import Definitions.Def_SizeRamsey_Equality_Mixed
public import Definitions.Def_SizeRamsey_Equality_Cubic
public import Definitions.Def_SizeRamsey_Equality_TwoRegular
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace SizeRamsey.Plan
universe u
attribute [local instance] Classical.propDecidable
end SizeRamsey.Plan
namespace SizeRamsey.Proof
end SizeRamsey.Proof


