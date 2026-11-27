-- Prove2me | Definitions.Def_SizeRamsey_ColoringBase
-- name    : SizeRamsey_ColoringBase
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:19:04.125648+00:00
-- url     : https://prove2.me/theorems/5989824c-7e91-4b4b-b7f1-7efa13cc7bd2
-- title:
--   Coloring Base
-- statement:
--   Definitions and structural lemmas for Coloring Base, from benkeene (benkeene/size-ramsey; see pinned Apache-2.0 LICENSE and source headers)'s pinned Connected size-Ramsey number of a four-edge matching versus a quadrilateral equals 17 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/ColoringBase.lean

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace SizeRamsey
def incidentRed {V : Type*} (F : SimpleGraph V) (S : Finset V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => F.Adj u v ∧ (u ∈ S ∨ v ∈ S))
end SizeRamsey
namespace SizeRamsey.Plan
end SizeRamsey.Plan
namespace SizeRamsey
end SizeRamsey


