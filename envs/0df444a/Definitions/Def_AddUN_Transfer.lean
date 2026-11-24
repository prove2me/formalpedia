-- Prove2me | Definitions.Def_AddUN_Transfer
-- name    : AddUN_Transfer
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:21:37.825164+00:00
-- url     : https://prove2.me/theorems/ccceb9c4-9d14-4b9e-b24f-de295d9e049a
-- title:
--   Transfer
-- statement:
--   Definitions and structural lemmas for Transfer, from VictorLiwentao (VictorLiwentao/open-logic-24-add-un; see pinned Apache-2.0 LICENSE and source headers)'s pinned Additivity of universally null sets and Goto Question 6.3 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/Transfer.lean

module
public import Definitions.Def_AddUN_UniversallyNull
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Set
namespace MeasureTheory
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSingletonClass Y]
end MeasureTheory


