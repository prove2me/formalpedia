-- Prove2me | Definitions.Def_AddUN_InitialCylinder
-- name    : AddUN_InitialCylinder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:22:00.179024+00:00
-- url     : https://prove2.me/theorems/ec209607-6987-4931-a419-b4ca50e0c92a
-- title:
--   Initial Cylinder
-- statement:
--   Definitions and structural lemmas for Initial Cylinder, from VictorLiwentao (VictorLiwentao/open-logic-24-add-un; see pinned Apache-2.0 LICENSE and source headers)'s pinned Additivity of universally null sets and Goto Question 6.3 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/InitialCylinder.lean

module
public import Definitions.Def_AddUN_CantorMeasure
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Set
namespace MeasureTheory
def initialCylinders : Set (Set (ℕ → Bool)) :=
  {S | ∃ (n : ℕ) (v : ℕ → Bool), S = cylinderOn (Finset.range n) v}
end MeasureTheory


