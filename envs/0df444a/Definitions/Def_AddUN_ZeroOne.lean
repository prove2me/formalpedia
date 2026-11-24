-- Prove2me | Definitions.Def_AddUN_ZeroOne
-- name    : AddUN_ZeroOne
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:22:14.214704+00:00
-- url     : https://prove2.me/theorems/e13f7403-13e1-4d8b-9138-ff7980880bc5
-- title:
--   Zero One
-- statement:
--   Definitions and structural lemmas for Zero One, from VictorLiwentao (VictorLiwentao/open-logic-24-add-un; see pinned Apache-2.0 LICENSE and source headers)'s pinned Additivity of universally null sets and Goto Question 6.3 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/ZeroOne.lean

module
public import Definitions.Def_AddUN_InitialCylinder
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Set
namespace MeasureTheory
def flipSet (s : Finset ℕ) (w : ℕ → Bool) : ℕ → Bool := fun j ↦ if j ∈ s then !w j else w j
def saturation (E : Set (ℕ → Bool)) : Set (ℕ → Bool) := ⋃ s : Finset ℕ, flipSet s ⁻¹' E
end MeasureTheory


