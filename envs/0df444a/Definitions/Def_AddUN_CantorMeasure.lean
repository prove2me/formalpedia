-- Prove2me | Definitions.Def_AddUN_CantorMeasure
-- name    : AddUN_CantorMeasure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:21:31.522038+00:00
-- url     : https://prove2.me/theorems/ce21b564-6776-48ca-a462-5f305343fee5
-- title:
--   Cantor Measure
-- statement:
--   Definitions and structural lemmas for Cantor Measure, from VictorLiwentao (VictorLiwentao/open-logic-24-add-un; see pinned Apache-2.0 LICENSE and source headers)'s pinned Additivity of universally null sets and Goto Question 6.3 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/CantorMeasure.lean

module
public import Definitions.Def_AddUN_UniversallyNull
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ClopenBox
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Set Filter Topology TopologicalSpace
open scoped ENNReal
namespace MeasureTheory
def flip (i : ℕ) (w : ℕ → Bool) : ℕ → Bool := fun j ↦ if j = i then !w j else w j
def Determined (s : Set ℕ) (E : Set (ℕ → Bool)) : Prop :=
  ∀ ⦃w w' : ℕ → Bool⦄, (∀ i ∈ s, w i = w' i) → w ∈ E → w' ∈ E
namespace Determined
variable {s t : Set ℕ} {E F : Set (ℕ → Bool)}
end Determined
def cylinderOn (B : Finset ℕ) (v : ℕ → Bool) : Set (ℕ → Bool) := {w | ∀ i ∈ B, w i = v i}
instance : Countable (Clopens (ℕ → Bool)) :=
  Clopens.countable_iff_secondCountable.2 inferInstance
end MeasureTheory


