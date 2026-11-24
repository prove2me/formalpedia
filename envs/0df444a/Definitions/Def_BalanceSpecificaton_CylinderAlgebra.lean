-- Prove2me | Definitions.Def_BalanceSpecificaton_CylinderAlgebra
-- name    : BalanceSpecificaton_CylinderAlgebra
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:35:04.854103+00:00
-- url     : https://prove2.me/theorems/db62402f-bc10-4987-91fc-8fbf84168690
-- title:
--   Cylinder Algebra
-- statement:
--   Definitions and structural lemmas for Cylinder Algebra, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CylinderAlgebra.lean

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.SetAlgebra
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open MeasureTheory Set MeasurableSpace
open scoped symmDiff ENNReal
namespace BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A]
def centeredCylinderFamily (X : ShiftSpace A) : Set (Set X.carrier) :=
  {E | ∃ n : ℕ, ∃ w : Word A, w.length = 2 * n + 1 ∧ E = cylinder X w (-(n : ℤ))}
def finiteCylinderAlgebra (X : ShiftSpace A) : Set (Set X.carrier) :=
  {E | ∃ n : ℕ, ∀ x y : X.carrier,
    block x.val (-(n : ℤ)) (2 * n + 1) = block y.val (-(n : ℤ)) (2 * n + 1) →
      (x ∈ E ↔ y ∈ E)}
variable [Fintype A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]
end BalanceSpecification


