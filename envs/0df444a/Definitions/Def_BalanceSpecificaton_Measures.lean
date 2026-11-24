-- Prove2me | Definitions.Def_BalanceSpecificaton_Measures
-- name    : BalanceSpecificaton_Measures
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:34:25.505069+00:00
-- url     : https://prove2.me/theorems/a534c859-a785-4d1e-81e9-247ee61b0819
-- title:
--   Measures
-- statement:
--   Definitions and structural lemmas for Measures, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Measures.lean

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open MeasureTheory
namespace BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
def cylinder (X : ShiftSpace A) (w : Word A) (k : ℤ) : Set X.carrier :=
  {x | block x.val k w.length = w}
variable [Fintype A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]
def IsInvariant {X : ShiftSpace A} (μ : ProbabilityMeasure X.carrier) : Prop :=
  MeasurePreserving (shiftMap X) (μ : Measure X.carrier) (μ : Measure X.carrier)
def GibbsBounds {X : ShiftSpace A} (hX : X.carrier.Nonempty)
    (μ : ProbabilityMeasure X.carrier) (K : ℝ) : Prop :=
  0 < K ∧ ∀ w ∈ language X,
    1 / K ≤ (μ : Measure X.carrier).real (cylinder X w 0) *
      Real.exp ((w.length : ℝ) * entropy X hX) ∧
    (μ : Measure X.carrier).real (cylinder X w 0) *
      Real.exp ((w.length : ℝ) * entropy X hX) ≤ K
def IsGibbsMeasure {X : ShiftSpace A} (hX : X.carrier.Nonempty)
    (μ : ProbabilityMeasure X.carrier) : Prop :=
  IsInvariant μ ∧ ∃ K : ℝ, GibbsBounds hX μ K
end BalanceSpecification


