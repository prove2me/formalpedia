-- Prove2me | Definitions.Def_BalanceSpecificaton_MaximalEntropy
-- name    : BalanceSpecificaton_MaximalEntropy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T03:09:30.510946+00:00
-- url     : https://prove2.me/theorems/488fe217-0566-4177-a4a3-c9b15f252b74
-- title:
--   Maximal Entropy
-- statement:
--   Definitions and structural lemmas for Maximal Entropy, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MaximalEntropy.lean

module
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
namespace BalanceSpecification
open MeasureTheory Filter
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
def IsMaximalEntropyMeasure (hX : X.carrier.Nonempty) (μ : ProbabilityMeasure X.carrier) : Prop :=
  ∃ hInv : IsInvariant μ, measureEntropy μ hInv = entropy X hX
def IntrinsicallyErgodic (X : ShiftSpace A) (hX : X.carrier.Nonempty) : Prop :=
  ∃! μ : ProbabilityMeasure X.carrier, IsMaximalEntropyMeasure hX μ
end BalanceSpecification


