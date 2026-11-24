-- Prove2me | Definitions.Def_BalanceSpecificaton_FactorialEntropy
-- name    : BalanceSpecificaton_FactorialEntropy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:37:32.744292+00:00
-- url     : https://prove2.me/theorems/52c26a43-1848-4e9f-898d-a58978347ff0
-- title:
--   Factorial Entropy
-- statement:
--   Definitions and structural lemmas for Factorial Entropy, from pseudorandom/balance_and_specification contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Bi-balanced symbolic shifts, variable specification and entropy development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FactorialEntropy.lean

module
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_GrowthTiling
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open scoped ENNReal
namespace BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] [DiscreteTopology A]
def languageShift (L : Set (Word A)) : ShiftSpace A := forbiddenShift Lᶜ
variable [Fintype A]
def languageEntropy (L : Set (Word A)) : EReal :=
  Filter.limsup (fun n : ℕ =>
    (((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : EReal) *
      ENNReal.log ((wordCount L (n + 1) : ℕ) : ℝ≥0∞))) Filter.atTop
end BalanceSpecification


