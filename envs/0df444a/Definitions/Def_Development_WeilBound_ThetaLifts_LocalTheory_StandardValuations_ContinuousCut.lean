-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut
-- name    : Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:55.580806+00:00
-- url     : https://prove2.me/theorems/2eab2805-92ca-4a45-870a-500e2f27f3e0
-- title:
--   Continuous Cut
-- statement:
--   Definitions and structural lemmas for Continuous Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/ContinuousCut.lean

import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open scoped Pointwise
namespace PositivityTheory.ThKG.Std
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {κ : Type} [Fintype κ] [DecidableEq κ]
def ind (c : k) (x : k) : ℂ := if valuation k x ≤ valuation k c then 1 else 0
def wt (P : Finset κ) (Z : κ → k) : ℂ := ∏ p, if p ∈ P then 1 else ind 1 (Z p)
def cut (P : Finset κ) (Z : κ → k) : κ → k := fun p => if p ∈ P then Z p else 0
def one (κ : Type) [Fintype κ] (Z : κ → k) : ℂ := ∏ p, ind 1 (Z p)
variable [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k]
structure IsVol (m : Measure k) : Prop where
  haar : m.IsAddHaarMeasure
  one : m {x | valuation k x ≤ valuation k 1} = 1
structure IsPsi (ψ : AddChar k ℂ) : Prop where
  cont : Continuous ψ
  norm : ∀ x, ‖ψ x‖ = 1
  cond : ∀ x, (∀ y, valuation k y ≤ 1 → ψ (x * y) = 1) ↔ valuation k x ≤ 1
end PositivityTheory.ThKG.Std


