-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChartDensityChangeFormula
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChartDensityChangeFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:43.607686+00:00
-- url     : https://prove2.me/theorems/90d02c71-e9ca-48cc-8f24-16de0b4377f2
-- title:
--   Chart Density Change Formula
-- statement:
--   Definitions and structural lemmas for Chart Density Change Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ChartDensityChangeFormula.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ChartMeasApplyOfSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Topology
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal
namespace GlobalTheory.GlueCover
open GlobalTheory.ChartGlue
variable {n : ℕ}
section Null
variable {X ι : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
end Null
section Cover
variable {A B ι κ : Type} [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B]
  [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace B] [BorelSpace B]
  {e : ι → OpenPartialHomeomorph A (V n)} {ρ : ι → A → ℝ≥0∞}
  {e' : κ → OpenPartialHomeomorph B (V n)} {ρ' : κ → B → ℝ≥0∞} {m : B → A}
end Cover
end GlobalTheory.GlueCover


