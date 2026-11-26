-- Prove2me | Definitions.Def_BicausalOT_MeasurableFeasibleStrategy
-- name    : BicausalOT_MeasurableFeasibleStrategy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:31:04.558705+00:00
-- url     : https://prove2.me/theorems/64cdc06e-fb65-4fb8-87f7-883658d52717
-- title:
--   Measurable Feasible Strategy
-- statement:
--   Definitions and structural lemmas for Measurable Feasible Strategy, from KT. Wu (MaxWellApexLab/BicausalOT-palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Bicausal optimal transport Bellman representation and measurable selection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MeasurableFeasibleStrategy.lean

import Definitions.Def_BicausalOT_LscBellman
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
namespace MultiPeriod
variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
  [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
variable (κμP : (t : ℕ) → XHist X t → ProbabilityMeasure (X (t + 1)))
variable (κνP : (t : ℕ) → YHist Y t → ProbabilityMeasure (Y (t + 1)))
end MultiPeriod
end


