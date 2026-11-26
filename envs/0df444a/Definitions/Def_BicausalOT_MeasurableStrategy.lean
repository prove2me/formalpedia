-- Prove2me | Definitions.Def_BicausalOT_MeasurableStrategy
-- name    : BicausalOT_MeasurableStrategy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:12:04.656282+00:00
-- url     : https://prove2.me/theorems/415a1145-2180-5d97-848d-3640918e14c0
-- title:
--   Measurable Strategy
-- statement:
--   Definitions and structural lemmas for Measurable Strategy, from KT. Wu (MaxWellApexLab/BicausalOT-palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Bicausal optimal transport Bellman representation and measurable selection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MeasurableStrategy.lean

import Definitions.Def_BicausalOT_SemianalyticValue
import Definitions.Def_BicausalOT_DescriptiveSetTheory_EpsOptimalSelection
set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
namespace MultiPeriod
variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
  [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
variable (κμ : (t : ℕ) → XHist X t → Measure (X (t + 1)))
variable (κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)
end MultiPeriod
end


