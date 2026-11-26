-- Prove2me | Definitions.Def_BicausalOT_DescriptiveSetTheory_EpsOptimalSelection
-- name    : BicausalOT_DescriptiveSetTheory_EpsOptimalSelection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:06:10.066043+00:00
-- url     : https://prove2.me/theorems/d71ad905-9570-40eb-8f75-ac4839f3fdfa
-- title:
--   Eps Optimal Selection
-- statement:
--   Definitions and structural lemmas for Eps Optimal Selection, from KT. Wu (MaxWellApexLab/BicausalOT-palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Bicausal optimal transport Bellman representation and measurable selection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/EpsOptimalSelection.lean

import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical
noncomputable section
variable {H E : Type*} [TopologicalSpace H] [TopologicalSpace E]
namespace EpsOptimalSelection
def bandPred (ε' : ℝ≥0∞) : ℕ → ℝ≥0∞ → Prop
  | 0, v => v = ∞
  | m + 1, v => v < ((m + 1 : ℕ) : ℝ≥0∞) * ε'
end EpsOptimalSelection
end


