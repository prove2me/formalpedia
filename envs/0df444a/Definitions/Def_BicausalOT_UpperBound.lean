-- Prove2me | Definitions.Def_BicausalOT_UpperBound
-- name    : BicausalOT_UpperBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T07:59:13.897295+00:00
-- url     : https://prove2.me/theorems/67f89198-4f52-4787-8fd6-1b8b3e196c8a
-- title:
--   Upper Bound
-- statement:
--   Definitions and structural lemmas for Upper Bound, from KT. Wu (MaxWellApexLab/BicausalOT-palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Bicausal optimal transport Bellman representation and measurable selection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/UpperBound.lean

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_DescriptiveSetTheory_JankovVonNeumann
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
variable (c₀ : X₀ × Y₀ → ENNReal) (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)
end


