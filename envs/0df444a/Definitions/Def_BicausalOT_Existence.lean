-- Prove2me | Definitions.Def_BicausalOT_Existence
-- name    : BicausalOT_Existence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T07:59:16.346282+00:00
-- url     : https://prove2.me/theorems/92d5ad3c-e7d7-5b61-ba27-de4eaa19f78e
-- title:
--   Existence
-- statement:
--   Definitions and structural lemmas for Existence, from KT. Wu (MaxWellApexLab/BicausalOT-palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Bicausal optimal transport Bellman representation and measurable selection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/Existence.lean

import Definitions.Def_BicausalOT_Defs
import Mathlib.Topology.Semicontinuity.Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
variable (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)
end


