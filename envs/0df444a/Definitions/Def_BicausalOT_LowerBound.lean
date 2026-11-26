-- Prove2me | Definitions.Def_BicausalOT_LowerBound
-- name    : BicausalOT_LowerBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T07:58:54.901948+00:00
-- url     : https://prove2.me/theorems/03031f74-f862-4cee-8932-d32e24d2afef
-- title:
--   Lower Bound
-- statement:
--   Definitions and structural lemmas for Lower Bound, from KT. Wu (MaxWellApexLab/BicausalOT-palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Bicausal optimal transport Bellman representation and measurable selection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/LowerBound.lean

import Definitions.Def_BicausalOT_Defs
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
variable (c₀ : X₀ × Y₀ → ENNReal) (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)
end


