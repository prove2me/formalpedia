-- Prove2me | Definitions.Def_BicausalOT_Proposition1
-- name    : BicausalOT_Proposition1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T07:58:53.869806+00:00
-- url     : https://prove2.me/theorems/1bd1a8d5-5092-4c5e-87e8-86fd5cd2ddc7
-- title:
--   Proposition1
-- statement:
--   Definitions and structural lemmas for Proposition1, from KT. Wu (MaxWellApexLab/BicausalOT-palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Bicausal optimal transport Bellman representation and measurable selection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/Proposition1.lean

import Definitions.Def_BicausalOT_Defs
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
end


