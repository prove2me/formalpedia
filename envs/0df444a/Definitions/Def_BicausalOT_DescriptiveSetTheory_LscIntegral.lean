-- Prove2me | Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
-- name    : BicausalOT_DescriptiveSetTheory_LscIntegral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:09:00.111823+00:00
-- url     : https://prove2.me/theorems/78336c95-5034-445b-b61b-d55e66833238
-- title:
--   Lsc Integral
-- statement:
--   Definitions and structural lemmas for Lsc Integral, from KT. Wu (MaxWellApexLab/BicausalOT-palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Bicausal optimal transport Bellman representation and measurable selection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/LscIntegral.lean

import Definitions.Def_BicausalOT_DescriptiveSetTheory_LintegralLsc
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
variable {H W : Type*}
  [TopologicalSpace H] [PolishSpace H] [MeasurableSpace H] [BorelSpace H]
  [TopologicalSpace W] [PolishSpace W] [MeasurableSpace W] [BorelSpace W]
end


