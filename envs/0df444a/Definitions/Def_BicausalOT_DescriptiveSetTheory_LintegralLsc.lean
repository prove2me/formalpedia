-- Prove2me | Definitions.Def_BicausalOT_DescriptiveSetTheory_LintegralLsc
-- name    : BicausalOT_DescriptiveSetTheory_LintegralLsc
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:04:54.400482+00:00
-- url     : https://prove2.me/theorems/5b73e00d-043c-43e4-9624-cbc1a86e1b97
-- title:
--   Lintegral Lsc
-- statement:
--   Definitions and structural lemmas for Lintegral Lsc, from KT. Wu (MaxWellApexLab/BicausalOT-palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Bicausal optimal transport Bellman representation and measurable selection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/LintegralLsc.lean

import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set Topology
open scoped ENNReal
section SequentialBound
variable {W : Type*} [MeasurableSpace W] [TopologicalSpace W] [OpensMeasurableSpace W]
end SequentialBound


