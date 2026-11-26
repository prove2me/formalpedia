-- Prove2me | Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
-- name    : BicausalOT_DescriptiveSetTheory_CouplingsCompact
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:04:54.336318+00:00
-- url     : https://prove2.me/theorems/b2e51999-64f8-47b4-be27-8c79af45660c
-- title:
--   Couplings Compact
-- statement:
--   Definitions and structural lemmas for Couplings Compact, from KT. Wu (MaxWellApexLab/BicausalOT-palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Bicausal optimal transport Bellman representation and measurable selection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsCompact.lean

import Mathlib
set_option autoImplicit false
open MeasureTheory Topology
noncomputable section
section Translation
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
end Translation
section Couplings
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]
end Couplings
end


