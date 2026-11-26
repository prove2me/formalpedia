-- Prove2me | Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
-- name    : BicausalOT_DescriptiveSetTheory_CouplingsUHC
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:08:14.247117+00:00
-- url     : https://prove2.me/theorems/f6f7b79b-377b-5265-b40a-579a3f1e92e1
-- title:
--   Couplings UHC
-- statement:
--   Definitions and structural lemmas for Couplings UHC, from KT. Wu (MaxWellApexLab/BicausalOT-palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Bicausal optimal transport Bellman representation and measurable selection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/CouplingsUHC.lean

import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
set_option autoImplicit false
open MeasureTheory Set Filter Topology
noncomputable section
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]
end


