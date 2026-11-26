-- Prove2me | Definitions.Def_BicausalOT_DescriptiveSetTheory_LowerSemianalytic
-- name    : BicausalOT_DescriptiveSetTheory_LowerSemianalytic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T07:59:16.279803+00:00
-- url     : https://prove2.me/theorems/2ab74342-8f5a-4916-85a7-49cda374631d
-- title:
--   Lower Semianalytic
-- statement:
--   Definitions and structural lemmas for Lower Semianalytic, from KT. Wu (MaxWellApexLab/BicausalOT-palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Bicausal optimal transport Bellman representation and measurable selection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/DescriptiveSetTheory/LowerSemianalytic.lean

import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Prod
set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
variable {X : Type*} [TopologicalSpace X]
def IsLowerSemianalytic (f : X → ENNReal) : Prop :=
  ∀ c : ENNReal, AnalyticSet {x | f x < c}
end


