-- Prove2me | Definitions.Def_BicausalOT_FeasNonempty
-- name    : BicausalOT_FeasNonempty
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:10:32.505016+00:00
-- url     : https://prove2.me/theorems/851ee26d-25b6-42a8-99dc-4ec1e09abb0c
-- title:
--   Feas Nonempty
-- statement:
--   Definitions and structural lemmas for Feas Nonempty, from KT. Wu (MaxWellApexLab/BicausalOT-palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Bicausal optimal transport Bellman representation and measurable selection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/FeasNonempty.lean

import Definitions.Def_BicausalOT_MultiPeriod
import Definitions.Def_BicausalOT_ValueRepresentation
import Mathlib.MeasureTheory.Measure.Prod
set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
section OneStep
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
variable (c₀ : X₀ × Y₀ → ENNReal) (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)
end OneStep
namespace MultiPeriod
variable {X Y : ℕ → Type*}
variable [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
variable (κμ : (t : ℕ) → XHist X t → Measure (X (t + 1)))
variable (κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)
end MultiPeriod
end


