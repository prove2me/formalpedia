-- Prove2me | solution 1 for Auto.aux_lintegral_orbit_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:55:35.488169+00:00
-- url     : https://prove2.me/submissions/bc393554-014f-49ef-9628-ae7dad51b26e

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_orbit_measurePreserving

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace Auto
theorem _root_.solution {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {n : ℕ} (S : ErgodicSystem X μ n) (k : Fin n → ℕ)
    {F : X → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F (aux_orbit S.transformation k x) ∂μ = ∫⁻ x, F x ∂μ :=
  (aux_orbit_measurePreserving S.transformation k S.measurePreserving).lintegral_comp hF
end Auto
