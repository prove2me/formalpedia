-- Prove2me | solution 1 for Auto.aux_memLp_orbit_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:55:57.40296+00:00
-- url     : https://prove2.me/submissions/ea043a5c-0ef4-4fa6-a6b9-f2c2bebc9236

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
    {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    {F : X → E} {p : ℝ≥0∞} (hF : MemLp F p μ) :
    MemLp (F ∘ aux_orbit S.transformation k) p μ :=
  hF.comp_measurePreserving
    (aux_orbit_measurePreserving S.transformation k S.measurePreserving)
end Auto
