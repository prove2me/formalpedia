-- Prove2me | solution 1 for Auto.aux_eLpNorm_orbit_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:55:54.057974+00:00
-- url     : https://prove2.me/submissions/a6183231-83b8-4460-8fdb-cab7eddf2dfc

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
    (F : X → E) (p : ℝ≥0∞) (hF : AEStronglyMeasurable F μ) :
    eLpNorm (F ∘ aux_orbit S.transformation k) p μ = eLpNorm F p μ :=
  eLpNorm_comp_measurePreserving hF
    (aux_orbit_measurePreserving S.transformation k S.measurePreserving)
end Auto
