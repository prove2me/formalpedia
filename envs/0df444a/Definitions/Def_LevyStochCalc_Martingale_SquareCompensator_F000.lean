-- Prove2me | Definitions.Def_LevyStochCalc_Martingale_SquareCompensator_F000
-- name    : LevyStochCalc_Martingale_SquareCompensator_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T21:58:56.446472+00:00
-- url     : https://prove2.me/theorems/684cdd8b-210c-46be-a1d3-71093572118a
-- title:
--   LevyStochCalc source module: LevyStochCalc.Martingale.SquareCompensator
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Martingale.SquareCompensator in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Martingale.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated square of a square-integrable martingale

For a square-integrable martingale `M` and an adapted integrable process `A`, the process
`M² − A` is a martingale as soon as the increments satisfy the set-level identity
`∫_B (M_t − M_s)² = ∫_B (A_t − A_s)` for every `s ≤ t` and every `B ∈ ℱ_s`: the cross term
`∫_B M_s M_t` equals `∫_B M_s²` by the martingale property, so the identity says exactly that
`∫_B (M_t² − A_t) = ∫_B (M_s² − A_s)`.
-/

open MeasureTheory Filter

namespace LevyStochCalc.Martingale

variable {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} {ℱ : Filtration ι mΩ}
  {μ : Measure Ω} [IsFiniteMeasure μ] {M A : ι → Ω → ℝ}

/-- For a square-integrable martingale, the set integral over an `ℱ s`-measurable set of the
product `M s · M t` equals that of `M s ^ 2`. -/
lemma setIntegral_mul_eq_sq (hM : Martingale M ℱ μ) (hM2 : ∀ t, MemLp (M t) 2 μ) {s t : ι}
    (hst : s ≤ t) {B : Set Ω} (hB : MeasurableSet[ℱ s] B) :
    ∫ ω in B, M s ω * M t ω ∂μ = ∫ ω in B, (M s ω) ^ 2 ∂μ := by
  have hm : ℱ s ≤ mΩ := ℱ.le s
  have hcr : Integrable (fun ω => M s ω * M t ω) μ := (hM2 s).integrable_mul (hM2 t)
  have h_pull : μ[(fun ω => M s ω * M t ω) | ℱ s] =ᵐ[μ] fun ω => M s ω * (μ[M t | ℱ s]) ω :=
    condExp_mul_of_stronglyMeasurable_left (hM.stronglyAdapted s) hcr (hM.integrable t)
  calc ∫ ω in B, M s ω * M t ω ∂μ
      = ∫ ω in B, (μ[(fun ω => M s ω * M t ω) | ℱ s]) ω ∂μ :=
        (setIntegral_condExp hm hcr hB).symm
    _ = ∫ ω in B, M s ω * (μ[M t | ℱ s]) ω ∂μ :=
        setIntegral_congr_ae (hm B hB) (h_pull.mono fun ω h _ => h)
    _ = ∫ ω in B, M s ω * M s ω ∂μ := by
        refine setIntegral_congr_ae (hm B hB) ?_
        filter_upwards [hM.condExp_ae_eq hst] with ω h _
        rw [h]
    _ = ∫ ω in B, (M s ω) ^ 2 ∂μ := by
        refine setIntegral_congr_fun (hm B hB) fun ω _ => ?_
        ring
/-- The set integral of a squared increment of a square-integrable martingale over an
`ℱ s`-measurable set is the difference of the set integrals of the squares. -/
lemma setIntegral_increment_sq (hM : Martingale M ℱ μ) (hM2 : ∀ t, MemLp (M t) 2 μ) {s t : ι}
    (hst : s ≤ t) {B : Set Ω} (hB : MeasurableSet[ℱ s] B) :
    ∫ ω in B, (M t ω - M s ω) ^ 2 ∂μ
      = (∫ ω in B, (M t ω) ^ 2 ∂μ) - ∫ ω in B, (M s ω) ^ 2 ∂μ := by
  have hm : ℱ s ≤ mΩ := ℱ.le s
  have ht2 : IntegrableOn (fun ω => (M t ω) ^ 2) B μ := (hM2 t).integrable_sq.integrableOn
  have hs2 : IntegrableOn (fun ω => (M s ω) ^ 2) B μ := (hM2 s).integrable_sq.integrableOn
  have hcr : IntegrableOn (fun ω => M s ω * M t ω) B μ :=
    ((hM2 s).integrable_mul (hM2 t)).integrableOn
  have hexp : ∀ ω, (M t ω - M s ω) ^ 2 = (M t ω) ^ 2 - 2 * (M s ω * M t ω) + (M s ω) ^ 2 :=
    fun ω => by ring
  simp_rw [hexp]
  have h1 : IntegrableOn (fun ω => (M t ω) ^ 2 - 2 * (M s ω * M t ω)) B μ :=
    ht2.sub (hcr.const_mul 2)
  have h2 : IntegrableOn (fun ω => 2 * (M s ω * M t ω)) B μ := hcr.const_mul 2
  rw [integral_add h1 hs2, integral_sub ht2 h2, integral_const_mul,
    setIntegral_mul_eq_sq hM hM2 hst hB]
  ring
end LevyStochCalc.Martingale


