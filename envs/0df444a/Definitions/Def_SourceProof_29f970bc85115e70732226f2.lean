-- Prove2me | Definitions.Def_SourceProof_29f970bc85115e70732226f2
-- name    : SourceProof_29f970bc85115e70732226f2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:44:52.357761+00:00
-- url     : https://prove2.me/theorems/2cb5ef8e-323f-44ad-a151-1cec9d5bddd7
-- title:
--   LevyStochCalc source module: SourceProof_29f970bc85115e70732226f2
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.tendsto_energy_clampAt_sub` comes from the `LevyStochCalc.Brownian.ItoTruncate` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoTruncate_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Truncating an integrand to a bounded one

Clamping a real integrand to `[-j, j]` leaves a bounded integrand that approximates it in energy:
the clamp is `1`-Lipschitz, fixes `0`, never increases the absolute value, and converges to the
identity pointwise, so dominated convergence gives energy convergence on every window.

## Main statements

* `LevyStochCalc.clampAt` — the clamp.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_clampAt_sub` — the clamped integrand converges to
  the integrand in energy.
-/

namespace LevyStochCalc

open MeasureTheory
open scoped NNReal ENNReal Topology

section Clamp

end Clamp

namespace Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


theorem _root_.Prove2MeSourceProof.h_29f970bc85115e70732226f2 {G : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry G))
    {T : ℝ} (hq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤) :
    Filter.Tendsto (fun j : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖clampAt (j : ℝ) (G ω s) - G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) Filter.atTop (𝓝 0) := by
  have hmc : ∀ j : ℕ, Measurable (Function.uncurry fun ω s => LevyStochCalc.clampAt (j : ℝ) (G ω s)) :=
    fun j => (LevyStochCalc.continuous_clampAt (j : ℝ)).measurable.comp hm
  have hbmeas : Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := LevyStochCalc.Brownian.Ito.measurable_energyDensity hm T
  have hFmeas : ∀ j : ℕ, Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖LevyStochCalc.clampAt (j : ℝ) (G ω s) - G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    fun j => LevyStochCalc.Brownian.Ito.measurable_energyDensity ((hmc j).sub hm) T
  have hptw : ∀ (j : ℕ) (ω : Ω) (s : ℝ),
      (‖LevyStochCalc.clampAt (j : ℝ) (G ω s) - G ω s‖₊ : ℝ≥0∞) ^ 2 ≤ (‖G ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro j ω s
    have habs : |LevyStochCalc.clampAt (j : ℝ) (G ω s) - G ω s| ≤ |G ω s| :=
      LevyStochCalc.abs_clampAt_sub_le (Nat.cast_nonneg j) _
    have hle : (‖LevyStochCalc.clampAt (j : ℝ) (G ω s) - G ω s‖₊ : ℝ≥0∞) ≤ (‖G ω s‖₊ : ℝ≥0∞) := by
      refine ENNReal.coe_le_coe.mpr ?_
      rw [← NNReal.coe_le_coe]
      simpa [Real.norm_eq_abs] using habs
    gcongr
  have hinner : ∀ᵐ ω ∂P, Filter.Tendsto (fun j : ℕ => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖LevyStochCalc.clampAt (j : ℝ) (G ω s) - G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) Filter.atTop (𝓝 0) := by
    filter_upwards [MeasureTheory.ae_lt_top hbmeas hq] with ω hfin
    have hlim := MeasureTheory.tendsto_lintegral_of_dominated_convergence
      (μ := volume.restrict (Set.Icc (0 : ℝ) T))
      (F := fun (j : ℕ) (s : ℝ) => (‖LevyStochCalc.clampAt (j : ℝ) (G ω s) - G ω s‖₊ : ℝ≥0∞) ^ 2)
      (f := fun _s : ℝ => (0 : ℝ≥0∞))
      (bound := fun s => (‖G ω s‖₊ : ℝ≥0∞) ^ 2)
      (fun j => ((((LevyStochCalc.continuous_clampAt ((j : ℕ) : ℝ)).measurable.comp
          (Measurable.of_uncurry_left hm)).sub
        (Measurable.of_uncurry_left hm)).nnnorm.coe_nnreal_ennreal).pow_const 2)
      (fun j => Filter.Eventually.of_forall fun s => hptw j ω s) hfin.ne ?_
    · simpa using hlim
    · filter_upwards with s
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (LevyStochCalc.Brownian.Ito.eventually_clampAt_eq (G ω s))
      refine tendsto_atTop_of_eventually_const (i₀ := N) fun j hj => ?_
      rw [hN j hj]
      simp
  have hlim := MeasureTheory.tendsto_lintegral_of_dominated_convergence
    (μ := P)
    (F := fun (j : ℕ) (ω : Ω) => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖LevyStochCalc.clampAt (j : ℝ) (G ω s) - G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
    (f := fun _ω : Ω => (0 : ℝ≥0∞))
    (bound := fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
    hFmeas
    (fun j => Filter.Eventually.of_forall fun ω =>
      MeasureTheory.lintegral_mono fun s => hptw j ω s) hq hinner
  simpa using hlim
section Difference

open LevyStochCalc.Brownian.Multidim

variable {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

end Difference

end Brownian.Ito

end LevyStochCalc


