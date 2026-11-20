-- Prove2me | Definitions.Def_SourceProof_a157dd277ff36750db5f28f0
-- name    : SourceProof_a157dd277ff36750db5f28f0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:38:45.643491+00:00
-- url     : https://prove2.me/theorems/f7fe65b7-c7f5-495a-beb3-d8156966ae32
-- title:
--   LevyStochCalc source module: SourceProof_a157dd277ff36750db5f28f0
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Martingale.brownian_martingale_natural` comes from the `LevyStochCalc.Brownian.MartingaleQuadVar` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_MartingaleQuadVar_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian martingale property and quadratic variation

Brownian motion is a martingale for its natural filtration, hence for any filtration to which it
is adapted with independent increments, and its quadratic variation is `⟨W⟩_t = t`: the process
`W_t² − t` is again a martingale. The identity `(dW)² = dt` it records is the second-order term
of the Itô formula.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Martingale

universe u

section MartingaleAndQuadVar
variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_a157dd277ff36750db5f28f0
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) :
    MeasureTheory.Martingale (fun t : ℝ => W.W t) (naturalFiltration W) P := by
  refine ⟨?_, ?_⟩
  · -- StronglyAdapted: by Filtration.stronglyAdapted_natural
    exact MeasureTheory.Filtration.stronglyAdapted_natural _
  · -- Cond-exp identity: 𝔼[W_t | ℱ_s] = W_s for s ≤ t.
    intro s t hst
    by_cases hst_eq : s = t
    · -- s = t: 𝔼[W_t | ℱ_t] = W_t (W_t is `ℱ_t`-measurable).
      subst hst_eq
      -- Use condExp_of_stronglyMeasurable.
      have h_le : (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq s ≤ ‹MeasurableSpace Ω› :=
        (LevyStochCalc.Brownian.Martingale.naturalFiltration W).le' s
      have h_meas := MeasureTheory.Filtration.stronglyAdapted_natural
        (u := W.W) (fun u => (W.measurable_eval u).stronglyMeasurable) s
      -- Integrability of W.W s under P (Gaussian moments).
      -- Using `s = t`, but we don't have `0 ≤ s`. The natural filtration is
      -- defined for all `t : ℝ`; we still need integrability.
      have h_int : MeasureTheory.Integrable (W.W s) P :=
        _root_.Prove2MeSourceProof.h_15e9b29820f9078d07baa577 W s
      -- SigmaFinite trim instance derives from `IsFiniteMeasure P`.
      have h_eq := MeasureTheory.condExp_of_stronglyMeasurable h_le h_meas h_int
      -- Convert `=` to `=ᵐ[P]` (regular equality implies a.e. equality).
      rw [h_eq]
    · -- s < t: decompose W_t = W_s + (W_t − W_s).
      -- 𝔼[W_t | ℱ_s] = 𝔼[W_s | ℱ_s] + 𝔼[W_t − W_s | ℱ_s]
      -- = W_s (condExp_of_stronglyMeasurable) + 0 (condExp_increment_eq_zero_aux)
      -- = W_s.
      have hst_lt : s < t := lt_of_le_of_ne hst hst_eq
      by_cases hs_nn : 0 ≤ s
      swap
      · -- s < 0: handle subcases on t.
        push Not at hs_nn
        by_cases ht_nn : 0 ≤ t
        · -- s < 0 ≤ t: tower through F_0.
          -- F_s ≤ F_0 (filtration monotone). P[P[W_t | F_0] | F_s] = P[W_t | F_s].
          -- P[W_t | F_0] = 0 a.s. (brownian_martingale_zero_aux).
          -- P[0 | F_s] = 0 a.s. So P[W_t | F_s] = 0 = W_s a.s.
          have h_le_F : (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq s ≤ (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq 0 :=
            (LevyStochCalc.Brownian.Martingale.naturalFiltration W).mono hs_nn.le
          have h_le_F0 : (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq 0 ≤ ‹MeasurableSpace Ω› :=
            (LevyStochCalc.Brownian.Martingale.naturalFiltration W).le' 0
          have h_tower := MeasureTheory.condExp_condExp_of_le
            (μ := P) (f := W.W t) h_le_F h_le_F0
          have h_inner_zero := LevyStochCalc.Brownian.Martingale.brownian_martingale_zero_aux W ht_nn
          -- Apply condExp_congr_ae to inner equality
          have h_outer_zero :
              P[P[W.W t | (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq 0] | (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq s]
                =ᵐ[P] P[(fun _ => 0 : Ω → ℝ) | (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq s] := by
            exact MeasureTheory.condExp_congr_ae h_inner_zero
          have h_zero_inner := MeasureTheory.condExp_const (μ := P)
            ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).le' s) (0 : ℝ)
          have hWs_zero : ∀ᵐ ω ∂P, W.W s ω = 0 := W.negative_zero s hs_nn
          filter_upwards [h_tower, h_outer_zero, hWs_zero]
            with ω h_tower_ω h_outer_ω hWs_ω
          rw [← h_tower_ω, h_outer_ω, h_zero_inner]
          change (0 : ℝ) = W.W s ω
          rw [hWs_ω]
        · -- s < t < 0: both W_s and W_t are 0 a.s.
          push Not at ht_nn
          have hWs_zero : ∀ᵐ ω ∂P, W.W s ω = 0 := W.negative_zero s hs_nn
          have hWt_zero : ∀ᵐ ω ∂P, W.W t ω = 0 := W.negative_zero t ht_nn
          have h_Wt_ae_zero : (W.W t : Ω → ℝ) =ᵐ[P] (fun _ => 0 : Ω → ℝ) := by
            filter_upwards [hWt_zero] with ω hω; exact hω
          have h_eq := MeasureTheory.condExp_congr_ae (m := (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq s)
            (μ := P) h_Wt_ae_zero
          have h_const := MeasureTheory.condExp_const (μ := P)
            ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).le' s) (0 : ℝ)
          filter_upwards [h_eq, hWs_zero] with ω h_eq_ω hWs_ω
          rw [h_eq_ω, h_const]
          change (0 : ℝ) = W.W s ω
          rw [hWs_ω]
      -- Now 0 ≤ s < t.
      have h_int_s : MeasureTheory.Integrable (W.W s) P :=
        _root_.Prove2MeSourceProof.h_15e9b29820f9078d07baa577 W s
      have h_int_t : MeasureTheory.Integrable (W.W t) P :=
        _root_.Prove2MeSourceProof.h_15e9b29820f9078d07baa577 W t
      have h_inc_int : MeasureTheory.Integrable (fun ω => W.W t ω - W.W s ω) P :=
        h_int_t.sub h_int_s
      have h_inc_zero := LevyStochCalc.Brownian.Martingale.condExp_increment_eq_zero_aux W hs_nn hst_lt
      have h_le : (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq s ≤ ‹MeasurableSpace Ω› :=
        (LevyStochCalc.Brownian.Martingale.naturalFiltration W).le' s
      have h_adapt_s :=
        MeasureTheory.Filtration.stronglyAdapted_natural
          (u := W.W) (fun u => (W.measurable_eval u).stronglyMeasurable) s
      have h_decomp : (W.W t : Ω → ℝ) = W.W s + (fun ω => W.W t ω - W.W s ω) := by
        funext ω; simp [Pi.add_apply]
      change P[W.W t | (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq s] =ᶠ[ae P] W.W s
      rw [h_decomp]
      have h_add := MeasureTheory.condExp_add h_int_s h_inc_int
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq s)
      have h_self := MeasureTheory.condExp_of_stronglyMeasurable h_le h_adapt_s h_int_s
      filter_upwards [h_add, h_inc_zero] with ω h_add_ω h_zero_ω
      rw [h_add_ω, Pi.add_apply, h_zero_ω, h_self]
      change W.W s ω + 0 = W.W s ω
      ring
end MartingaleAndQuadVar

end LevyStochCalc.Brownian.Martingale


