-- Prove2me | Definitions.Def_SourceProof_c420c5d06462fb990bdab16f
-- name    : SourceProof_c420c5d06462fb990bdab16f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:10:35.718376+00:00
-- url     : https://prove2.me/theorems/226c9080-593d-4bc6-b6fc-2e3608fb65c6
-- title:
--   LevyStochCalc source module: SourceProof_c420c5d06462fb990bdab16f
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.eventually_gridStop_lt` comes from the `LevyStochCalc.Brownian.ItoLocality` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoLocality_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The local property of the Itô integral

Cutting the integrand off at a stopping time `τ` does not change the integral at a time the
stopping time has not yet reached. The stopping time is approximated from above by the
finite-range stopping times that stop at the first point of a uniform grid strictly beyond it,
for which the finite-range optional stopping identity applies directly; the approximation
converges in energy, and an `L²` squeeze removes the approximation.

## Main statements

* `LevyStochCalc.Brownian.Ito.stepStop`, `gridStop` — the two-valued and the grid stopping times.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_eq_of_le` — the local property.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_pos` — the integral to a
  positive time sees the integrand only at positive times.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_le` — two integrands agreeing
  up to a stopping time have the same integral where that time has not been reached.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (τ : Ω → WithTop ℝ)

section GridStop

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_c420c5d06462fb990bdab16f {t : ℝ} (ht : 0 < t) (ω : Ω) {s : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (hτs : τ ω < ((s : ℝ) : WithTop ℝ)) :
    ∀ᶠ n in Filter.atTop, gridStop τ t n ω < ((s : ℝ) : WithTop ℝ) := by
  have hne : τ ω ≠ ⊤ := by
    intro h
    rw [h] at hτs
    exact absurd hτs (by simp)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  have hrs : r < s := by
    rw [← hr] at hτs
    exact_mod_cast hτs
  set u : ℝ := max r 0 with hu
  have hu0 : 0 ≤ u := le_max_right r 0
  have hus : u < s := max_lt hrs hs
  have hpos : 0 < s - u := sub_pos.mpr hus
  obtain ⟨N, hN⟩ := exists_nat_gt (t / (s - u))
  refine Filter.eventually_atTop.mpr ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans (le_max_left N 1) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hstep : t / (n : ℝ) < s - u := by
    have h1 : t / (s - u) < (n : ℝ) := lt_of_lt_of_le hN hnN
    rw [div_lt_iff₀ hnpos]
    rw [div_lt_iff₀ hpos] at h1
    linarith
  set j : ℕ := ⌊u * (n : ℝ) / t⌋₊ + 1 with hj
  have hfl : (⌊u * (n : ℝ) / t⌋₊ : ℝ) ≤ u * (n : ℝ) / t :=
    Nat.floor_le (by positivity)
  have hfl' : u * (n : ℝ) / t < (⌊u * (n : ℝ) / t⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hjc : (j : ℝ) = (⌊u * (n : ℝ) / t⌋₊ : ℝ) + 1 := by
    rw [hj]
    push_cast
    ring
  have hgu : u < LevyStochCalc.Brownian.Ito.gridPt t n j := by
    rw [LevyStochCalc.Brownian.Ito.gridPt, lt_div_iff₀ hnpos, hjc]
    have := hfl'
    rw [div_lt_iff₀ ht] at this
    nlinarith
  have hgs : LevyStochCalc.Brownian.Ito.gridPt t n j < s := by
    have hle : LevyStochCalc.Brownian.Ito.gridPt t n j ≤ u + t / (n : ℝ) := by
      rw [LevyStochCalc.Brownian.Ito.gridPt, hjc, div_le_iff₀ hnpos]
      have := hfl
      rw [le_div_iff₀ ht] at this
      field_simp
      nlinarith
    linarith
  have hjn : j ≤ n := by
    by_contra hcon
    push Not at hcon
    have : t ≤ LevyStochCalc.Brownian.Ito.gridPt t n j := by
      rw [LevyStochCalc.Brownian.Ito.gridPt, le_div_iff₀ hnpos]
      have : (n : ℝ) ≤ (j : ℝ) := by exact_mod_cast hcon.le
      nlinarith
    linarith
  have hstep' : LevyStochCalc.Brownian.Ito.stepStop τ (LevyStochCalc.Brownian.Ito.gridPt t n j) ω = ((LevyStochCalc.Brownian.Ito.gridPt t n j : ℝ) : WithTop ℝ) := by
    rw [LevyStochCalc.Brownian.Ito.stepStop, if_neg]
    rw [← hr]
    intro hcon
    have : LevyStochCalc.Brownian.Ito.gridPt t n j ≤ r := by exact_mod_cast hcon
    have : LevyStochCalc.Brownian.Ito.gridPt t n j ≤ u := le_trans this (le_max_left r 0)
    linarith
  calc LevyStochCalc.Brownian.Ito.gridStop τ t n ω ≤ LevyStochCalc.Brownian.Ito.stepStop τ (LevyStochCalc.Brownian.Ito.gridPt t n j) ω :=
        (LevyStochCalc.Brownian.Ito.gridStopAux_le_iff τ t n n ω _).mpr ⟨j, hjn, le_rfl⟩
    _ = ((LevyStochCalc.Brownian.Ito.gridPt t n j : ℝ) : WithTop ℝ) := hstep'
    _ < ((s : ℝ) : WithTop ℝ) := by exact_mod_cast hgs
end GridStop

section Local

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end Local

end LevyStochCalc.Brownian.Ito


