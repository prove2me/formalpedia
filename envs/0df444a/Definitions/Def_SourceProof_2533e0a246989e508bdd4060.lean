-- Prove2me | Definitions.Def_SourceProof_2533e0a246989e508bdd4060
-- name    : SourceProof_2533e0a246989e508bdd4060
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:21:31.020901+00:00
-- url     : https://prove2.me/theorems/f85e68f0-d7f5-4660-a335-28d2ed9132b4
-- title:
--   LevyStochCalc source module: SourceProof_2533e0a246989e508bdd4060
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.exists_unifGrid_cell` comes from the `LevyStochCalc.Brownian.ItoFormulaGrid` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaGrid_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The uniform grid and the third-moment remainder

The uniform partition of `[0, T]` into `m` cells, and the bound it gives for the sum of third
absolute moments of the increments of an Itô process — the size of the Taylor remainder in
Itô's formula.

## Main statements

* `LevyStochCalc.Brownian.Ito.unifGrid` — the uniform grid on `[0, T]`.
* `LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid` — the simple integrand carried by
  the uniform grid.
* `LevyStochCalc.Brownian.Ito.sum_integral_abs_sub_pow_three_le` — the sum of third absolute
  moments of the Itô-integral increments across the grid, of order `m^{-1/2}`.
* `LevyStochCalc.Brownian.Ito.sum_integral_abs_itoIncrement_pow_three_le` — the same for the
  increments of a full Itô process, drift included.
* `LevyStochCalc.Brownian.Ito.tendsto_riemann_weighted_unifGrid` — the Riemann sums of a
  continuous weight against a bounded density converge as the grid refines.
* `LevyStochCalc.Brownian.Ito.exists_unifGrid_cell` — every time in `(0, T]` lies in a cell.
* `LevyStochCalc.Brownian.Ito.abs_ofUnifGrid_eval_sub_le` — the grid step weight is within the
  weight's modulus of continuity at the mesh.
* `LevyStochCalc.Brownian.Ito.lintegral_sq_sub_le_of_bound` — a uniform pathwise bound on
  `(0, T]` gives the `L²` distance over the window.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_2533e0a246989e508bdd4060 {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) {s : ℝ}
    (hs : 0 < s) (hsT : s ≤ T) :
    ∃ i : ℕ, i < m ∧ unifGrid T m i < s ∧ s ≤ unifGrid T m (i + 1) := by
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  set x : ℝ := s * (m : ℝ) / T with hxdef
  have hx0 : 0 < x := by rw [hxdef]; positivity
  have hxm : x ≤ (m : ℝ) := by
    rw [hxdef, div_le_iff₀ hT]
    nlinarith [hmR.le]
  set k : ℕ := ⌈x⌉₊ with hkdef
  have hk1 : 1 ≤ k := Nat.ceil_pos.mpr hx0
  have hkm : k ≤ m := Nat.ceil_le.mpr (by exact_mod_cast hxm)
  refine ⟨k - 1, by omega, ?_, ?_⟩
  · have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      have : (1 : ℕ) ≤ k := hk1
      push_cast [Nat.cast_sub this]
      ring
    rw [LevyStochCalc.Brownian.Ito.unifGrid, hcast, div_lt_iff₀ hmR]
    have hlt : (k : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
    have hxs : x * T = s * (m : ℝ) := by
      rw [hxdef]; field_simp
    nlinarith [hT, hmR]
  · have hcast : (((k - 1 : ℕ) + 1 : ℕ) : ℝ) = (k : ℝ) := by
      have : (1 : ℕ) ≤ k := hk1
      push_cast [Nat.cast_sub this]
      ring
    rw [LevyStochCalc.Brownian.Ito.unifGrid, hcast, le_div_iff₀ hmR]
    have hle : x ≤ (k : ℝ) := Nat.le_ceil x
    have hxs : x * T = s * (m : ℝ) := by
      rw [hxdef]; field_simp
    nlinarith [hT, hmR]
section ThirdMomentSum

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

end ThirdMomentSum

section RiemannLimit

end RiemannLimit

section ItoIncrement

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

end ItoIncrement

end LevyStochCalc.Brownian.Ito


