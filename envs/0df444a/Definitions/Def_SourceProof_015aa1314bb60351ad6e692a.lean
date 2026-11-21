-- Prove2me | Definitions.Def_SourceProof_015aa1314bb60351ad6e692a
-- name    : SourceProof_015aa1314bb60351ad6e692a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:36:36.498178+00:00
-- url     : https://prove2.me/theorems/52081f64-1f64-448b-ba53-59ec530feb93
-- title:
--   LevyStochCalc source module: SourceProof_015aa1314bb60351ad6e692a
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.tendsto_energy_window_clamp` comes from the `LevyStochCalc.Ito.ItoFormulaUnboundedClamp` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F000
import Definitions.Def_SourceProof_29f970bc85115e70732226f2

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Coefficients of a vector Itô process clamped at a finite level

Clamping the coefficients of a vector Itô process at level `j` leaves bounded coefficients of
finite energy whose distance in energy to the original coefficients tends to `0`, and the process
they drive stays within that distance of the original one in `L²`, uniformly on a bounded window;
along a suitable subsequence of levels the clamped processes converge to the original one almost
surely.

## Main statements

* `LevyStochCalc.Brownian.Ito.clampCoeff`, `clampDrift` — the clamped coefficients.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_window_clamp` — the mesh of the approximation.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Clamped

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}


theorem _root_.Prove2MeSourceProof.h_015aa1314bb60351ad6e692a {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hm : ∀ p k, Measurable (Function.uncurry (H p k))) {b : Fin n → Ω → ℝ → ℝ}
    (hbm : ∀ p, Measurable (Function.uncurry (b p))) {T : ℝ}
    (hq : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤)
    (hbq : ∀ p : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤) :
    Filter.Tendsto (clampMesh P H b T) Filter.atTop (𝓝 0) := by
  unfold LevyStochCalc.Brownian.Ito.clampMesh
  have hdrift : ∀ p : Fin n, Filter.Tendsto (fun j : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖LevyStochCalc.Brownian.Ito.clampDrift b j p ω s - b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) Filter.atTop (𝓝 0) :=
    fun p => _root_.Prove2MeSourceProof.h_29f970bc85115e70732226f2 (hbm p) (hbq p)
  have hdiff : ∀ (p : Fin n) (k : Fin d),
      Filter.Tendsto (fun j : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖LevyStochCalc.Brownian.Ito.clampCoeff H j p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) Filter.atTop (𝓝 0) :=
    fun p k => _root_.Prove2MeSourceProof.h_29f970bc85115e70732226f2 (hm p k) (hq p k)
  have hterm : ∀ p : Fin n, Filter.Tendsto (fun j : ℕ =>
      (2 * (ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖LevyStochCalc.Brownian.Ito.clampDrift b j p ω s - b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖LevyStochCalc.Brownian.Ito.clampCoeff H j p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)))
      Filter.atTop (𝓝 0) := by
    intro p
    have h1 : Filter.Tendsto (fun j : ℕ =>
        2 * (ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖LevyStochCalc.Brownian.Ito.clampDrift b j p ω s - b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))
        Filter.atTop (𝓝 0) := by
      have hc := ENNReal.Tendsto.const_mul (a := 2 * ENNReal.ofReal T) (hdrift p)
        (Or.inr (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top))
      rw [mul_zero] at hc
      exact hc.congr fun j => by rw [mul_assoc]
    have h2 : Filter.Tendsto (fun j : ℕ =>
        2 * ((d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖LevyStochCalc.Brownian.Ito.clampCoeff H j p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))
        Filter.atTop (𝓝 0) := by
      have hsum : Filter.Tendsto (fun j : ℕ => ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖LevyStochCalc.Brownian.Ito.clampCoeff H j p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          Filter.atTop (𝓝 0) := by
        have := tendsto_finsetSum (Finset.univ : Finset (Fin d))
          (fun k _ => hdiff p k)
        simpa using this
      have hc := ENNReal.Tendsto.const_mul (a := 2 * (d : ℝ≥0∞)) hsum
        (Or.inr (ENNReal.mul_ne_top (by simp) (by simp)))
      rw [mul_zero] at hc
      exact hc.congr fun j => by rw [mul_assoc]
    simpa using h1.add h2
  have := tendsto_finsetSum (Finset.univ : Finset (Fin n)) (fun p _ => hterm p)
  simpa using this
section ClampProcess

variable (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

end ClampProcess

end Clamped

end LevyStochCalc.Brownian.Ito


