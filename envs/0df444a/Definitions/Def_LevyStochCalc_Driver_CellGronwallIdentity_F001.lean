-- Prove2me | Definitions.Def_LevyStochCalc_Driver_CellGronwallIdentity_F001
-- name    : LevyStochCalc_Driver_CellGronwallIdentity_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:27:59.369557+00:00
-- url     : https://prove2.me/theorems/0876b42e-e8d6-47f8-aec1-42a94ed8b5ad
-- title:
--   LevyStochCalc source module: LevyStochCalc.Driver.CellGronwallIdentity
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Driver.CellGronwallIdentity in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellGronwallPairing_F001
import Definitions.Def_SourceProof_d70b081240f0d1c36022214e

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The cell identity and the Grönwall bound for the cell pairing

The real and the imaginary cell identities recombine into an integral equation for the pairing of
a square-integrable weight and a bounded factor with the product of the Brownian cell character
`e^{i l X_s}` and the Poisson cell character: the pairing at a time in the cell is its value at
the origin plus a deterministic drift term over the elapsed times and a mark-factor term over the
window. The Grönwall estimate that follows forces the pairing to vanish throughout the cell when
the weight is orthogonal to every Itô integral and every compensated integral and has mean zero
against the bounded factor.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section Identity

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  (N : PoissonRandomMeasure P ν) (hℱN : IsPoissonFiltration N ℱ)
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ} {ι : Type*} [Fintype ι]

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- At the origin the pairing is the mean of the weight against the bounded factor. -/
theorem cellPairing_zero (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) {Z V : Ω → ℝ} {l : ℝ}
    (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ)) :
    cellPairing N w Bfam Z V l X 0 = ((∫ ω, Z ω * V ω ∂P : ℝ) : ℂ) := by
  rw [cellPairing]
  have h : ∀ᵐ ω ∂P, ((Z ω * V ω : ℝ) : ℂ)
      * (Complex.exp (Complex.I * ((l * X 0 ω : ℝ) : ℂ)) * charAt N w Bfam 0 ω)
      = ((Z ω * V ω : ℝ) : ℂ) := by
    filter_upwards [hX0] with ω hω
    rw [hω, charAt_zero N w]
    simp
  rw [integral_congr_ae h]
  exact integral_ofReal
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The pairing is bounded uniformly in the time. -/
theorem norm_cellPairing_bound (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {Z V : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hVm : Measurable V) {Mv : ℝ} (hMv0 : 0 ≤ Mv) (hVb : ∀ ω, |V ω| ≤ Mv) {l : ℝ} {s : ℝ}
    (hXs : Measurable (X s)) :
    ‖cellPairing N w Bfam Z V l X s‖ ≤ 2 * (Mv * ∫ ω, ‖Z ω‖ ∂P) := by
  rw [_root_.Prove2MeSourceProof.h_d70b081240f0d1c36022214e N w hBm hZ2 hVm hVb hXs]
  refine le_trans (norm_add_le _ _) ?_
  have h1 := _root_.Prove2MeSourceProof.h_9d0138fdc01d3cc6c2310f1d (l := l) (X := X) N w Bfam (hZ2.integrable one_le_two) hMv0 hVb
    Real.abs_cos_le_one s
  have h2 := _root_.Prove2MeSourceProof.h_9d0138fdc01d3cc6c2310f1d (l := l) (X := X) N w Bfam (hZ2.integrable one_le_two) hMv0 hVb
    Real.abs_sin_le_one s
  rw [norm_mul, Complex.norm_I, one_mul]
  linarith
end Identity

end LevyStochCalc.Driver


