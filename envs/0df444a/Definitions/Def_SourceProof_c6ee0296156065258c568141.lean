-- Prove2me | Definitions.Def_SourceProof_c6ee0296156065258c568141
-- name    : SourceProof_c6ee0296156065258c568141
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:39:04.748434+00:00
-- url     : https://prove2.me/theorems/eae3b44d-935c-490d-9c9e-df43c4d09ba6
-- title:
--   LevyStochCalc source module: SourceProof_c6ee0296156065258c568141
-- statement:
--   The original source theorem `LevyStochCalc.Driver.pairing_cell_joint_eq_zero` comes from the `LevyStochCalc.Driver.CellComplex` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellComplex_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The cell lemma for a complex bounded factor

The grid induction carries the joint character of the earlier cells as the bounded factor, and
that character is complex. Since the weight stays real, the pairing splits into the real and
imaginary parts of the factor, and the vanishing of the mean against the complex factor is the
vanishing of both real means.
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

section Complex

variable (N : PoissonRandomMeasure P ν)

variable {Z : Ω → ℝ} {V : Ω → ℂ} {Mv l : ℝ} {X : ℝ → Ω → ℝ}

end Complex

section Cell

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  (N : PoissonRandomMeasure P ν) (hℱN : IsPoissonFiltration N ℱ)
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}

include hℱN hℱW in

theorem _root_.Prove2MeSourceProof.h_c6ee0296156065258c568141
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (ha : 0 ≤ a) (hab : a < b) (l : ℝ)
    {T : ℝ} (hT : 0 < T) (hbT : b < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc a b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZito : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {V : Ω → ℂ} (hVa : StronglyMeasurable[ℱ a] V) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, ‖V ω‖ ≤ Mv) (hZV : ∫ ω, ((Z ω : ℝ) : ℂ) * V ω ∂P = 0) :
    ∫ ω, ((Z ω : ℝ) : ℂ) * V ω
      * (Complex.exp (Complex.I * ((l * (W.W b ω - W.W a ω) : ℝ) : ℂ))
        * charAt N w Bfam b ω) ∂P = 0 := by
  classical
  have hb0 : (0 : ℝ) < b := lt_of_le_of_lt ha hab
  have hmi := LevyStochCalc.Brownian.Ito.measurable_uncurry_indIoc (Ω := Ω) a b
  have hpi : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (LevyStochCalc.Brownian.Ito.indIoc Ω a b) := by
    rcases eq_or_lt_of_le ha with rfl | ha'
    · exact LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indIoc₀ ℱ hb0
    · exact LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indIoc ℱ ha' hab
  have hqi := _root_.Prove2MeSourceProof.h_0d2a3821a25704fa81bdea82 (Ω := Ω) P a b
  obtain ⟨X, hX⟩ := _root_.Prove2MeSourceProof.h_a53c24ec6562d896f4419b97 W ℱ hℱW (LevyStochCalc.Brownian.Ito.indIoc Ω a b) hmi hpi hqi
    (C := 1) zero_le_one (LevyStochCalc.Brownian.Ito.indIoc_le_one a b) hℱ0 hnull
    (X₀ := fun _ => (0 : ℝ)) measurable_const
    (fun _ _ => (0 : ℝ)) measurable_const (LevyStochCalc.Brownian.Ito.progressivelyMeasurable_zero ℱ)
    (B := 0) le_rfl (fun ω s => by simp)
  have hX0 := LevyStochCalc.Brownian.Ito.ae_eq_zero_of_isItoVersion_indIoc ha hab hX
  have hXb := LevyStochCalc.Brownian.Ito.ae_eq_increment_of_isItoVersion_indIoc ha hab hX
  have hzero := LevyStochCalc.Driver.cellPairingC_eq_zero N hℱN W hℱW hX hX0 ha hab l hT hbT hA hAν w hBm hBsub he₀
    hZ2 hZito hZcomp hVa hMv0 hVb hZV b ⟨hb0.le, le_rfl⟩
  rw [LevyStochCalc.Driver.cellPairingC] at hzero
  refine Eq.trans (integral_congr_ae ?_) hzero
  filter_upwards [hXb] with ω hω
  rw [hω]
end Cell

end LevyStochCalc.Driver


