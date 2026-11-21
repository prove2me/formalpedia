-- Prove2me | Definitions.Def_SourceProof_1cfc3aa11ae6a425fc4b5453
-- name    : SourceProof_1cfc3aa11ae6a425fc4b5453
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:27:16.038095+00:00
-- url     : https://prove2.me/theorems/cd64ef87-3083-4965-a07b-f2917bff2da6
-- title:
--   LevyStochCalc source module: SourceProof_1cfc3aa11ae6a425fc4b5453
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.lintegral_lintegral_sq_lt_top_of_supL2` comes from the `LevyStochCalc.Ito.PicardWindow` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardLocality_F000
import Definitions.Def_LevyStochCalc_Ito_PicardLocality_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Solutions of the SDE on a window

`SolvesOn` records that a path map satisfies the jump-diffusion integral equation at every time
of `[0, T]`, in the `picardStep` form; the integrand hypotheses that make the two stochastic
integrals well-typed are bundled existentially, as in
`LevyStochCalc.Ito.Setting.JumpDiffusion.is_solution`, so that a solution can be re-read with any
proof of them. Two solutions on a common window and a common filtration agree, by the Bielecki
contraction.
-/

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### From an `S²` bound to the time-integrated energy -/


theorem _root_.Prove2MeSourceProof.h_1cfc3aa11ae6a425fc4b5453 {Z : ℝ → Ω → (Fin n → ℝ)}
    (hS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (b : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  rcases le_or_gt b 0 with hb | hb
  · have hvol : (volume (Set.Icc (0 : ℝ) b)) = 0 := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_eq_zero.mpr (by linarith : b - 0 ≤ 0)
    have : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume = 0 := by
      intro ω
      exact setLIntegral_measure_zero _ _ hvol
    simp [this]
  · set F : Ω → ℝ≥0∞ :=
      fun ω => ⨆ t : Set.Icc (0 : ℝ) b, ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2 with hF
    have hle : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
          ≤ ∫⁻ ω, F ω * ENNReal.ofReal b ∂P := by
      refine lintegral_mono fun ω => ?_
      have hpt : ∫⁻ s in Set.Icc (0 : ℝ) b,
          ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume
            ≤ ∫⁻ _ in Set.Icc (0 : ℝ) b, F ω ∂volume := by
        refine setLIntegral_mono_ae ?_ ?_
        · exact measurable_const.aemeasurable
        · refine Filter.Eventually.of_forall fun s hs => ?_
          exact le_iSup (fun t : Set.Icc (0 : ℝ) b =>
            ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ⟨s, hs⟩
      refine hpt.trans ?_
      rw [setLIntegral_const, Real.volume_Icc, sub_zero]
    refine lt_of_le_of_lt hle ?_
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top (hS b hb) (ENNReal.ofReal_lt_top)
/-! ### Auxiliary Bielecki facts -/

/-! ### Solutions on a window -/

section Solves

variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (x₀ : Fin n → ℝ)

end Solves

/-! ### The canonical integrand hypotheses along a process with a finite `S²` norm -/

section Canonical

variable {ν : Measure E}
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}

end Canonical

/-! ### The window fixed point is a solution -/

section FixedPoint

variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)

end FixedPoint

end LevyStochCalc.Ito.Picard


