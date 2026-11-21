-- Prove2me | Definitions.Def_SourceProof_993ce145fd17dba0bc1a4282
-- name    : SourceProof_993ce145fd17dba0bc1a4282
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:54:29.725712+00:00
-- url     : https://prove2.me/theorems/08a96351-5fdb-4ca2-abb2-a0281c01b5f9
-- title:
--   LevyStochCalc source module: SourceProof_993ce145fd17dba0bc1a4282
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.pairing_eq_zero_of_norm_le` comes from the `LevyStochCalc.Brownian.PRPPairing` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPPairing_F000
import Definitions.Def_LevyStochCalc_Brownian_PRPPairing_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pairing a weight orthogonal to the Itô integrals against a trigonometric increment

If `Z` pairs to zero against every Itô integral, then pairing it against `g (X_t)`, for `X` a
version of `∫ 1_{(a,b]} dW` and `g` one of the scaled trigonometric functions, gives a scalar
function of `t` that solves `Λ(t) = −(l²/2) ∫_0^t 1_{(a,b]}(s) Λ(s) ds`. Grönwall then forces
`Λ` to vanish.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Pairing

variable {P : Measure Ω} [IsProbabilityMeasure P]

variable {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}

variable {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}

end Pairing

section Perp

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {a b : ℝ}

end Perp

section Equation

variable {P : Measure Ω} [IsProbabilityMeasure P]


theorem _root_.Prove2MeSourceProof.h_993ce145fd17dba0bc1a4282 {b : ℝ} {X : ℝ → Ω → ℝ}
    (hXm : Measurable (Function.uncurry fun ω s => X s ω)) (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ))
    {Y : Ω → ℂ} (hYm : Measurable Y) (hY : Integrable Y P) (hY0 : ∫ ω, Y ω ∂P = 0)
    (l : ℝ) {g : ℝ → ℝ} (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1)
    (hstep : ∀ t : ℝ, 0 < t → t ≤ b →
      ‖∫ ω, Y ω * ((g (X t ω) : ℝ) : ℂ) ∂P‖
        ≤ l ^ 2 / 2 * ∫ s in Set.Ioc (0 : ℝ) t, ‖∫ ω, Y ω * ((g (X s ω) : ℝ) : ℂ) ∂P‖) :
    ∀ t ∈ Set.Icc (0 : ℝ) b, ∫ ω, Y ω * ((g (X t ω) : ℝ) : ℂ) ∂P = 0 := by
  have hgm : ∀ u : ℝ, Measurable fun ω : Ω => ((g (X u ω) : ℝ) : ℂ) := fun u =>
    Complex.measurable_ofReal.comp (hgc.measurable.comp
      (hXm.comp ((measurable_id (α := Ω)).prodMk measurable_const)))
  have hgbC : ∀ (u : ℝ) (ω : Ω), ‖((g (X u ω) : ℝ) : ℂ)‖ ≤ 1 := by
    intro u ω
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hgb _
  have hint : ∀ u : ℝ, Integrable (fun ω => Y ω * ((g (X u ω) : ℝ) : ℂ)) P := fun u =>
    LevyStochCalc.Brownian.Ito.integrable_mul_of_bounded hY (hgm u).aestronglyMeasurable (hgbC u)
  have hΛmeas : Measurable fun u : ℝ => ∫ ω, Y ω * ((g (X u ω) : ℝ) : ℂ) ∂P :=
    LevyStochCalc.Brownian.Ito.measurable_pairing hYm hXm hgc
  have hΛbd : ∀ u : ℝ, ‖∫ ω, Y ω * ((g (X u ω) : ℝ) : ℂ) ∂P‖ ≤ ∫ ω, ‖Y ω‖ ∂P := by
    intro u
    refine (norm_integral_le_integral_norm _).trans (integral_mono (hint u).norm hY.norm ?_)
    intro ω
    calc ‖Y ω * ((g (X u ω) : ℝ) : ℂ)‖ = ‖Y ω‖ * ‖((g (X u ω) : ℝ) : ℂ)‖ := norm_mul _ _
      _ ≤ ‖Y ω‖ * 1 := mul_le_mul_of_nonneg_left (hgbC u ω) (norm_nonneg _)
      _ = ‖Y ω‖ := mul_one _
  have hzero := LevyStochCalc.Analysis.eq_zero_of_le_mul_setIntegral
    (a := (0 : ℝ)) (b := b) (c := l ^ 2 / 2) (B := ∫ ω, ‖Y ω‖ ∂P) (by positivity)
    (f := fun u => ‖∫ ω, Y ω * ((g (X u ω) : ℝ) : ℂ) ∂P‖) hΛmeas.norm.aestronglyMeasurable
    (fun u => norm_nonneg _) (fun u _ => hΛbd u) ?_
  · intro t ht
    have := hzero t ht
    simpa using this
  · rintro t ⟨ht0, htb⟩
    rcases eq_or_lt_of_le ht0 with rfl | ht0'
    · rw [LevyStochCalc.Brownian.Ito.pairing_zero_time hX0 hY0 g]
      simp
    · exact hstep t ht0' htb
end Equation

end LevyStochCalc.Brownian.Ito


