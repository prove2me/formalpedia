-- Prove2me | Definitions.Def_SourceProof_da7ea7e203c7e5242a91682e
-- name    : SourceProof_da7ea7e203c7e5242a91682e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:58:39.651805+00:00
-- url     : https://prove2.me/theorems/181555b1-2032-412d-9ab9-60ba254eb7c1
-- title:
--   LevyStochCalc source module: SourceProof_da7ea7e203c7e5242a91682e
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.norm_pairing_le_setIntegral_norm` comes from the `LevyStochCalc.Brownian.PRPPairing` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPPairing_F001
import Definitions.Def_SourceProof_8fe1606d2a5bd9c8ee5cbf20

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


theorem _root_.Prove2MeSourceProof.h_da7ea7e203c7e5242a91682e {a b : ℝ} {X : ℝ → Ω → ℝ}
    (hXm : Measurable (Function.uncurry fun ω s => X s ω)) (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ))
    {Y : Ω → ℂ} (hYm : Measurable Y) (hY : Integrable Y P) (hY0 : ∫ ω, Y ω ∂P = 0)
    (l : ℝ) {g : ℝ → ℝ} (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1)
    {A : Ω → ℝ} (hAperp : ∫ ω, Y ω * ((A ω : ℝ) : ℂ) ∂P = 0)
    {t : ℝ} (ht : 0 < t)
    (hIto : ∀ᵐ ω ∂P, g (X t ω) - g (X 0 ω) = A ω + trigDrift l g X a b t ω) :
    ‖∫ ω, Y ω * ((g (X t ω) : ℝ) : ℂ) ∂P‖
      ≤ l ^ 2 / 2 * ∫ s in Set.Ioc (0 : ℝ) t, ‖∫ ω, Y ω * ((g (X s ω) : ℝ) : ℂ) ∂P‖ := by
  classical
  have hgm : ∀ u : ℝ, Measurable fun ω : Ω => ((g (X u ω) : ℝ) : ℂ) := fun u =>
    Complex.measurable_ofReal.comp (hgc.measurable.comp
      (hXm.comp ((measurable_id (α := Ω)).prodMk measurable_const)))
  have hgbC : ∀ (u : ℝ) (ω : Ω), ‖((g (X u ω) : ℝ) : ℂ)‖ ≤ 1 := by
    intro u ω
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hgb _
  have hint : ∀ u : ℝ, Integrable (fun ω => Y ω * ((g (X u ω) : ℝ) : ℂ)) P := fun u =>
    LevyStochCalc.Brownian.Ito.integrable_mul_of_bounded hY (hgm u).aestronglyMeasurable (hgbC u)
  -- the pairing vanishes at time zero
  have hΛ0 : ∫ ω, Y ω * ((g (X 0 ω) : ℝ) : ℂ) ∂P = 0 := by
    have hcong : ∫ ω, Y ω * ((g (X 0 ω) : ℝ) : ℂ) ∂P = ∫ ω, Y ω * ((g 0 : ℝ) : ℂ) ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hX0] with ω hω
      rw [hω]
    rw [hcong, integral_mul_const, hY0, zero_mul]
  -- the drift term is bounded and measurable
  have hjoint : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      -l ^ 2 * g (X s ω) * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s ^ 2) := by
    have h1 : Measurable fun p : Ω × ℝ => -l ^ 2 * g (X p.2 p.1) :=
      (hgc.measurable.comp hXm).const_mul _
    have h2 : Measurable fun p : Ω × ℝ => LevyStochCalc.Brownian.Ito.indIoc Ω a b p.1 p.2 ^ 2 :=
      (LevyStochCalc.Brownian.Ito.measurable_uncurry_indIoc a b).pow_const 2
    exact h1.mul h2
  have hDmeas : Measurable fun ω : Ω => ((LevyStochCalc.Brownian.Ito.trigDrift l g X a b t ω : ℝ) : ℂ) := by
    refine Complex.measurable_ofReal.comp ?_
    have hDr : Measurable (LevyStochCalc.Brownian.Ito.trigDrift l g X a b t) :=
      (StronglyMeasurable.integral_prod_right (ν := volume.restrict (Set.Ioc (0 : ℝ) t))
        hjoint.stronglyMeasurable).measurable.const_mul _
    exact hDr
  have hDbd : ∀ ω : Ω, ‖((LevyStochCalc.Brownian.Ito.trigDrift l g X a b t ω : ℝ) : ℂ)‖ ≤ l ^ 2 / 2 * t := by
    intro ω
    rw [Complex.norm_real, LevyStochCalc.Brownian.Ito.trigDrift_eq, Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ l ^ 2 / 2)]
    have hb : |∫ s in Set.Ioc (0 : ℝ) t, g (X s ω) * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s ∂volume| ≤ 1 * t := by
      have hC : ∀ s ∈ Set.Ioc (0 : ℝ) t, ‖g (X s ω) * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s‖ ≤ 1 := by
        intro s _
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_one₀ (hgb _) (abs_nonneg _) (LevyStochCalc.Brownian.Ito.indIoc_le_one a b ω s)
      have hnorm := norm_setIntegral_le_of_norm_le_const (μ := volume)
        (s := Set.Ioc (0 : ℝ) t) (f := fun s => g (X s ω) * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s) (C := 1)
        (by simp [Real.volume_Ioc]) hC
      rw [Real.norm_eq_abs] at hnorm
      refine hnorm.trans (le_of_eq ?_)
      rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
      ring
    calc l ^ 2 / 2 * |∫ s in Set.Ioc (0 : ℝ) t, g (X s ω) * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s ∂volume|
        ≤ l ^ 2 / 2 * (1 * t) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = l ^ 2 / 2 * t := by ring
  have hYDint : Integrable (fun ω => Y ω * ((LevyStochCalc.Brownian.Ito.trigDrift l g X a b t ω : ℝ) : ℂ)) P :=
    LevyStochCalc.Brownian.Ito.integrable_mul_of_bounded hY hDmeas.aestronglyMeasurable hDbd
  have hYABint : Integrable
      (fun ω => Y ω * (((A ω + LevyStochCalc.Brownian.Ito.trigDrift l g X a b t ω : ℝ)) : ℂ)) P := by
    refine ((hint t).sub (hint 0)).congr ?_
    filter_upwards [hIto] with ω hω
    simp only [Pi.sub_apply, ← hω]
    push_cast
    ring
  have hYAint : Integrable (fun ω => Y ω * ((A ω : ℝ) : ℂ)) P := by
    have hsub : (fun ω => Y ω * ((A ω : ℝ) : ℂ))
        = fun ω => Y ω * (((A ω + LevyStochCalc.Brownian.Ito.trigDrift l g X a b t ω : ℝ)) : ℂ)
            - Y ω * ((LevyStochCalc.Brownian.Ito.trigDrift l g X a b t ω : ℝ) : ℂ) := by
      funext ω; push_cast; ring
    rw [hsub]
    exact hYABint.sub hYDint
  -- the pairing at time `t` is the pairing against the drift term
  have hΛt : ∫ ω, Y ω * ((g (X t ω) : ℝ) : ℂ) ∂P
      = ∫ ω, Y ω * ((LevyStochCalc.Brownian.Ito.trigDrift l g X a b t ω : ℝ) : ℂ) ∂P := by
    have hcong : ∫ ω, Y ω * ((g (X t ω) : ℝ) : ℂ) ∂P
        = ∫ ω, (Y ω * (((A ω + LevyStochCalc.Brownian.Ito.trigDrift l g X a b t ω : ℝ)) : ℂ)
            + Y ω * ((g (X 0 ω) : ℝ) : ℂ)) ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hIto] with ω hω
      have hval : g (X t ω) = A ω + LevyStochCalc.Brownian.Ito.trigDrift l g X a b t ω + g (X 0 ω) := by linarith
      rw [hval]
      push_cast
      ring
    rw [hcong, integral_add hYABint (hint 0), hΛ0, add_zero]
    have hsplit : ∫ ω, Y ω * (((A ω + LevyStochCalc.Brownian.Ito.trigDrift l g X a b t ω : ℝ)) : ℂ) ∂P
        = (∫ ω, Y ω * ((A ω : ℝ) : ℂ) ∂P)
          + ∫ ω, Y ω * ((LevyStochCalc.Brownian.Ito.trigDrift l g X a b t ω : ℝ) : ℂ) ∂P := by
      rw [← integral_add hYAint hYDint]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      push_cast
      ring
    rw [hsplit, hAperp, zero_add]
  -- the drift pairing, by Fubini, is the running integral of the pairing
  have hstep1 : ∫ ω, Y ω * ((LevyStochCalc.Brownian.Ito.trigDrift l g X a b t ω : ℝ) : ℂ) ∂P
      = -((l ^ 2 / 2 : ℝ) : ℂ) * ∫ ω, Y ω *
          (∫ s in Set.Ioc (0 : ℝ) t, ((g (X s ω) * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s : ℝ) : ℂ)) ∂P := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [LevyStochCalc.Brownian.Ito.trigDrift_eq, integral_complex_ofReal]
    push_cast
    ring
  have hΦm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      ((g (X s ω) * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp
      ((hgc.measurable.comp hXm).mul (LevyStochCalc.Brownian.Ito.measurable_uncurry_indIoc a b))
  have hΦb : ∀ (ω : Ω) (s : ℝ), ‖((g (X s ω) * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s : ℝ) : ℂ)‖ ≤ 1 := by
    intro ω s
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    exact mul_le_one₀ (hgb _) (abs_nonneg _) (LevyStochCalc.Brownian.Ito.indIoc_le_one a b ω s)
  have hfub := _root_.Prove2MeSourceProof.h_8fe1606d2a5bd9c8ee5cbf20
    (a := (0 : ℝ)) (t := t) hYm hY hΦm hΦb
  have hinner : ∀ s : ℝ, ∫ ω, Y ω * ((g (X s ω) * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s : ℝ) : ℂ) ∂P
      = (∫ ω, Y ω * ((g (X s ω) : ℝ) : ℂ) ∂P)
        * (((Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s : ℝ) : ℂ) := by
    intro s
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    change Y ω * ((g (X s ω) * (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s : ℝ) : ℂ) = _
    push_cast
    ring
  -- the pairing is uniformly bounded and measurable in time
  have hΛmeas : Measurable fun u : ℝ => ∫ ω, Y ω * ((g (X u ω) : ℝ) : ℂ) ∂P :=
    LevyStochCalc.Brownian.Ito.measurable_pairing hYm hXm hgc
  have hΛbd : ∀ u : ℝ, ‖∫ ω, Y ω * ((g (X u ω) : ℝ) : ℂ) ∂P‖ ≤ ∫ ω, ‖Y ω‖ ∂P := by
    intro u
    refine (norm_integral_le_integral_norm _).trans (integral_mono (hint u).norm hY.norm ?_)
    intro ω
    calc ‖Y ω * ((g (X u ω) : ℝ) : ℂ)‖ = ‖Y ω‖ * ‖((g (X u ω) : ℝ) : ℂ)‖ := norm_mul _ _
      _ ≤ ‖Y ω‖ * 1 := mul_le_mul_of_nonneg_left (hgbC u ω) (norm_nonneg _)
      _ = ‖Y ω‖ := mul_one _
  have hIntΛ : IntegrableOn
      (fun s => ‖∫ ω, Y ω * ((g (X s ω) : ℝ) : ℂ) ∂P‖) (Set.Ioc (0 : ℝ) t) volume := by
    refine Measure.integrableOn_of_bounded (M := ∫ ω, ‖Y ω‖ ∂P) (by simp [Real.volume_Ioc])
      hΛmeas.norm.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hΛbd s
  have hIntΛind : IntegrableOn (fun s => ‖(∫ ω, Y ω * ((g (X s ω) : ℝ) : ℂ) ∂P)
      * (((Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s : ℝ) : ℂ)‖) (Set.Ioc (0 : ℝ) t) volume := by
    have hmeas : Measurable fun s : ℝ => ‖(∫ ω, Y ω * ((g (X s ω) : ℝ) : ℂ) ∂P)
        * (((Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s : ℝ) : ℂ)‖ :=
      (hΛmeas.mul (Complex.measurable_ofReal.comp
        (measurable_const.indicator measurableSet_Ioc))).norm
    refine Measure.integrableOn_of_bounded (M := ∫ ω, ‖Y ω‖ ∂P) (by simp [Real.volume_Ioc])
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_mul, Complex.norm_real,
      Real.norm_eq_abs]
    refine le_trans (mul_le_of_le_one_right (norm_nonneg _) ?_) (hΛbd s)
    by_cases h : s ∈ Set.Ioc a b
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  have hbound : ‖∫ s in Set.Ioc (0 : ℝ) t, (∫ ω, Y ω * ((g (X s ω) : ℝ) : ℂ) ∂P)
        * (((Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s : ℝ) : ℂ)‖
      ≤ ∫ s in Set.Ioc (0 : ℝ) t, ‖∫ ω, Y ω * ((g (X s ω) : ℝ) : ℂ) ∂P‖ := by
    refine (norm_integral_le_integral_norm _).trans (integral_mono hIntΛind hIntΛ fun s => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    by_cases h : s ∈ Set.Ioc a b
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  rw [hΛt, hstep1, hfub]
  simp only [hinner]
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ l ^ 2 / 2)]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)
end Equation

end LevyStochCalc.Brownian.Ito


