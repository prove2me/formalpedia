-- Prove2me | Definitions.Def_SourceProof_f2734a4bc0d51d1dd6733e48
-- name    : SourceProof_f2734a4bc0d51d1dd6733e48
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:43:38.060461+00:00
-- url     : https://prove2.me/theorems/7801fc55-3d14-4184-bbd8-42175aa4c57c
-- title:
--   LevyStochCalc source module: SourceProof_f2734a4bc0d51d1dd6733e48
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral_mulLeft` comes from the `LevyStochCalc.Poisson.CompensatedPullOut` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedPullOut_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pulling a past weight inside a compensated integral

A bounded weight measurable at time `a` times the compensated integral of a marked integrand
vanishing up to `a` is the compensated integral of the weighted integrand. The identity is proved
in `L²`: the squared distance between the two sides expands, through the Itô–Lévy isometry and
the quadratic-variation martingale started at `a`, into a combination of weighted compensators
that cancels.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Vanishing

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ) (φ : Ω → ℝ → E → ℝ)
  (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (hq : ∀ T : ℝ, 0 < T → markedEnergy P ν T φ < ⊤)

end Vanishing

section Weighted

namespace MarkedHorizonIntegrand

variable {T : ℝ}

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)


theorem _root_.Prove2MeSourceProof.h_f2734a4bc0d51d1dd6733e48 (hT : 0 < T) (G : MarkedHorizonIntegrand P ν ℱ T) {a : ℝ} (ha : 0 ≤ a)
    (haT : a ≤ T) (hGa : ∀ ω s e, s ≤ a → G.toFun ω s e = 0) {V : Ω → ℝ}
    (hVm : StronglyMeasurable[ℱ a] V) {M : ℝ} (hVb : ∀ ω, |V ω| ≤ M) :
    (G.mulLeft hGa hVm hVb).integral N hℱ =ᵐ[P] fun ω => V ω * G.integral N hℱ ω := by
  have hVb' : ∀ ω, |V ω| ≤ |M| := fun ω => (hVb ω).trans (le_abs_self M)
  have hM0 : 0 ≤ |M| := abs_nonneg M
  have hVm1 : StronglyMeasurable[ℱ a] fun ω => V ω + 1 := hVm.add stronglyMeasurable_const
  have hVb1 : ∀ ω, |V ω + 1| ≤ |M| + 1 := fun ω =>
    (abs_add_le _ _).trans (by simpa using add_le_add_right (hVb' ω) 1)
  set X := ((LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.mulLeft G) hGa hVm hVb).integral N hℱ with hX
  set Y := G.integral N hℱ with hY
  set S := ((LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.mulLeft G) hGa hVm1 hVb1).integral N hℱ with hS
  have hSXY : S =ᵐ[P] fun ω => X ω + Y ω := by
    have h1 := LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral_add N hℱ hT ((LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.mulLeft G) hGa hVm hVb) G
    have h2 : ((LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.add ((LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.mulLeft G) hGa hVm hVb)) G).integral N hℱ = S :=
      LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral_congr_toFun N hℱ (by funext ω s e; simp only [LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.add, LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.mulLeft]; ring)
    rw [h2] at h1
    exact h1
  have hX2 : MemLp X 2 P := LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.memLp N hℱ _
  have hY2 : MemLp Y 2 P := LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.memLp N hℱ G
  have hS2 : MemLp S 2 P := LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.memLp N hℱ _
  have hVmeas : Measurable V := hVm.measurable.mono (ℱ.le a) le_rfl
  have hVnorm : ∀ᵐ ω ∂P, ‖V ω‖ ≤ M :=
    Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hVb ω
  have hcomp : Integrable (LevyStochCalc.Poisson.Compensated.compensator ν G.toFun T) P :=
    LevyStochCalc.Poisson.Compensated.integrable_compensator G.toFun G.measurable_uncurry G.sq_int_global T
  -- integrability of bounded multiples of the compensator
  have hbdd : ∀ (U : Ω → ℝ), Measurable U → ∀ C : ℝ, (∀ ω, |U ω| ≤ C) →
      Integrable (fun ω => U ω * LevyStochCalc.Poisson.Compensated.compensator ν G.toFun T ω) P := fun U hU C hC =>
    hcomp.bdd_mul hU.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)
  -- the five weighted second moments
  have hXX : ∫ ω, X ω ^ 2 ∂P = ∫ ω, V ω ^ 2 * LevyStochCalc.Poisson.Compensated.compensator ν G.toFun T ω ∂P := by
    have h := LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral_mul_sq_integral N hℱ ((LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.mulLeft G) hGa hVm hVb) ha haT
      (fun ω s e hs => by
        change V ω * G.toFun ω s e = 0
        rw [hGa ω s e hs, mul_zero])
      (U := fun _ => (1 : ℝ)) stronglyMeasurable_const (M := 1) (fun _ => by simp)
    simp only [one_mul, LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.compensator_mulLeft] at h
    exact h
  have hYY : ∫ ω, V ω ^ 2 * Y ω ^ 2 ∂P = ∫ ω, V ω ^ 2 * LevyStochCalc.Poisson.Compensated.compensator ν G.toFun T ω ∂P :=
    LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral_mul_sq_integral N hℱ G ha haT hGa (hVm.pow 2) (M := M ^ 2)
      (fun ω => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hVb ω) 2)
  have hVSS : ∫ ω, V ω * S ω ^ 2 ∂P
      = ∫ ω, V ω * ((V ω + 1) ^ 2 * LevyStochCalc.Poisson.Compensated.compensator ν G.toFun T ω) ∂P := by
    have h := LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral_mul_sq_integral N hℱ ((LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.mulLeft G) hGa hVm1 hVb1) ha haT
      (fun ω s e hs => by
        change (V ω + 1) * G.toFun ω s e = 0
        rw [hGa ω s e hs, mul_zero]) hVm hVb
    simp only [LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.compensator_mulLeft] at h
    exact h
  have hVXX : ∫ ω, V ω * X ω ^ 2 ∂P
      = ∫ ω, V ω * (V ω ^ 2 * LevyStochCalc.Poisson.Compensated.compensator ν G.toFun T ω) ∂P := by
    have h := LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral_mul_sq_integral N hℱ ((LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.mulLeft G) hGa hVm hVb) ha haT
      (fun ω s e hs => by
        change V ω * G.toFun ω s e = 0
        rw [hGa ω s e hs, mul_zero]) hVm hVb
    simp only [LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.compensator_mulLeft] at h
    exact h
  have hVYY : ∫ ω, V ω * Y ω ^ 2 ∂P = ∫ ω, V ω * LevyStochCalc.Poisson.Compensated.compensator ν G.toFun T ω ∂P :=
    LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral_mul_sq_integral N hℱ G ha haT hGa hVm hVb
  -- the cross term by polarisation
  have hXYint : Integrable (fun ω => V ω * (X ω * Y ω)) P :=
    (LevyStochCalc.Poisson.Compensated.integrable_mul_of_memLp_two hX2 hY2).bdd_mul hVmeas.aestronglyMeasurable hVnorm
  have hVS2 : Integrable (fun ω => V ω * S ω ^ 2) P :=
    hS2.integrable_sq.bdd_mul hVmeas.aestronglyMeasurable hVnorm
  have hVX2 : Integrable (fun ω => V ω * X ω ^ 2) P :=
    hX2.integrable_sq.bdd_mul hVmeas.aestronglyMeasurable hVnorm
  have hVY2 : Integrable (fun ω => V ω * Y ω ^ 2) P :=
    hY2.integrable_sq.bdd_mul hVmeas.aestronglyMeasurable hVnorm
  have hXY : ∫ ω, V ω * (X ω * Y ω) ∂P = ∫ ω, V ω ^ 2 * LevyStochCalc.Poisson.Compensated.compensator ν G.toFun T ω ∂P := by
    have hpt : (fun ω => V ω * (X ω * Y ω))
        =ᵐ[P] fun ω => (1 / 2 : ℝ) * (V ω * S ω ^ 2 - V ω * X ω ^ 2 - V ω * Y ω ^ 2) := by
      filter_upwards [hSXY] with ω hω
      rw [hω]
      ring
    have hVSX : Integrable (fun ω => V ω * S ω ^ 2 - V ω * X ω ^ 2) P := hVS2.sub hVX2
    rw [integral_congr_ae hpt, integral_const_mul, integral_sub hVSX hVY2,
      integral_sub hVS2 hVX2, hVSS, hVXX, hVYY]
    have i1 : Integrable (fun ω => (V ω * (V ω + 1) ^ 2) * LevyStochCalc.Poisson.Compensated.compensator ν G.toFun T ω) P :=
      hbdd (fun ω => V ω * (V ω + 1) ^ 2) (hVmeas.mul ((hVmeas.add_const 1).pow_const 2))
        (|M| * (|M| + 1) ^ 2) (fun ω => by
          rw [abs_mul, abs_pow]
          exact mul_le_mul (hVb' ω) (pow_le_pow_left₀ (abs_nonneg _) (hVb1 ω) 2)
            (by positivity) hM0)
    have i2 : Integrable (fun ω => (V ω * V ω ^ 2) * LevyStochCalc.Poisson.Compensated.compensator ν G.toFun T ω) P :=
      hbdd (fun ω => V ω * V ω ^ 2) (hVmeas.mul (hVmeas.pow_const 2)) (|M| * |M| ^ 2)
        (fun ω => by
          rw [abs_mul, abs_pow]
          exact mul_le_mul (hVb' ω) (pow_le_pow_left₀ (abs_nonneg _) (hVb' ω) 2)
            (by positivity) hM0)
    have i3 : Integrable (fun ω => V ω * LevyStochCalc.Poisson.Compensated.compensator ν G.toFun T ω) P := hbdd V hVmeas M hVb
    have i12 : Integrable (fun ω => (V ω * (V ω + 1) ^ 2) * LevyStochCalc.Poisson.Compensated.compensator ν G.toFun T ω
        - (V ω * V ω ^ 2) * LevyStochCalc.Poisson.Compensated.compensator ν G.toFun T ω) P := i1.sub i2
    have e1 : (fun ω => V ω * ((V ω + 1) ^ 2 * LevyStochCalc.Poisson.Compensated.compensator ν G.toFun T ω))
        = fun ω => (V ω * (V ω + 1) ^ 2) * LevyStochCalc.Poisson.Compensated.compensator ν G.toFun T ω := by
      funext ω; ring
    have e2 : (fun ω => V ω * (V ω ^ 2 * LevyStochCalc.Poisson.Compensated.compensator ν G.toFun T ω))
        = fun ω => (V ω * V ω ^ 2) * LevyStochCalc.Poisson.Compensated.compensator ν G.toFun T ω := by
      funext ω; ring
    rw [e1, e2, ← integral_sub i1 i2, ← integral_sub i12 i3, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    ring
  -- the squared distance vanishes
  have hpt : ∀ ω, (X ω - V ω * Y ω) ^ 2
      = X ω ^ 2 - 2 * (V ω * (X ω * Y ω)) + V ω ^ 2 * Y ω ^ 2 := fun ω => by ring
  have hV2Y2 : Integrable (fun ω => V ω ^ 2 * Y ω ^ 2) P :=
    hY2.integrable_sq.bdd_mul (hVmeas.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hVb ω) 2)
  have hint : Integrable (fun ω => (X ω - V ω * Y ω) ^ 2) P := by
    have : (fun ω => (X ω - V ω * Y ω) ^ 2)
        = fun ω => X ω ^ 2 - 2 * (V ω * (X ω * Y ω)) + V ω ^ 2 * Y ω ^ 2 := funext hpt
    rw [this]
    exact (hX2.integrable_sq.sub (hXYint.const_mul 2)).add hV2Y2
  have hA : Integrable (fun ω => X ω ^ 2 - 2 * (V ω * (X ω * Y ω))) P :=
    hX2.integrable_sq.sub (hXYint.const_mul 2)
  have hZ : ∫ ω, (X ω - V ω * Y ω) ^ 2 ∂P = 0 := by
    simp_rw [hpt]
    rw [MeasureTheory.integral_add hA hV2Y2, integral_sub hX2.integrable_sq (hXYint.const_mul 2),
      integral_const_mul, hXX, hXY, hYY]
    ring
  have hnn : 0 ≤ fun ω => (X ω - V ω * Y ω) ^ 2 := fun ω => sq_nonneg _
  filter_upwards [(integral_eq_zero_iff_of_nonneg hnn hint).mp hZ] with ω hω
  have h2 : (X ω - V ω * Y ω) ^ 2 = 0 := hω
  exact sub_eq_zero.mp ((pow_eq_zero_iff (n := 2) (by norm_num)).mp h2)
end MarkedHorizonIntegrand

end Weighted

end LevyStochCalc.Poisson.Compensated


