-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ou_exact_stochastic_integral_transition_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:39:23.088884+00:00
-- url     : https://prove2.me/submissions/ff71d353-b67b-4189-b6b5-815b4e53e2b5

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Theorems.Thm_LevyStochCalc_Brownian_Ito_martingale_quadVar_stochasticIntegralBrownian_readable
import Theorems.Thm_AppliedSDE_SarkkaSolin_ou_deterministic_integrand_energy
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology BigOperators

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (rate q x₀ T : ℝ) (hrate : 0 < rate) (hq : 0 ≤ q) (hT : 0 ≤ T)
    (H : Ω → ℝ → ℝ)
    (hH : ∀ (ω : Ω) (s : ℝ),
      H ω s = Real.sqrt q * Real.exp (-rate * (T - s)))
    (hHmeas : Measurable (Function.uncurry H))
    (hHprog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hHsq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    let Y : Ω → ℝ := fun ω =>
      Real.exp (-rate * T) * x₀ +
        LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
          W ℱ hW H hHmeas hHprog hHsq T ω
    (∫ ω, Y ω ∂P) = Real.exp (-rate * T) * x₀ ∧
      (∫ ω, (Y ω - Real.exp (-rate * T) * x₀) ^ 2 ∂P) =
        q / (2 * rate) * (1 - Real.exp (-2 * rate * T)) := by
  let I : ℝ → Ω → ℝ := fun t ω =>
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
      W ℱ hW H hHmeas hHprog hHsq t ω
  let c : ℝ := Real.exp (-rate * T) * x₀
  let E : ℝ := q / (2 * rate) * (1 - Real.exp (-2 * rate * T))
  have hcomp (ω : Ω) :
      (∫ s in Set.Icc (0 : ℝ) T, (H ω s) ^ 2 ∂volume) = E := by
    calc
      (∫ s in Set.Icc (0 : ℝ) T, (H ω s) ^ 2 ∂volume) =
          ∫ s in Set.Icc (0 : ℝ) T,
            (Real.sqrt q * Real.exp (-rate * (T - s))) ^ 2 ∂volume := by
              apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
              intro s hs
              simpa only [hH]
      _ = ∫ s in (0 : ℝ)..T,
          (Real.sqrt q * Real.exp (-rate * (T - s))) ^ 2 := by
              rw [intervalIntegral.integral_of_le hT,
                ← MeasureTheory.integral_Icc_eq_integral_Ioc]
      _ = E := by
          exact AppliedSDE.SarkkaSolin.ou_deterministic_integrand_energy
            rate q T hrate hq hT
  have hm : Martingale I ℱ P := by
    simpa only [I] using
      (LevyStochCalc.Brownian.Ito.martingale_stochasticIntegralBrownian
        W ℱ hW H hHmeas hHprog hHsq)
  have hmq : Martingale
      (fun t ω => I t ω ^ 2 -
        ∫ s in Set.Icc (0 : ℝ) t, (H ω s) ^ 2 ∂volume) ℱ P := by
    simpa only [I] using
      (LevyStochCalc.Brownian.Ito.martingale_quadVar_stochasticIntegralBrownian_readable
        W ℱ hW H hHmeas hHprog hHsq)
  have hI0 : I 0 =ᵐ[P] (fun _ => (0 : ℝ)) := by
    exact LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_nonpos
      W ℱ hW H hHmeas hHprog hHsq (le_refl (0 : ℝ))
  have hmean0 : (∫ ω, I 0 ω ∂P) = 0 := by
    rw [integral_congr_ae hI0]
    simp
  have hmeanT : (∫ ω, I T ω ∂P) = 0 := by
    have heq := hm.setIntegral_eq (i := (0 : ℝ)) (j := T)
      hT (s := Set.univ) (by simp)
    simp only [MeasureTheory.setIntegral_univ] at heq
    exact heq.symm.trans hmean0
  have hQ0ae :
      (fun ω => I 0 ω ^ 2 -
        ∫ s in Set.Icc (0 : ℝ) (0 : ℝ), (H ω s) ^ 2 ∂volume)
          =ᵐ[P] (fun _ => (0 : ℝ)) := by
    filter_upwards [hI0] with ω hz
    simp [hz]
  have hQ0 : (∫ ω, I 0 ω ^ 2 -
      (∫ s in Set.Icc (0 : ℝ) (0 : ℝ), (H ω s) ^ 2 ∂volume) ∂P) = 0 := by
    rw [integral_congr_ae hQ0ae]
    simp
  have hQmean : (∫ ω, I T ω ^ 2 -
      (∫ s in Set.Icc (0 : ℝ) T, (H ω s) ^ 2 ∂volume) ∂P) = 0 := by
    have heq := hmq.setIntegral_eq (i := (0 : ℝ)) (j := T)
      hT (s := Set.univ) (by simp)
    simp only [MeasureTheory.setIntegral_univ] at heq
    exact heq.symm.trans hQ0
  have hsqEq :
      (fun ω : Ω => I T ω ^ 2) =
        (fun ω => (I T ω ^ 2 -
          ∫ s in Set.Icc (0 : ℝ) T, (H ω s) ^ 2 ∂volume) + E) := by
    funext ω
    rw [hcomp ω]
    ring
  have hsqMean : (∫ ω, I T ω ^ 2 ∂P) = E := by
    rw [hsqEq, integral_add (hmq.integrable T) (integrable_const E)]
    rw [hQmean]
    simp
  change (∫ ω, c + I T ω ∂P) = c ∧
    (∫ ω, ((c + I T ω) - c) ^ 2 ∂P) = E
  constructor
  · rw [integral_add (integrable_const c) (hm.integrable T)]
    simp [hmeanT]
  · simpa only [add_sub_cancel_left] using hsqMean
