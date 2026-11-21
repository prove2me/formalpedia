-- Prove2me | Definitions.Def_SourceProof_68bcc04d25dcb303fabb8713
-- name    : SourceProof_68bcc04d25dcb303fabb8713
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:47:42.325487+00:00
-- url     : https://prove2.me/theorems/82c9980f-e98b-468d-bd1e-2667530db5a1
-- title:
--   LevyStochCalc source module: SourceProof_68bcc04d25dcb303fabb8713
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.exists_markStep_close` comes from the `LevyStochCalc.Poisson.CompensatedApprox` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedApprox_F000
import Definitions.Def_LevyStochCalc_Poisson_MarkStepIncrement_F000
import Definitions.Def_SourceProof_98f8d351dfc96ce2a734c0bf

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Approximation of a square-integrable integrand by mark-step integrands

For a jointly measurable, progressively measurable integrand `φ : Ω → ℝ → E → ℝ` that is
square integrable over `Ω × [0, T] × E`, and any dyadic level `L₀` and tolerance `ε`, there is
an adapted mark-step integrand on a dyadic grid of level at least `L₀` within `ε` of `φ` in
`L²(P ⊗ ds ⊗ ν)` on `[0, T]` (`exists_markStep_close`). The integrand is first clipped and
restricted to a mark set of finite measure (`truncate`), which reduces to the bounded,
finitely supported case treated by `exists_markEval_L2_tendsto`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

section Truncate

variable (φ : Ω → ℝ → E → ℝ) (M : ℝ) (S : Set E)

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

end Truncate

section Close

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)

include N h_meas h_progMeas in

theorem _root_.Prove2MeSourceProof.h_68bcc04d25dcb303fabb8713 {T : ℝ} (hT : 0 < T)
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (L₀ : ℕ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ ℓ : ℕ, L₀ ≤ ℓ ∧ ∃ G : MarkStep Ω E ν (TimeGrid.dyadic T hT ℓ), G.Adapted ℱ ∧
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ε := by
  classical
  have hε4 : 0 < ε / 4 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨M, S, hS, hSfin, hMS⟩ := LevyStochCalc.Poisson.Compensated.exists_truncate_close φ h_meas h_sq_int hε4
  have hψm := LevyStochCalc.Poisson.Compensated.truncate_measurable φ M S h_meas hS
  have hψp := LevyStochCalc.Poisson.Compensated.truncate_progMeas φ M S ℱ h_progMeas (Nat.cast_nonneg M) hS
  obtain ⟨Ki, Bi, ci, hBim, hBiS, hcia, hcib, htend⟩ :=
    _root_.Prove2MeSourceProof.h_98f8d351dfc96ce2a734c0bf N ℱ hT (LevyStochCalc.Poisson.Compensated.truncate φ M S) hψm hψp
      (LevyStochCalc.Poisson.Compensated.truncate_abs_le φ M S (Nat.cast_nonneg M)) hS hSfin
      (fun ω e he u => LevyStochCalc.Poisson.Compensated.truncate_eq_zero φ M S ω he u)
  obtain ⟨ℓ, hℓerr, hℓ⟩ :=
    ((htend.eventually (Iio_mem_nhds hε4)).and (Filter.eventually_ge_atTop L₀)).exists
  have hcim : ∀ i k, Measurable (ci ℓ i k) := fun i k =>
    (hcia ℓ i k).measurable.mono (ℱ.le _) le_rfl
  obtain ⟨K, B, ξ, hBm, hBf, hξb, hξm, hξa, hF⟩ :=
    _root_.Prove2MeSourceProof.h_38bd2809fbf8ffc383f84cb8 N ℱ (LevyStochCalc.Poisson.Compensated.dyadicPartition T ℓ) (Bi ℓ) (ci ℓ) (hBim ℓ)
      (fun i k => ne_top_of_le_ne_top hSfin (measure_mono (hBiS ℓ i k))) (hcib ℓ) hcim (hcia ℓ)
  let G : LevyStochCalc.Poisson.Compensated.MarkStep Ω E ν (LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic T hT ℓ) :=
    { K := K
      B := B
      B_measurable := hBm
      B_finite := hBf
      ξ := fun i k => if h : i < 2 ^ ℓ then ξ ⟨i, h⟩ k else 0
      ξ_bounded := fun i k => by
        by_cases h : i < 2 ^ ℓ
        · rw [dif_pos h]
          exact hξb ⟨i, h⟩ k
        · rw [dif_neg h]
          exact ⟨0, fun ω => by simp⟩
      ξ_measurable := fun i k => by
        by_cases h : i < 2 ^ ℓ
        · rw [dif_pos h]
          exact hξm ⟨i, h⟩ k
        · rw [dif_neg h]
          exact measurable_const }
  have hG : G.Adapted ℱ := by
    intro i hi k
    change @StronglyMeasurable Ω ℝ _ (ℱ ((LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic T hT ℓ).p i))
      (if h : i < 2 ^ ℓ then ξ ⟨i, h⟩ k else 0)
    rw [dif_pos (show i < 2 ^ ℓ from hi)]
    exact hξa ⟨i, hi⟩ k
  have heval : ∀ s e ω, G.eval s e ω = ∑ i : Fin (2 ^ ℓ),
      (Set.Ioc (LevyStochCalc.Poisson.Compensated.dyadicPartition T ℓ i.castSucc) (LevyStochCalc.Poisson.Compensated.dyadicPartition T ℓ i.succ)).indicator
        (fun _ => (1 : ℝ)) s
      * ∑ k, ci ℓ i k ω * (Bi ℓ i k).indicator (fun _ => (1 : ℝ)) e := by
    intro s e ω
    rw [LevyStochCalc.Poisson.Compensated.MarkStep.eval_eq_fin]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (Set.Ioc (LevyStochCalc.Poisson.Compensated.dyadicPartition T ℓ i.castSucc) (LevyStochCalc.Poisson.Compensated.dyadicPartition T ℓ i.succ)).indicator
        (fun _ => (1 : ℝ)) s
      * ∑ k, (if h : (i : ℕ) < 2 ^ ℓ then ξ ⟨i, h⟩ k else 0) ω
          * (B k).indicator (fun _ => (1 : ℝ)) e = _
    congr 1
    rw [show (∑ k, (if h : (i : ℕ) < 2 ^ ℓ then ξ ⟨i, h⟩ k else 0) ω
          * (B k).indicator (fun _ => (1 : ℝ)) e)
        = ∑ k, ξ ⟨i, i.isLt⟩ k ω * (B k).indicator (fun _ => (1 : ℝ)) e from
      Finset.sum_congr rfl fun k _ => by rw [dif_pos (show (i : ℕ) < 2 ^ ℓ from i.isLt)]]
    exact hF ⟨i, i.isLt⟩ ω (fun B' => B'.indicator (fun _ => (1 : ℝ)) e)
  have hmk : Measurable (fun p : Ω × ℝ × E => ∑ i : Fin (2 ^ ℓ),
      (Set.Ioc (LevyStochCalc.Poisson.Compensated.dyadicPartition T ℓ i.castSucc) (LevyStochCalc.Poisson.Compensated.dyadicPartition T ℓ i.succ)).indicator
        (fun _ => (1 : ℝ)) p.2.1
      * ∑ k, ci ℓ i k p.1 * (Bi ℓ i k).indicator (fun _ => (1 : ℝ)) p.2.2) := by
    have := G.eval_measurable
    simp_rw [heval] at this
    exact this
  refine ⟨ℓ, hℓ, G, hG, ?_⟩
  simp_rw [heval]
  exact LevyStochCalc.Poisson.Compensated.triple_sq_lt_of_lt h_meas hψm hMS hℓerr
end Close

section Master

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end Master

section Cauchy

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end Cauchy

end LevyStochCalc.Poisson.Compensated


