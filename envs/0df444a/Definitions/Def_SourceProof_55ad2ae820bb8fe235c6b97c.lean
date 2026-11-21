-- Prove2me | Definitions.Def_SourceProof_55ad2ae820bb8fe235c6b97c
-- name    : SourceProof_55ad2ae820bb8fe235c6b97c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:31:05.606178+00:00
-- url     : https://prove2.me/theorems/0ae121f7-edeb-4973-928d-1e7e35f750dc
-- title:
--   LevyStochCalc source module: SourceProof_55ad2ae820bb8fe235c6b97c
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.itoFormula_between` comes from the `LevyStochCalc.Ito.ItoFormulaIncrement` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaIncrement_F000
import Definitions.Def_SourceProof_bec416f96d2158f67c5c93e0

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for the increment of a path between two stopping times

Subtracting Itô's formula along the path stopped at one stopping time from Itô's formula along
the path stopped at another recombines into a single formula for the increment between the two
clipped horizons: each Lebesgue integral becomes the integral of the increment of the cut-off
integrand, and the two Itô integrals become the single Itô integral of that increment.

## Main statements

* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_sub` — the Itô integral of the
  increment between two cut-offs of an integrand is the difference of the two Itô integrals.
* `LevyStochCalc.Brownian.Ito.ae_integrableOn_stopped_Ioc` — a cut-off integrand of finite energy
  is almost surely integrable on a bounded window.
* `LevyStochCalc.Brownian.Ito.ae_integrableOn_stopped_Ioc_of_ae_integrableOn` — cutting off at a
  stopping time preserves almost sure integrability on a bounded window.
* `LevyStochCalc.Brownian.Ito.itoFormula_between` — Itô's formula for the increment of a path
  between two stopping times.
* `LevyStochCalc.Brownian.Ito.itoFormula_stopped_general_shift` — Itô's formula along a path
  stopped at an arbitrary stopping time, for a function translated by a fixed vector.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_shift` — the increment formula for a function
  translated by a fixed vector.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section IncrementAdmissible

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

end IncrementAdmissible

section IncrementEnergy

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end IncrementEnergy

section IncrementItoIntegral

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end IncrementItoIntegral

section Between

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

include hcoord in

theorem _root_.Prove2MeSourceProof.h_55ad2ae820bb8fe235c6b97c
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : IsVectorItoVersion W ℱ' hcoord H hHm hHp hHs X₀ bdrift X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (hX₀ : ∀ p : Fin n, Measurable[ℱ' 0] fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ' (bdrift p))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ' σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ' τ)
    (hσ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ σ ω)
    (hτ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ τ ω)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hmG : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpG : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqG : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmD : ∀ p : Fin n, Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s))
    (hqD : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmQ : ∀ p q : Fin n, Measurable (Function.uncurry
      fun ω s => coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s))
    {T : ℝ} (hT : 0 < T)
    (hQint : ∀ᵐ ω ∂P, ∀ p q : Fin n, MeasureTheory.IntegrableOn
      (fun s => coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s)
      (Set.Ioc (0 : ℝ) T) volume) :
    (fun ω : Ω => f (X (clipTime τ T ω) ω) - f (X (clipTime σ T ω) ω)) =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          (Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s) ω s) ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s =>
              Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω) * H p k ω s) ω s
                - Probability.stopped σ
                    (fun ω s => coordDeriv f' p (X s ω) * H p k ω s) ω s)
            (measurable_uncurry_stopped_sub hσ hτ (hmG p k))
            (progressivelyMeasurable_stopped_sub hσ hτ (hpG p k))
            (energy_stopped_sub_lt_top hσ hτ (hmG p k) (hqG p k)) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
              - Probability.stopped σ (fun ω s => coordDeriv₂ f'' p q (X s ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume := by
  classical
  have hmSτ : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      (LevyStochCalc.Probability.stopped τ fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)) :=
    fun p k => LevyStochCalc.Probability.measurable_uncurry_stopped hτ (hmG p k)
  have hpSτ : ∀ (p : Fin n) (k : Fin d), LevyStochCalc.Probability.ProgressivelyMeasurable ℱ'
      (LevyStochCalc.Probability.stopped τ fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s) :=
    fun p k => _root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hτ (hpG p k)
  have hqSτ : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖LevyStochCalc.Probability.stopped τ (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s) ω s‖₊
        : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun p k => LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le
      (fun ω s => LevyStochCalc.Probability.abs_stopped_le τ _ ω s) (hqG p k)
  have hmSσ : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      (LevyStochCalc.Probability.stopped σ fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)) :=
    fun p k => LevyStochCalc.Probability.measurable_uncurry_stopped hσ (hmG p k)
  have hpSσ : ∀ (p : Fin n) (k : Fin d), LevyStochCalc.Probability.ProgressivelyMeasurable ℱ'
      (LevyStochCalc.Probability.stopped σ fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s) :=
    fun p k => _root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hσ (hpG p k)
  have hqSσ : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖LevyStochCalc.Probability.stopped σ (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s) ω s‖₊
        : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun p k => LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le
      (fun ω s => LevyStochCalc.Probability.abs_stopped_le σ _ ω s) (hqG p k)
  have hτres := _root_.Prove2MeSourceProof.h_bec416f96d2158f67c5c93e0 W ℱ' hcoord h hℱ0 hnull hX₀ hbm hbp hbq hτ hτ0
    hfC hf hf' hmSτ hpSτ hqSτ hT
  have hσres := _root_.Prove2MeSourceProof.h_bec416f96d2158f67c5c93e0 W ℱ' hcoord h hℱ0 hnull hX₀ hbm hbp hbq hσ hσ0
    hfC hf hf' hmSσ hpSσ hqSσ hT
  have hsub : ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d),
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (fun ω s =>
            LevyStochCalc.Probability.stopped τ (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s) ω s
              - LevyStochCalc.Probability.stopped σ
                  (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s) ω s)
          (LevyStochCalc.Brownian.Ito.measurable_uncurry_stopped_sub hσ hτ (hmG p k))
          (LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub hσ hτ (hpG p k))
          (LevyStochCalc.Brownian.Ito.energy_stopped_sub_lt_top hσ hτ (hmG p k) (hqG p k)) T ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (LevyStochCalc.Probability.stopped τ fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
            (hmSτ p k) (hpSτ p k) (hqSτ p k) T ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (LevyStochCalc.Probability.stopped σ fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
            (hmSσ p k) (hpSσ p k) (hqSσ p k) T ω := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    intro k
    exact LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_sub (W.W k) ℱ' (hcoord k) hσ hτ
      (hmG p k) (hpG p k) (hqG p k) hT
  have hDτ : ∀ᵐ ω ∂P, ∀ p : Fin n, MeasureTheory.IntegrableOn
      (LevyStochCalc.Probability.stopped τ (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s) ω)
      (Set.Ioc (0 : ℝ) T) volume := by
    rw [MeasureTheory.ae_all_iff]
    exact fun p => LevyStochCalc.Brownian.Ito.ae_integrableOn_stopped_Ioc hτ (hmD p) (hqD p) hT
  have hDσ : ∀ᵐ ω ∂P, ∀ p : Fin n, MeasureTheory.IntegrableOn
      (LevyStochCalc.Probability.stopped σ (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s) ω)
      (Set.Ioc (0 : ℝ) T) volume := by
    rw [MeasureTheory.ae_all_iff]
    exact fun p => LevyStochCalc.Brownian.Ito.ae_integrableOn_stopped_Ioc hσ (hmD p) (hqD p) hT
  have hQ1 : ∀ p q : Fin n, ∀ᵐ ω ∂P, MeasureTheory.IntegrableOn
      (fun s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s)
      (Set.Ioc (0 : ℝ) T) volume := by
    intro p q
    filter_upwards [hQint] with ω hω using hω p q
  have hQτ : ∀ᵐ ω ∂P, ∀ p q : Fin n, MeasureTheory.IntegrableOn
      (LevyStochCalc.Probability.stopped τ (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
        * ∑ k : Fin d, H p k ω s * H q k ω s) ω) (Set.Ioc (0 : ℝ) T) volume := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    exact fun q => LevyStochCalc.Brownian.Ito.ae_integrableOn_stopped_Ioc_of_ae_integrableOn hτ (hmQ p q) (hQ1 p q)
  have hQσ : ∀ᵐ ω ∂P, ∀ p q : Fin n, MeasureTheory.IntegrableOn
      (LevyStochCalc.Probability.stopped σ (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
        * ∑ k : Fin d, H p k ω s * H q k ω s) ω) (Set.Ioc (0 : ℝ) T) volume := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    exact fun q => LevyStochCalc.Brownian.Ito.ae_integrableOn_stopped_Ioc_of_ae_integrableOn hσ (hmQ p q) (hQ1 p q)
  filter_upwards [hτres, hσres, hsub, hDτ, hDσ, hQτ, hQσ] with ω e1 e2 e3 e4 e5 e6 e7
  have hA : (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
        (LevyStochCalc.Probability.stopped τ (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s) ω s
          - LevyStochCalc.Probability.stopped σ
              (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s) ω s) ∂volume)
      = (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          LevyStochCalc.Probability.stopped τ
            (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s) ω s ∂volume)
        - ∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            LevyStochCalc.Probability.stopped σ
              (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s) ω s ∂volume := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => MeasureTheory.integral_sub (e4 p) (e5 p)
  have hB : (∑ p : Fin n, ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
        (fun ω s =>
          LevyStochCalc.Probability.stopped τ (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s) ω s
            - LevyStochCalc.Probability.stopped σ
                (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s) ω s)
        (LevyStochCalc.Brownian.Ito.measurable_uncurry_stopped_sub hσ hτ (hmG p k))
        (LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub hσ hτ (hpG p k))
        (LevyStochCalc.Brownian.Ito.energy_stopped_sub_lt_top hσ hτ (hmG p k) (hqG p k)) T ω)
      = (∑ p : Fin n, ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (LevyStochCalc.Probability.stopped τ fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
          (hmSτ p k) (hpSτ p k) (hqSτ p k) T ω)
        - ∑ p : Fin n, ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (LevyStochCalc.Probability.stopped σ fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
            (hmSσ p k) (hpSσ p k) (hqSσ p k) T ω := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => e3 p k
  have hC : (∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
        (LevyStochCalc.Probability.stopped τ (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
            * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
          - LevyStochCalc.Probability.stopped σ (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
              * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume)
      = (∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          LevyStochCalc.Probability.stopped τ (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
            * ∑ k : Fin d, H p k ω s * H q k ω s) ω s ∂volume)
        - ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            LevyStochCalc.Probability.stopped σ (fun ω s => LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
              * ∑ k : Fin d, H p k ω s * H q k ω s) ω s ∂volume := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => MeasureTheory.integral_sub (e6 p q) (e7 p q)
  rw [hA, hB, hC]
  linarith [e1, e2]
end Between

end LevyStochCalc.Brownian.Ito


