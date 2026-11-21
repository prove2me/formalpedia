-- Prove2me | Definitions.Def_SourceProof_01f7c70491ce7157ce54880f
-- name    : SourceProof_01f7c70491ce7157ce54880f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:00:46.83146+00:00
-- url     : https://prove2.me/theorems/13d637f6-8989-42db-a475-52ddb3e96ee9
-- title:
--   LevyStochCalc source module: SourceProof_01f7c70491ce7157ce54880f
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormulaTime` comes from the `LevyStochCalc.Brownian.VectorItoTimeFormula` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F003
import Definitions.Def_LevyStochCalc_Brownian_VectorItoTimeAug_F001
import Definitions.Def_SourceProof_2631a3786acbcf68272d1d52
import Definitions.Def_SourceProof_48bb348bd252ccd46dd07812

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for a time-dependent function of a vector Itô process

Applying the state-only formula to the process augmented by its own time separates the time
derivative — paired with the unit drift of the extra coordinate — from the space derivatives.
The extra coordinate carries no diffusion, so it contributes neither a stochastic integral nor a
quadratic-variation term.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormulaTime` — Itô's formula for a
  time-dependent function.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section TimeFormula

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
  {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)}
  {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H p k ω s| ≤ C)

include hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_01f7c70491ce7157ce54880f
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hX₀ : ∀ q : Fin n, Measurable fun ω => X₀ ω q)
    (hbm : ∀ q, Measurable (Function.uncurry (bdrift q))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (q : Fin n) (ω : Ω) (s : ℝ), |bdrift q ω s| ≤ B)
    (hqa : ∀ (p q : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {f : (Fin (n + 1) → ℝ) → ℝ} {f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hfC : ContDiff ℝ 2 f)
    (hmg : ∀ (q : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      coordDeriv f' q.succ (timeAugProcess X s ω) * H q k ω s))
    (hpg : ∀ (q : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ
      fun ω s => coordDeriv f' q.succ (timeAugProcess X s ω) * H q k ω s)
    (hqg : ∀ (q : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' q.succ (timeAugProcess X s ω) * H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f (timeAugProcess X T ω) - f (timeAugProcess X 0 ω)) =ᵐ[P] fun ω : Ω =>
      (∫ s in Set.Ioc (0 : ℝ) T, coordDeriv f' 0 (timeAugProcess X s ω) ∂volume)
        + (∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv f' q.succ (timeAugProcess X s ω) * bdrift q ω s ∂volume)
        + (∑ q : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
            (fun ω s => coordDeriv f' q.succ (timeAugProcess X s ω) * H q k ω s)
            (hmg q k) (hpg q k) (hqg q k) T ω)
        + 1 / 2 * ∑ q : Fin n, ∑ q' : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' q.succ q'.succ (timeAugProcess X s ω)
              * ∑ k : Fin d, H q k ω s * H q' k ω s ∂volume := by
  classical
  have hX₀' : ∀ p : Fin (n + 1), Measurable fun ω => LevyStochCalc.Brownian.Ito.timeAugInit X₀ ω p := by
    intro p
    induction p using Fin.cases with
    | zero =>
      simp only [LevyStochCalc.Brownian.Ito.timeAugInit, Fin.cons_zero]
      exact measurable_const
    | succ q => simpa [LevyStochCalc.Brownian.Ito.timeAugInit] using hX₀ q
  have hmgA := LevyStochCalc.Brownian.Ito.measurable_timeAugWeight f' X H hmg
  have hpgA := LevyStochCalc.Brownian.Ito.progressivelyMeasurable_timeAugWeight f' X H ℱ hpg
  have hqgA := LevyStochCalc.Brownian.Ito.sq_timeAugWeight f' X H hqg
  have hq0 : ∀ T' : ℝ, 0 < T' → ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T',
      (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro T' _
    simp
  have hSI0 : ∀ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
      (fun ω s => LevyStochCalc.coordDeriv f' (0 : Fin (n + 1)) (LevyStochCalc.Brownian.Ito.timeAugProcess X s ω)
        * LevyStochCalc.Brownian.Ito.timeAugDiffusion H 0 k ω s) (hmgA 0 k) (hpgA 0 k) (hqgA 0 k) T =ᵐ[P] 0 := by
    intro k
    have heq : (fun ω s => LevyStochCalc.coordDeriv f' (0 : Fin (n + 1)) (LevyStochCalc.Brownian.Ito.timeAugProcess X s ω)
        * LevyStochCalc.Brownian.Ito.timeAugDiffusion H 0 k ω s) = fun (_ : Ω) (_ : ℝ) => (0 : ℝ) := by
      funext ω s
      simp [LevyStochCalc.Brownian.Ito.timeAugDiffusion]
    rw [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun (W.W k) ℱ (hcoord k) heq (hmgA 0 k) (hpgA 0 k)
      (hqgA 0 k) measurable_const (LevyStochCalc.Probability.progressivelyMeasurable_const ℱ (0 : ℝ)) hq0 T]
    exact _root_.Prove2MeSourceProof.h_2631a3786acbcf68272d1d52 (W.W k) ℱ (hcoord k) _ _ _ T
  have hform := ((_root_.Prove2MeSourceProof.h_48bb348bd252ccd46dd07812 h)).itoFormula_of_contDiff hC0 (LevyStochCalc.Brownian.Ito.abs_timeAugDiffusion_le H hC0 hCH) hX₀'
    (LevyStochCalc.Brownian.Ito.measurable_timeAugDrift bdrift hbm) (le_trans hB0 (le_max_left B 1))
    (LevyStochCalc.Brownian.Ito.abs_timeAugDrift_le bdrift hB) (LevyStochCalc.Brownian.Ito.measurable_timeAugDiffusion_add H hHm)
    (LevyStochCalc.Brownian.Ito.progressivelyMeasurable_timeAugDiffusion_add H ℱ hHp)
    (LevyStochCalc.Brownian.Ito.sq_timeAugDiffusion_add H hHs hqa) hfC hf hf'
    hmgA hpgA hqgA hT
  filter_upwards [hform, MeasureTheory.ae_all_iff.mpr hSI0] with ω hω hz
  rw [hω]
  have hA : (∑ p : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
        LevyStochCalc.coordDeriv f' p (LevyStochCalc.Brownian.Ito.timeAugProcess X s ω) * LevyStochCalc.Brownian.Ito.timeAugDrift bdrift p ω s ∂volume)
      = (∫ s in Set.Ioc (0 : ℝ) T, LevyStochCalc.coordDeriv f' 0 (LevyStochCalc.Brownian.Ito.timeAugProcess X s ω) ∂volume)
        + ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            LevyStochCalc.coordDeriv f' q.succ (LevyStochCalc.Brownian.Ito.timeAugProcess X s ω) * bdrift q ω s ∂volume := by
    rw [Fin.sum_univ_succ]
    congr 1
    simp [LevyStochCalc.Brownian.Ito.timeAugDrift]
  have hbridge : ∀ (q : Fin n) (k : Fin d),
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
          (fun ω s => LevyStochCalc.coordDeriv f' q.succ (LevyStochCalc.Brownian.Ito.timeAugProcess X s ω)
            * LevyStochCalc.Brownian.Ito.timeAugDiffusion H q.succ k ω s)
          (hmgA q.succ k) (hpgA q.succ k) (hqgA q.succ k) T ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
          (fun ω s => LevyStochCalc.coordDeriv f' q.succ (LevyStochCalc.Brownian.Ito.timeAugProcess X s ω) * H q k ω s)
          (hmg q k) (hpg q k) (hqg q k) T ω := by
    intro q k
    have heq : (fun ω s => LevyStochCalc.coordDeriv f' q.succ (LevyStochCalc.Brownian.Ito.timeAugProcess X s ω)
          * LevyStochCalc.Brownian.Ito.timeAugDiffusion H q.succ k ω s)
        = fun ω s => LevyStochCalc.coordDeriv f' q.succ (LevyStochCalc.Brownian.Ito.timeAugProcess X s ω) * H q k ω s := by
      funext ω s
      simp [LevyStochCalc.Brownian.Ito.timeAugDiffusion]
    exact congrFun (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun (W.W k) ℱ (hcoord k) heq
      (hmgA q.succ k) (hpgA q.succ k) (hqgA q.succ k) (hmg q k) (hpg q k) (hqg q k) T) ω
  have hB' : (∑ p : Fin (n + 1), ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
        (fun ω s => LevyStochCalc.coordDeriv f' p (LevyStochCalc.Brownian.Ito.timeAugProcess X s ω) * LevyStochCalc.Brownian.Ito.timeAugDiffusion H p k ω s)
        (hmgA p k) (hpgA p k) (hqgA p k) T ω)
      = ∑ q : Fin n, ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
          (fun ω s => LevyStochCalc.coordDeriv f' q.succ (LevyStochCalc.Brownian.Ito.timeAugProcess X s ω) * H q k ω s)
          (hmg q k) (hpg q k) (hqg q k) T ω := by
    rw [Fin.sum_univ_succ, Finset.sum_eq_zero fun k _ => hz k, zero_add]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun k _ => hbridge q k
  have hC' : (∑ p : Fin (n + 1), ∑ p' : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
        LevyStochCalc.coordDeriv₂ f'' p p' (LevyStochCalc.Brownian.Ito.timeAugProcess X s ω)
          * ∑ k : Fin d, LevyStochCalc.Brownian.Ito.timeAugDiffusion H p k ω s * LevyStochCalc.Brownian.Ito.timeAugDiffusion H p' k ω s ∂volume)
      = ∑ q : Fin n, ∑ q' : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          LevyStochCalc.coordDeriv₂ f'' q.succ q'.succ (LevyStochCalc.Brownian.Ito.timeAugProcess X s ω)
            * ∑ k : Fin d, H q k ω s * H q' k ω s ∂volume := by
    rw [Fin.sum_univ_succ, Finset.sum_eq_zero fun p' _ => by simp [LevyStochCalc.Brownian.Ito.timeAugDiffusion], zero_add]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Fin.sum_univ_succ]
    rw [show (∫ s in Set.Ioc (0 : ℝ) T, LevyStochCalc.coordDeriv₂ f'' q.succ 0 (LevyStochCalc.Brownian.Ito.timeAugProcess X s ω)
        * ∑ k : Fin d, LevyStochCalc.Brownian.Ito.timeAugDiffusion H q.succ k ω s * LevyStochCalc.Brownian.Ito.timeAugDiffusion H 0 k ω s ∂volume)
        = 0 from by simp [LevyStochCalc.Brownian.Ito.timeAugDiffusion], zero_add]
    exact Finset.sum_congr rfl fun q' _ => by simp [LevyStochCalc.Brownian.Ito.timeAugDiffusion]
  rw [hA, hB', hC']
end TimeFormula

end LevyStochCalc.Brownian.Ito


