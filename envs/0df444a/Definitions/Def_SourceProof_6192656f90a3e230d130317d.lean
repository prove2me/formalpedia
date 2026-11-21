-- Prove2me | Definitions.Def_SourceProof_6192656f90a3e230d130317d
-- name    : SourceProof_6192656f90a3e230d130317d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:05:21.082543+00:00
-- url     : https://prove2.me/theorems/e20069f0-66c5-416e-aafc-ad3d50fccd68
-- title:
--   LevyStochCalc source module: SourceProof_6192656f90a3e230d130317d
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.adaptedSimple_dense_L2_brownian` comes from the `LevyStochCalc.Brownian.ItoDensityUnbounded` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F003
import Definitions.Def_SourceProof_68cf78692a1b2aaaa5a8b410
import Definitions.Def_SourceProof_e4a003adac246e81fe5cee0f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Density of the simple predictable processes in `L²`

Removal of the boundedness restriction by truncation: the `eLpNorm`/`lintegral`
dictionary on the product measure, and the density results `simplePredictable_dense_L2`
and `adaptedSimple_dense_L2_brownian` for an arbitrary square-integrable integrand.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.
set_option maxHeartbeats 1600000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.

theorem _root_.Prove2MeSourceProof.h_6192656f90a3e230d130317d
    {P : Measure Ω} [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (hT : 0 < T)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ Hn : ℕ → SimplePredictable Ω T,
      (∀ n : ℕ, ∀ i : Fin (Hn n).N,
        @MeasureTheory.StronglyMeasurable Ω ℝ _
          (ℱ ((Hn n).partition i.castSucc)) ((Hn n).ξ i)) ∧
      Filter.Tendsto
        (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        Filter.atTop (nhds 0) := by
  -- Truncation preserves measurability + progressive measurability.
  have h_clip_bound : ∀ M : ℕ, ∀ ω s,
      |max (-(M : ℝ)) (min (M : ℝ) (H ω s))| ≤ (M : ℝ) := by
    intro M ω s
    have h_M_nn : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    rw [abs_le]
    refine ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have h_clip_meas : ∀ M : ℕ, Measurable
      (Function.uncurry (fun (ω : Ω) (s : ℝ) =>
        max (-(M : ℝ)) (min (M : ℝ) (H ω s)))) := by
    intro M
    have h : Measurable (fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x)) := by fun_prop
    exact h.comp h_meas
  -- Progressive measurability preserved under continuous clip.
  have h_clip_progMeas : ∀ M : ℕ, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
      (fun ω s => max (-(M : ℝ)) (min (M : ℝ) (H ω s))) := by
    intro M
    have h_clip_cont : Continuous (fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x)) := by
      fun_prop
    have h_clip_zero : max (-(M : ℝ)) (min (M : ℝ) 0) = 0 := by
      rw [min_eq_right (Nat.cast_nonneg M), max_eq_right (neg_nonpos.mpr (Nat.cast_nonneg M))]
    exact h_clip_cont.comp_progressivelyMeasurable h_clip_zero h_progMeas
  -- Apply bounded adapted-density.
  have h_bdd : ∀ M : ℕ, ∃ Hn : ℕ → LevyStochCalc.Brownian.Ito.SimplePredictable Ω T,
      (∀ n : ℕ, ∀ i : Fin (Hn n).N,
        @MeasureTheory.StronglyMeasurable Ω ℝ _
          (ℱ ((Hn n).partition i.castSucc)) ((Hn n).ξ i)) ∧
      Filter.Tendsto
        (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖max (-(M : ℝ)) (min (M : ℝ) (H ω s)) - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P)
        Filter.atTop (nhds 0) :=
    fun M => LevyStochCalc.Brownian.Ito.adaptedSimple_dense_L2_bounded_brownian ℱ hT
      (fun ω s => max (-(M : ℝ)) (min (M : ℝ) (H ω s)))
      (h_clip_meas M) (h_clip_progMeas M) (M : ℝ) (h_clip_bound M)
  choose Hn_seq h_Hn_adapt h_Hn_seq using h_bdd
  -- Same diagonal selection as simplePredictable_dense_L2.
  have h_N : ∀ n : ℕ, ∃ N : ℕ, ∀ k ≥ N,
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
            - (Hn_seq n k).eval s ω‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P) ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    have h_eps : ((n : ℝ≥0∞) + 1)⁻¹ > 0 := by
      apply ENNReal.inv_pos.mpr
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, by simp⟩
    exact (ENNReal.tendsto_atTop_zero.mp (h_Hn_seq n)) _ h_eps
  choose N_seq h_N_seq using h_N
  refine ⟨fun n => Hn_seq n (max n (N_seq n)), ?_, ?_⟩
  · -- Adaptedness inherited.
    intro n i
    exact h_Hn_adapt n (max n (N_seq n)) i
  -- Convergence: same proof as simplePredictable_dense_L2.
  have h_trunc := _root_.Prove2MeSourceProof.h_68cf78692a1b2aaaa5a8b410 H h_meas h_sq_int (T := T)
  rw [ENNReal.tendsto_atTop_zero] at h_trunc ⊢
  intro ε hε_pos
  have hε4_pos : (0 : ℝ≥0∞) < ε / 4 := by
    rw [ENNReal.div_pos_iff]
    refine ⟨hε_pos.ne', ?_⟩
    decide
  obtain ⟨N₁, hN₁⟩ := h_trunc (ε / 4) hε4_pos
  have h_inv_tendsto : Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹)
      Filter.atTop (nhds 0) := by
    have h := ENNReal.tendsto_inv_nat_nhds_zero
    have hcomp :
        Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) Filter.atTop (nhds 0) :=
      h.comp (Filter.tendsto_add_atTop_nat 1)
    simpa [Nat.cast_add, Nat.cast_one] using hcomp
  obtain ⟨N₂, hN₂⟩ := (ENNReal.tendsto_atTop_zero.mp h_inv_tendsto) (ε / 4) hε4_pos
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := le_of_max_le_left hn
  have hn₂ : N₂ ≤ n := le_of_max_le_right hn
  have h_pointwise : ∀ ω s,
      (‖H ω s - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2
            + (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
                  - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2) := by
    intro ω s
    have h_sum : (H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s)))
        + (max (-(n : ℝ)) (min (n : ℝ) (H ω s))
            - (Hn_seq n (max n (N_seq n))).eval s ω)
        = H ω s - (Hn_seq n (max n (N_seq n))).eval s ω := by ring
    have := _root_.Prove2MeSourceProof.h_e4a003adac246e81fe5cee0f
      (H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s)))
      (max (-(n : ℝ)) (min (n : ℝ) (H ω s))
        - (Hn_seq n (max n (N_seq n))).eval s ω)
    rw [h_sum] at this
    exact this
  set A : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖H ω s
      - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2 with hA
  set B : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
                    - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2 with hB
  set C : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖H ω s - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2 with hC
  have h_C_le : ∀ ω s, C ω s ≤ 2 * (A ω s + B ω s) := h_pointwise
  have h_s_le : ∀ ω,
      (∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume) ≤
        2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
          + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) := by
    intro ω
    calc (∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume)
        ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, 2 * (A ω s + B ω s) ∂volume :=
          MeasureTheory.lintegral_mono (h_C_le ω)
      _ = 2 * ∫⁻ s in Set.Icc (0 : ℝ) T, (A ω s + B ω s) ∂volume := by
          rw [MeasureTheory.lintegral_const_mul']
          simp
      _ = 2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
          + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) := by
          congr 1
          rw [MeasureTheory.lintegral_add_left']
          have h_meas_A_s : Measurable (fun s => A ω s) := by
            simp only [hA]
            exact ((by fun_prop : Measurable (fun s =>
              ‖H ω s
                - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊)).coe_nnreal_ennreal).pow_const 2
          exact h_meas_A_s.aemeasurable
  have h_double_le :
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume ∂P)
      ≤ 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P) := by
    calc (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume ∂P)
        ≤ ∫⁻ ω,
            2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
              + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) ∂P :=
          MeasureTheory.lintegral_mono h_s_le
      _ = 2 * ∫⁻ ω,
            ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
              + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) ∂P := by
          rw [MeasureTheory.lintegral_const_mul']
          simp
      _ = 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P) := by
          congr 1
          rw [MeasureTheory.lintegral_add_left']
          have h_meas_A_pair : Measurable (fun (q : Ω × ℝ) => A q.1 q.2) := by
            simp only [hA]
            exact ((by fun_prop : Measurable (fun (q : Ω × ℝ) =>
              ‖H q.1 q.2
                - max (-(n : ℝ)) (min (n : ℝ) (H q.1 q.2))‖₊)).coe_nnreal_ennreal)
                  |>.pow_const 2
          exact (Measurable.lintegral_prod_right'
            (ν := volume.restrict (Set.Icc (0:ℝ) T)) h_meas_A_pair).aemeasurable
  have h_first : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2
      ∂volume ∂P) ≤ ε / 4 := hN₁ n hn₁
  have h_second : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
          - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2
      ∂volume ∂P) ≤ ε / 4 := by
    have h_max_ge : N_seq n ≤ max n (N_seq n) := le_max_right _ _
    exact (h_N_seq n (max n (N_seq n)) h_max_ge).trans (hN₂ n hn₂)
  calc (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P)
      ≤ 2 * (ε / 4 + ε / 4) := by
        refine h_double_le.trans ?_
        exact mul_le_mul_right (add_le_add h_first h_second) _
    _ = ε := by
        rw [← two_mul, ← mul_assoc, show (2 : ℝ≥0∞) * 2 = 4 from by norm_num]
        exact ENNReal.mul_div_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by simp)
-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.

end LevyStochCalc.Brownian.Ito


