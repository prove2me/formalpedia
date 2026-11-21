-- Prove2me | Definitions.Def_SourceProof_557f52677e345dfcfa63b53b
-- name    : SourceProof_557f52677e345dfcfa63b53b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:43:00.42512+00:00
-- url     : https://prove2.me/theorems/0ca07889-b0db-4638-b794-fd2ba4e16d5d
-- title:
--   LevyStochCalc source module: SourceProof_557f52677e345dfcfa63b53b
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.exists_itoIntegralL2_brownian_progMeas` comes from the `LevyStochCalc.Brownian.ItoL2CompletionExistence` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionExistence_F000
import Definitions.Def_SourceProof_68cf78692a1b2aaaa5a8b410

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: existence of the `L²` integral

Adaptedness, integrability and conditional-expectation identities for the
simple-integrand Brownian integral, and the existence statements they yield for
the `L²` Itô integral of a bounded, respectively progressively measurable and
square-integrable, integrand against a Brownian motion `W` on a Brownian
filtration `ℱ`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

set_option maxHeartbeats 1600000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.

theorem _root_.Prove2MeSourceProof.h_557f52677e345dfcfa63b53b
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (hT : 0 < T)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ Mlp : MeasureTheory.Lp ℝ 2 P,
      MeasureTheory.eLpNorm (↑↑Mlp : Ω → ℝ) 2 P ^ (2 : ℝ)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  -- Truncation helpers (mirrored from adaptedSimple_dense_L2_brownian).
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
  have h_clip_progMeas : ∀ M : ℕ, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
      (fun ω s => max (-(M : ℝ)) (min (M : ℝ) (H ω s))) := by
    intro M
    have h_clip_cont : Continuous (fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x)) := by
      fun_prop
    have h_clip_zero : max (-(M : ℝ)) (min (M : ℝ) 0) = 0 := by
      rw [min_eq_right (Nat.cast_nonneg M), max_eq_right (neg_nonpos.mpr (Nat.cast_nonneg M))]
    exact h_clip_cont.comp_progressivelyMeasurable h_clip_zero h_progMeas
  -- Bounded existence on each clipped function.
  have h_bdd : ∀ M : ℕ, ∃ Mlp_M : MeasureTheory.Lp ℝ 2 P,
      MeasureTheory.eLpNorm (↑↑Mlp_M : Ω → ℝ) 2 P ^ (2 : ℝ)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖max (-(M : ℝ)) (min (M : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
    fun M => LevyStochCalc.Brownian.Ito.exists_itoIntegralL2_brownian_progMeas_bounded W ℱ hℱ hT
      (fun ω s => max (-(M : ℝ)) (min (M : ℝ) (H ω s)))
      (h_clip_meas M) (h_clip_progMeas M) (M : ℝ) (h_clip_bound M)
  -- Pick N_seq for the diagonal: for each n, choose k ≥ N_seq n such that the
  -- L²-distance from clip_n H to the dyadic eval at depth k is ≤ 1/(n+1).
  have h_N : ∀ n : ℕ, ∃ N : ℕ, ∀ k ≥ N,
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s)) -
          (LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT
            (fun ω s => max (-(n : ℝ)) (min (n : ℝ) (H ω s)))
            (h_clip_meas n) (n : ℝ) (h_clip_bound n) k).eval s ω‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P) ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    have h_eps : ((n : ℝ≥0∞) + 1)⁻¹ > 0 := by
      apply ENNReal.inv_pos.mpr
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, by simp⟩
    have h_L2 := _root_.Prove2MeSourceProof.h_5731c142c22a48f56440eba3 (P := P) hT
      (fun ω s => max (-(n : ℝ)) (min (n : ℝ) (H ω s)))
      (h_clip_meas n) (n : ℝ) (h_clip_bound n)
    exact (ENNReal.tendsto_atTop_zero.mp h_L2) _ h_eps
  choose N_seq h_N_seq using h_N
  -- Diagonal sequence: G n = dyadic for clip_n H at depth (max n (N_seq n)).
  set G : ℕ → LevyStochCalc.Brownian.Ito.SimplePredictable Ω T := fun n =>
    LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT
      (fun ω s => max (-(n : ℝ)) (min (n : ℝ) (H ω s)))
      (h_clip_meas n) (n : ℝ) (h_clip_bound n) (max n (N_seq n)) with hG_def
  -- Properties of G.
  have h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N) := by
    intro n m
    rw [hG_def]
    rw [LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian_partition_last hT _
          (h_clip_meas n) (n : ℝ) (h_clip_bound n) (max n (N_seq n)),
        LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian_partition_last hT _
          (h_clip_meas m) (m : ℝ) (h_clip_bound m) (max m (N_seq m))]
  have h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ ((G n).partition i.castSucc)) ((G n).ξ i) := by
    intro n i
    exact LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian_adapted ℱ hT _
      (h_clip_meas n) (n : ℝ) (h_clip_bound n) (h_clip_progMeas n) (max n (N_seq n)) i
  have h_eval_meas : ∀ n,
      Measurable (fun (p : Ω × ℝ) => (G n).eval p.2 p.1) :=
    fun n => LevyStochCalc.Brownian.Ito.SimplePredictable.eval_jointly_measurable (G n)
  -- L²-convergence of G to H: diagonal lift.
  have h_trunc := _root_.Prove2MeSourceProof.h_68cf78692a1b2aaaa5a8b410 H h_meas h_sq_int (T := T)
  have h_L2_diff : Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - (G n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (nhds 0) := by
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
    -- Pointwise (a + b)² ≤ 2(a² + b²) splitting:
    -- ‖H - (G n).eval‖² ≤ 2 ‖H - clip_n H‖² + 2 ‖clip_n H - (G n).eval‖².
    have h_pointwise : ∀ ω s,
        (‖H ω s - (G n).eval s ω‖₊ : ℝ≥0∞) ^ 2
        ≤ 2 * ((‖H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2
              + (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
                    - (G n).eval s ω‖₊ : ℝ≥0∞) ^ 2) := by
      intro ω s
      have h_sum : (H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s)))
          + (max (-(n : ℝ)) (min (n : ℝ) (H ω s))
              - (G n).eval s ω)
          = H ω s - (G n).eval s ω := by ring
      have := _root_.Prove2MeSourceProof.h_e4a003adac246e81fe5cee0f
        (H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s)))
        (max (-(n : ℝ)) (min (n : ℝ) (H ω s))
          - (G n).eval s ω)
      rw [h_sum] at this
      exact this
    set A : Ω → ℝ → ℝ≥0∞ :=
      fun ω s => (‖H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2
        with hA
    set B : Ω → ℝ → ℝ≥0∞ :=
      fun ω s => (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
                      - (G n).eval s ω‖₊ : ℝ≥0∞) ^ 2 with hB
    set C : Ω → ℝ → ℝ≥0∞ :=
      fun ω s => (‖H ω s - (G n).eval s ω‖₊ : ℝ≥0∞) ^ 2 with hC
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
              have h1 : Measurable (fun s =>
                  ‖H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊) := by fun_prop
              exact (h1.coe_nnreal_ennreal).pow_const 2
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
                  - max (-(n : ℝ))
                      (min (n : ℝ) (H q.1 q.2))‖₊)).coe_nnreal_ennreal).pow_const 2
            exact (Measurable.lintegral_prod_right'
              (ν := volume.restrict (Set.Icc (0:ℝ) T)) h_meas_A_pair).aemeasurable
    have h_first : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P) ≤ ε / 4 := hN₁ n hn₁
    have h_second : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
            - (G n).eval s ω‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P) ≤ ε / 4 := by
      have h_max_ge : N_seq n ≤ max n (N_seq n) := le_max_right _ _
      exact (h_N_seq n (max n (N_seq n)) h_max_ge).trans (hN₂ n hn₂)
    calc (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H ω s - (G n).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P)
        ≤ 2 * (ε / 4 + ε / 4) := by
          refine h_double_le.trans ?_
          exact mul_le_mul_right (add_le_add h_first h_second) _
      _ = ε := by
          rw [← two_mul, ← mul_assoc, show (2 : ℝ≥0∞) * 2 = 4 from by norm_num]
          exact ENNReal.mul_div_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by simp)
  -- L²-Cauchy from L²-convergence.
  have h_cauchy_eval := _root_.Prove2MeSourceProof.h_6f312b3c41a43c93c4f0c9a1 (P := P) (T := T)
    G H h_eval_meas h_meas h_L2_diff
  -- Norm-tendsto from the general lemma.
  have h_norm_tendsto := _root_.Prove2MeSourceProof.h_cd0c957e24cb795d7143dc2e
    (μ := P) (T := T) H h_meas (fun n => (G n).eval) h_eval_meas h_L2_diff
  -- Apply exists_itoIntegralL2_brownian.
  exact LevyStochCalc.Brownian.Ito.exists_itoIntegralL2_brownian (P := P) W ℱ hℱ hT G h_eq h_adapt h_cauchy_eval H
    h_norm_tendsto
end LevyStochCalc.Brownian.Ito


