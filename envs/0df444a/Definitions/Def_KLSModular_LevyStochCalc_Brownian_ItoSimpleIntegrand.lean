-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoSimpleIntegrand
-- name    : KLSModular_LevyStochCalc_Brownian_ItoSimpleIntegrand
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:47:32.602965+00:00
-- url     : https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb
-- title:
--   Simple predictable integrands and their elementary Brownian integrals
-- statement:
--   Vendored from LevyStochCalc, repository https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `SimplePredictable Ω T` consists of a finite strictly increasing partition beginning at 0 and ending no later than T, together with bounded measurable coefficients ξᵢ : Ω → ℝ; filtration-adaptedness is not part of the structure. `SimplePredictable.eval` is the coefficient selected on the interval (tᵢ, tᵢ₊₁], and `simpleIntegral` is the finite sum of ξᵢ times the corresponding stopped Brownian increments. The auxiliary lemmas express evaluation as a sum of indicators, prove the partition intervals pairwise disjoint, and compute the inner and outer lower integrals of the squared nonnegative norm as sums weighted by interval lengths and coefficient energies.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.Multidim
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   structure SimplePredictable (Ω : Type u) [MeasurableSpace Ω] (T : ℝ) where
--     /-- Number of partition pieces. -/
--     N : ℕ
--     /-- Partition points `0 = t_0 < t_1 < ⋯ < t_N ≤ T`. -/
--     partition : Fin (N + 1) → ℝ
--     partition_zero : partition 0 = 0
--     partition_le_T : partition (Fin.last N) ≤ T
--     partition_strictMono : StrictMono partition
--     /-- Per-piece bounded coefficients `ξ_i : Ω → ℝ`. -/
--     ξ : Fin N → Ω → ℝ
--     /-- Each `ξ_i` is bounded. -/
--     ξ_bounded : ∀ i : Fin N, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M
--     /-- Each `ξ_i` is measurable. (Adaptedness — `ℱ_{t_i}`-measurability of
--     `ξ_i` for a filtration `ℱ` — is a separate hypothesis of the consumers; for
--     the L²-density argument the ambient measurability suffices.) -/
--     ξ_measurable : ∀ i : Fin N, Measurable (ξ i)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoSimpleIntegrand.lean) · `LevyStochCalc.Brownian.ItoSimpleIntegrand` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoSimpleIntegrand.lean#L28-L253 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoSimpleIntegrand`, definition bundle `KLSModular_LevyStochCalc_Brownian_ItoSimpleIntegrand`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Multidim

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoSimpleIntegrand.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Brownian
namespace Ito
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- A *simple predictable* integrand: a finite linear combination
`∑_i ξ_i · 1_{(t_i, t_{i+1}]}` where `ξ_i : Ω → ℝ` is `ℱ_{t_i}`-measurable
and bounded. We package the partition + the per-piece coefficient. -/
structure SimplePredictable (Ω : Type u) [MeasurableSpace Ω] (T : ℝ) where
  /-- Number of partition pieces. -/
  N : ℕ
  /-- Partition points `0 = t_0 < t_1 < ⋯ < t_N ≤ T`. -/
  partition : Fin (N + 1) → ℝ
  partition_zero : partition 0 = 0
  partition_le_T : partition (Fin.last N) ≤ T
  partition_strictMono : StrictMono partition
  /-- Per-piece bounded coefficients `ξ_i : Ω → ℝ`. -/
  ξ : Fin N → Ω → ℝ
  /-- Each `ξ_i` is bounded. -/
  ξ_bounded : ∀ i : Fin N, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M
  /-- Each `ξ_i` is measurable. (Adaptedness — `ℱ_{t_i}`-measurability of
  `ξ_i` for a filtration `ℱ` — is a separate hypothesis of the consumers; for
  the L²-density argument the ambient measurability suffices.) -/
  ξ_measurable : ∀ i : Fin N, Measurable (ξ i)
/-- Evaluate a simple predictable integrand at a fixed time. -/
noncomputable def SimplePredictable.eval {T : ℝ} (H : SimplePredictable Ω T)
    (t : ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin H.N,
    if H.partition i.castSucc < t ∧ t ≤ H.partition i.succ then H.ξ i ω else 0
/-- Integral of a simple predictable integrand against Brownian motion `W`:
`∑_i ξ_i (W_{t_{i+1}∧t} − W_{t_i∧t})`. -/
noncomputable def simpleIntegral
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin H.N,
    H.ξ i ω * (W.W (min (H.partition i.succ) t) ω
              - W.W (min (H.partition i.castSucc) t) ω)
/-- **`simpleIntegral` at time `T` collapses the `min` clauses.** Since
`partition_le_T` ensures `partition i.succ ≤ T` and `partition i.castSucc ≤ T`
for all `i : Fin H.N`, the `min` becomes the partition value. -/
lemma simpleIntegral_eq_sum
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) (ω : Ω) :
    simpleIntegral W H T ω
      = ∑ i : Fin H.N,
        H.ξ i ω * (W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω) := by
  unfold simpleIntegral
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h_part_le_succ : H.partition i.succ ≤ T := by
    refine le_trans ?_ H.partition_le_T
    exact H.partition_strictMono.monotone (Fin.le_last _)
  have h_part_le_castSucc : H.partition i.castSucc ≤ T :=
    le_of_lt ((H.partition_strictMono Fin.castSucc_lt_succ).trans_le h_part_le_succ)
  rw [min_eq_left h_part_le_succ, min_eq_left h_part_le_castSucc]
/-- **Eval as a sum of indicators.** Rewrite `H.eval s ω` as a sum of
indicator-functions of disjoint intervals `(t_i, t_{i+1}]`. -/
lemma eval_eq_sum_indicator {T : ℝ} (H : SimplePredictable Ω T) (s : ℝ) (ω : Ω) :
    H.eval s ω = ∑ i : Fin H.N,
      (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
        (fun _ => H.ξ i ω) s := by
  unfold SimplePredictable.eval
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : H.partition i.castSucc < s ∧ s ≤ H.partition i.succ
  · rw [if_pos h]
    rw [Set.indicator_of_mem (Set.mem_Ioc.mpr h)]
  · rw [if_neg h]
    rw [Set.indicator_of_notMem (fun hmem => h (Set.mem_Ioc.mp hmem))]
/-- **Disjoint intervals.** The intervals `(t_i, t_{i+1}]` for
`i : Fin H.N` are pairwise disjoint. -/
lemma partition_intervals_disjoint {T : ℝ} (H : SimplePredictable Ω T) :
    Pairwise (fun i j : Fin H.N => Disjoint
      (Set.Ioc (H.partition i.castSucc) (H.partition i.succ))
      (Set.Ioc (H.partition j.castSucc) (H.partition j.succ))) := by
  intro i j hij
  -- WLOG i < j (or j < i); then partition i.succ ≤ partition j.castSucc.
  rcases lt_or_gt_of_ne hij with h | h
  · -- i < j: i.succ ≤ j.castSucc, so (t_i, t_{i+1}] is to the left of (t_j, t_{j+1}]
    have h_succ_le : H.partition i.succ ≤ H.partition j.castSucc :=
      H.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr h)
    rw [Set.disjoint_iff]
    intro x ⟨hx_i, hx_j⟩
    obtain ⟨_, hx_i_le⟩ := Set.mem_Ioc.mp hx_i
    obtain ⟨hx_j_lt, _⟩ := Set.mem_Ioc.mp hx_j
    -- hx_i_le : x ≤ t_{i+1}, hx_j_lt : t_j < x. Combined with h_succ_le: contradiction.
    have : x ≤ H.partition j.castSucc := hx_i_le.trans h_succ_le
    exact absurd this (not_le.mpr hx_j_lt)
  · -- j < i: symmetric
    have h_succ_le : H.partition j.succ ≤ H.partition i.castSucc :=
      H.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr h)
    rw [Set.disjoint_iff]
    intro x ⟨hx_i, hx_j⟩
    obtain ⟨hx_i_lt, _⟩ := Set.mem_Ioc.mp hx_i
    obtain ⟨_, hx_j_le⟩ := Set.mem_Ioc.mp hx_j
    have : x ≤ H.partition i.castSucc := hx_j_le.trans h_succ_le
    exact absurd this (not_le.mpr hx_i_lt)
/-- **`‖H.eval s ω‖₊²` decomposes as a sum of indicator-squares** because
the partition intervals are pairwise disjoint, so at most one summand of
`H.eval` is nonzero at any `s`. -/
lemma eval_sq_eq_sum_indicator
    {T : ℝ} (H : SimplePredictable Ω T) (s : ℝ) (ω : Ω) :
    (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 = ∑ i : Fin H.N,
      (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
        (fun _ => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) s := by
  rw [eval_eq_sum_indicator]
  -- (∑ i, indicator A_i s · ξ_i ω)² with disjoint A_i.
  -- At most one indicator is nonzero at any s, so the square equals
  -- ∑ i, indicator A_i s · (ξ_i ω)².
  by_cases h_any : ∃ i : Fin H.N, s ∈ Set.Ioc (H.partition i.castSucc) (H.partition i.succ)
  · obtain ⟨i₀, hi₀⟩ := h_any
    -- At i₀, indicator gives ξ_{i₀}; at all other j, indicator gives 0 (by disjointness).
    have h_unique : ∀ j : Fin H.N, j ≠ i₀ →
        s ∉ Set.Ioc (H.partition j.castSucc) (H.partition j.succ) := by
      intro j hj hj_mem
      have := partition_intervals_disjoint H hj
      exact Set.disjoint_left.mp this hj_mem hi₀
    have h_sum_eq : (∑ i : Fin H.N,
        (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
          (fun _ => H.ξ i ω) s) = H.ξ i₀ ω := by
      rw [Finset.sum_eq_single i₀]
      · exact Set.indicator_of_mem hi₀ _
      · intro j _ hj
        exact Set.indicator_of_notMem (h_unique j hj) _
      · intro h_not; exact absurd (Finset.mem_univ _) h_not
    have h_sum_sq_eq : (∑ i : Fin H.N,
        (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
          (fun _ => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) s)
        = (‖H.ξ i₀ ω‖₊ : ℝ≥0∞) ^ 2 := by
      rw [Finset.sum_eq_single i₀]
      · exact Set.indicator_of_mem hi₀ _
      · intro j _ hj
        exact Set.indicator_of_notMem (h_unique j hj) _
      · intro h_not; exact absurd (Finset.mem_univ _) h_not
    rw [h_sum_eq, h_sum_sq_eq]
  · -- s is in none of the intervals; both sides are 0.
    push Not at h_any
    have h_zero : ∀ i : Fin H.N,
        (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
          (fun _ => H.ξ i ω) s = 0 :=
      fun i => Set.indicator_of_notMem (h_any i) _
    have h_zero_sq : ∀ i : Fin H.N,
        (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
          (fun _ => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) s = 0 :=
      fun i => Set.indicator_of_notMem (h_any i) _
    rw [Finset.sum_eq_zero (fun i _ => h_zero i),
        Finset.sum_eq_zero (fun i _ => h_zero_sq i)]
    simp
/-- **Inner lintegral of `‖H.eval s ω‖₊²` over `s ∈ [0, T]`** equals the sum
of `(t_{i+1} - t_i) · ‖ξ_i ω‖₊²` over partition pieces. -/
lemma lintegral_eval_sq {T : ℝ} (H : SimplePredictable Ω T) (ω : Ω) :
    ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume
      = ∑ i : Fin H.N,
        ENNReal.ofReal (H.partition i.succ - H.partition i.castSucc) *
        (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 := by
  -- Step 1: rewrite |H.eval|² as sum of indicators using `eval_sq_eq_sum_indicator`.
  rw [show (fun s => (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2)
      = (fun s => ∑ i : Fin H.N,
          (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
            (fun _ => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) s) from
    funext (eval_sq_eq_sum_indicator H · ω)]
  -- Step 2: pull sum out of lintegral.
  rw [MeasureTheory.lintegral_finsetSum]
  · -- Step 3: each summand evaluates to (t_{i+1} - t_i) · ‖ξ_i‖²
    refine Finset.sum_congr rfl (fun i _ => ?_)
    -- ∫⁻ s in [0, T], indicator (t_i, t_{i+1}] · |ξ_i|² ds = |ξ_i|² · vol((t_i, t_{i+1}])
    have h_meas_set : MeasurableSet
        (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)) := measurableSet_Ioc
    have h_subset : Set.Ioc (H.partition i.castSucc) (H.partition i.succ)
        ⊆ Set.Icc (0 : ℝ) T := by
      intro x hx
      have h_part_zero_le : 0 ≤ H.partition i.castSucc := by
        have : H.partition 0 ≤ H.partition i.castSucc :=
          H.partition_strictMono.monotone (Fin.zero_le _)
        rw [H.partition_zero] at this; exact this
      have h_part_succ_le_T : H.partition i.succ ≤ T := by
        refine le_trans ?_ H.partition_le_T
        exact H.partition_strictMono.monotone (Fin.le_last _)
      refine ⟨?_, ?_⟩
      · exact h_part_zero_le.trans (le_of_lt hx.1)
      · exact hx.2.trans h_part_succ_le_T
    rw [show (fun s => (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
              (fun _ => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) s)
          = (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
              (fun _ => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) from rfl]
    rw [MeasureTheory.lintegral_indicator h_meas_set]
    rw [MeasureTheory.setLIntegral_const]
    rw [show volume.restrict (Set.Icc (0 : ℝ) T)
            (Set.Ioc (H.partition i.castSucc) (H.partition i.succ))
          = volume (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)) from ?_]
    · rw [Real.volume_Ioc]
      ring
    · rw [MeasureTheory.Measure.restrict_apply h_meas_set]
      congr 1
      exact Set.inter_eq_left.mpr h_subset
  · -- Step 4: each term is measurable.
    intro i _
    refine Measurable.indicator ?_ measurableSet_Ioc
    fun_prop
/-- **Outer lintegral of `‖H.eval‖₊²` over `Ω × [0,T]`** equals the sum of
`ENNReal.ofReal(t_{i+1} - t_i) · ∫⁻ ‖ξ_i‖₊² ∂P`. This is the RHS reduction
of `simpleIntegral_isometry`. -/
lemma lintegral_eval_sq_outer
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (H : SimplePredictable Ω T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∑ i : Fin H.N,
        ENNReal.ofReal (H.partition i.succ - H.partition i.castSucc) *
        ∫⁻ ω, (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  rw [show (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      = (fun ω => ∑ i : Fin H.N,
          ENNReal.ofReal (H.partition i.succ - H.partition i.castSucc) *
          (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) from
    funext (fun ω => lintegral_eval_sq H ω)]
  rw [MeasureTheory.lintegral_finsetSum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MeasureTheory.lintegral_const_mul']
    exact ENNReal.ofReal_ne_top
  · intro i _
    refine Measurable.const_mul ?_ _
    exact (H.ξ_measurable i).enorm.pow_const 2
end Ito
end Brownian
end LevyStochCalc


