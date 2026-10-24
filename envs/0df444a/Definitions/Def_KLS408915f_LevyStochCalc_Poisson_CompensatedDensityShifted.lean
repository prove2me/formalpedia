-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityShifted
-- name    : KLS408915f_LevyStochCalc_Poisson_CompensatedDensityShifted
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T09:04:19.637822+00:00
-- url     : https://prove2.me/theorems/bcb81379-4421-475d-ac66-9c2d768dd397
-- title:
--   Adapted shifted dyadic evaluations
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc), commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `dyadicEvalShifted` is the piecewise-constant evaluation on the dyadic partition whose coefficient on the $i$-th cell is the preceding-cell average, with value zero on the first cell. For bounded jointly measurable $\phi$, the bundle proves boundedness and joint measurability, a.e. convergence in time for each fixed $(\omega,e)$, and convergence of the time $L^2$ error for each fixed $(\omega,e)$. With finite mark support, `dyadicEvalShifted_L2_tendsto` upgrades this to convergence of the full iterated $L^2$ energy over $P$, time volume on $[0,T]$, and $\nu$.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Poisson/CompensatedDensityShifted.lean#L34-L398 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Poisson.CompensatedDensityShifted`, definition bundle `KLS408915f_LevyStochCalc_Poisson_CompensatedDensityShifted`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityDyadic
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityTruncation
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleAdapted
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleQuadratic
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedSimple
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_Filtered
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_PoissonSuperposition
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Progressive
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Order.MonotoneContinuity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Poisson/CompensatedDensityShifted.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Poisson
namespace Compensated
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
/-- The left-shifted dyadic eval (adapted coefficients). -/
noncomputable def dyadicEvalShifted
    (T : ℝ) (φ : Ω → ℝ → E → ℝ) (n : ℕ) (s : ℝ) (ω : Ω) (e : E) : ℝ :=
  ∑ i : Fin (2 ^ n),
    if dyadicPartition T n i.castSucc < s ∧ s ≤ dyadicPartition T n i.succ
    then dyadicAvg_shifted T φ n i ω e else 0
omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- For `s ∈ (0, T]`, the shifted eval collapses to the shifted average at the index of `s`. -/
lemma dyadicEvalShifted_eq_at_index
    {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ) (n : ℕ) (s : ℝ) (hs : 0 < s ∧ s ≤ T)
    (ω : Ω) (e : E) :
    dyadicEvalShifted T φ n s ω e = dyadicAvg_shifted T φ n (dyadicIndex n T hT s hs) ω e := by
  set i := dyadicIndex n T hT s hs with hi
  have hi_mem := dyadicIndex_mem n T hT s hs
  have h_pcast : dyadicPartition T n i.castSucc = ((i : ℕ) : ℝ) * T / (2 ^ n : ℕ) := by
    unfold dyadicPartition; rw [Fin.val_castSucc]
  have h_psucc : dyadicPartition T n i.succ = (((i : ℕ) + 1) : ℝ) * T / (2 ^ n : ℕ) := by
    unfold dyadicPartition; rw [Fin.val_succ]; push_cast; ring
  have h_i_fires : dyadicPartition T n i.castSucc < s ∧ s ≤ dyadicPartition T n i.succ := by
    rw [h_pcast, h_psucc]; exact hi_mem
  unfold dyadicEvalShifted
  rw [Finset.sum_eq_single i]
  · rw [if_pos h_i_fires]
  · intro j _ hji
    refine if_neg (fun ⟨hj1, hj2⟩ => ?_)
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have := (dyadicPartition_strictMono hT n).monotone (Fin.succ_le_castSucc_iff.mpr hlt)
      linarith [h_i_fires.2]
    · exact hji heq.symm
    · have := (dyadicPartition_strictMono hT n).monotone (Fin.succ_le_castSucc_iff.mpr hgt)
      linarith [h_i_fires.1]
  · intro h_not; exact absurd (Finset.mem_univ i) h_not
omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- The shifted eval is bounded by `max M 0` (at most one indicator fires; each shifted
average is bounded by `max M 0`). -/
lemma dyadicEvalShifted_bounded {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ)
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M) (n : ℕ) (s : ℝ) (ω : Ω) (e : E) :
    |dyadicEvalShifted T φ n s ω e| ≤ max M 0 := by
  unfold dyadicEvalShifted
  by_cases h : ∃ i : Fin (2 ^ n),
      dyadicPartition T n i.castSucc < s ∧ s ≤ dyadicPartition T n i.succ
  · obtain ⟨i₀, hi₀⟩ := h
    have huniq : ∀ j : Fin (2 ^ n), j ≠ i₀ →
        ¬(dyadicPartition T n j.castSucc < s ∧ s ≤ dyadicPartition T n j.succ) := by
      intro j hj ⟨hj1, hj2⟩
      rcases lt_trichotomy i₀ j with hlt | heq | hgt
      · have := (dyadicPartition_strictMono hT n).monotone (Fin.succ_le_castSucc_iff.mpr hlt)
        linarith [hi₀.2]
      · exact hj heq.symm
      · have := (dyadicPartition_strictMono hT n).monotone (Fin.succ_le_castSucc_iff.mpr hgt)
        linarith [hi₀.1]
    rw [Finset.sum_eq_single i₀ (fun j _ hj => if_neg (huniq j hj))
        (fun h => absurd (Finset.mem_univ _) h), if_pos hi₀]
    exact dyadicAvg_shifted_bounded hT φ hM n i₀ ω e
  · rw [not_exists] at h
    rw [Finset.sum_eq_zero (fun i _ => if_neg (h i)), abs_zero]; exact le_max_right _ _
/-- Joint `(ω, s, e)`-measurability of the shifted eval. -/
lemma dyadicEvalShifted_measurable_triple
    {T : ℝ} (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)) (n : ℕ) :
    Measurable (fun p : Ω × ℝ × E => dyadicEvalShifted T φ n p.2.1 p.1 p.2.2) := by
  unfold dyadicEvalShifted
  refine Finset.measurable_sum _ (fun i _ => ?_)
  refine Measurable.ite ((measurable_fst.comp measurable_snd) measurableSet_Ioc) ?_
    measurable_const
  unfold dyadicAvg_shifted
  by_cases h : i.val = 0
  · simp only [h, ↓reduceDIte]; exact measurable_const
  · simp only [h, ↓reduceDIte]
    exact (dyadicAvg_measurable T φ h_meas n _).comp
      (by fun_prop : Measurable fun p : Ω × ℝ × E => ((p.1, p.2.2) : Ω × E))
/-- `dyadicPartition` depends only on the index's value. -/
lemma dyadicPartition_val_congr {T : ℝ} {n : ℕ} {k k' : Fin (2 ^ n + 1)}
    (h : (k : ℕ) = (k' : ℕ)) : dyadicPartition T n k = dyadicPartition T n k' := by
  unfold dyadicPartition
  rw [show (k : ℝ) = (k' : ℝ) from by exact_mod_cast h]
/-- **Per-`(ω,e)` a.e. convergence of the shifted eval.** For fixed `(ω, e)`, the
left-shifted dyadic eval converges to `φ(ω, s, e)` for a.e. `s ∈ [0,T]`: Lebesgue
differentiation (`K = 3`) on the *previous* dyadic interval; the centre/half are read
off the previous-interval index `⟨iₙ−1, _⟩`, so the closed-ball bridge is definitional.
The first interval (`iₙ = 0`, shift `= 0`) is escaped for all large `n`. -/
lemma dyadicEvalShifted_ae_tendsto_per_param
    {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M) (ω : Ω) (e : E) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun n => dyadicEvalShifted T φ n s ω e) Filter.atTop (nhds (φ ω s e)) := by
  have h_meas_slice : Measurable (fun s : ℝ => φ ω s e) :=
    h_meas.comp (by fun_prop : Measurable fun s : ℝ => ((ω, s, e) : Ω × ℝ × E))
  have h_loc : MeasureTheory.LocallyIntegrable (fun s : ℝ => φ ω s e) volume :=
    bounded_locallyIntegrable _ h_meas_slice M (fun s => hM ω s e)
  have h_leb := IsUnifLocDoublingMeasure.ae_tendsto_average (volume : Measure ℝ) h_loc 3
  have h_leb_r : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ {ι : Type} {l : Filter ι} (w : ι → ℝ) (δ : ι → ℝ),
        Filter.Tendsto δ l (nhdsWithin 0 (Set.Ioi 0)) →
        (∀ᶠ j in l, x ∈ Metric.closedBall (w j) (3 * δ j)) →
        Filter.Tendsto (fun j => ⨍ y in Metric.closedBall (w j) (δ j), φ ω y e ∂volume)
          l (nhds (φ ω x e)) :=
    MeasureTheory.ae_restrict_of_ae h_leb
  have h_pos_ae : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) T)), x ≠ 0 := by
    refine MeasureTheory.ae_restrict_of_ae ?_
    rw [MeasureTheory.ae_iff]
    have : {x : ℝ | ¬ x ≠ 0} = {0} := by ext x; simp
    rw [this, Real.volume_singleton]
  filter_upwards [h_leb_r, h_pos_ae, MeasureTheory.ae_restrict_mem measurableSet_Icc]
    with x h_leb_x hx_ne hx_mem
  have hx : 0 < x ∧ x ≤ T := ⟨lt_of_le_of_ne hx_mem.1 (Ne.symm hx_ne), hx_mem.2⟩
  have hjlt : ∀ n, (dyadicIndex n T hT x hx).val - 1 < 2 ^ n := fun n => by
    have := (dyadicIndex n T hT x hx).isLt; omega
  set jp : (n : ℕ) → Fin (2 ^ n) :=
    fun n => ⟨(dyadicIndex n T hT x hx).val - 1, hjlt n⟩ with hjp
  set w : ℕ → ℝ := fun n =>
    (dyadicPartition T n (jp n).castSucc + dyadicPartition T n (jp n).succ) / 2 with hw
  set δ : ℕ → ℝ := fun n =>
    (dyadicPartition T n (jp n).succ - dyadicPartition T n (jp n).castSucc) / 2 with hδ
  have hδ_eq : ∀ n, δ n = T / (2 * (2 ^ n : ℕ)) := by
    intro n; rw [hδ]
    change (dyadicPartition T n (jp n).succ - dyadicPartition T n (jp n).castSucc) / 2 = _
    rw [dyadicPartition_diff]; ring
  have hδ_pos : ∀ n, 0 < δ n := fun n => by rw [hδ_eq]; positivity
  have hδ0 : Filter.Tendsto δ Filter.atTop (nhds 0) := by
    have h2pow : Filter.Tendsto (fun n : ℕ => 2 * ((2 ^ n : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      have : Filter.Tendsto (fun n : ℕ => ((2 ^ n : ℕ) : ℝ)) Filter.atTop Filter.atTop :=
        tendsto_natCast_atTop_iff.mpr (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2))
      exact this.atTop_mul_const' (by norm_num : (0 : ℝ) < 2) |>.congr (fun n => by ring)
    exact (Filter.Tendsto.div_atTop tendsto_const_nhds h2pow).congr (fun n => (hδ_eq n).symm)
  have hδ_nhds : Filter.Tendsto δ Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hδ0, Filter.Eventually.of_forall hδ_pos⟩
  -- eventually the index is ≥ 1.
  have hev1 : ∀ᶠ n in Filter.atTop, 1 ≤ (dyadicIndex n T hT x hx).val := by
    have hpow : Filter.Tendsto (fun n : ℕ => ((2 ^ n : ℕ) : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_iff.mpr (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2))
    filter_upwards [hpow.eventually_gt_atTop (T / x)] with n hn
    have h1 : (1 : ℝ) < x * (2 ^ n : ℕ) / T := by
      rw [lt_div_iff₀ hT, one_mul]
      have h2 : T < (2 ^ n : ℕ) * x := (div_lt_iff₀ hx.1).mp hn
      linarith [h2]
    have hc : 1 < ⌈x * (2 ^ n : ℕ) / T⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast h1)
    simp only [dyadicIndex]; omega
  -- x is within 3δ of the previous interval's centre, in symbolic `a, b` form.
  have hxball : ∀ᶠ n in Filter.atTop, x ∈ Metric.closedBall (w n) (3 * δ n) := by
    filter_upwards [hev1] with n hn1
    set a := dyadicPartition T n (jp n).castSucc with ha
    set b := dyadicPartition T n (jp n).succ with hb
    have hval : ((dyadicIndex n T hT x hx).castSucc : ℕ) = ((jp n).succ : ℕ) := by
      simp only [hjp, Fin.val_castSucc, Fin.val_succ]; omega
    have hib : dyadicPartition T n (dyadicIndex n T hT x hx).castSucc = b := by
      rw [hb]; exact dyadicPartition_val_congr hval
    have hba : a ≤ b := (dyadicPartition_strictMono hT n).monotone Fin.castSucc_lt_succ.le
    have hdiff_j : b - a = T / (2 ^ n : ℕ) := dyadicPartition_diff n (jp n)
    have hdiff_i : dyadicPartition T n (dyadicIndex n T hT x hx).succ
        - dyadicPartition T n (dyadicIndex n T hT x hx).castSucc = T / (2 ^ n : ℕ) :=
      dyadicPartition_diff n (dyadicIndex n T hT x hx)
    have hlo : b < x := by
      rw [← hib]; unfold dyadicPartition; rw [Fin.val_castSucc]
      exact (dyadicIndex_mem n T hT x hx).1
    have hx_hi_part : x ≤ dyadicPartition T n (dyadicIndex n T hT x hx).succ := by
      have h2 := (dyadicIndex_mem n T hT x hx).2
      unfold dyadicPartition; rw [Fin.val_succ]; push_cast at h2 ⊢; linarith [h2]
    rw [hib] at hdiff_i
    rw [Metric.mem_closedBall, Real.dist_eq]
    change |x - (a + b) / 2| ≤ 3 * ((b - a) / 2)
    rw [abs_le]
    constructor <;> linarith [hlo, hx_hi_part, hdiff_i, hdiff_j, hba]
  -- bridge: shifted eval = closed-ball average centred at `wₙ` (definitional).
  have hbridge : ∀ᶠ n in Filter.atTop,
      dyadicEvalShifted T φ n x ω e = ⨍ y in Metric.closedBall (w n) (δ n), φ ω y e ∂volume := by
    filter_upwards [hev1] with n hn1
    have hival : (dyadicIndex n T hT x hx).val ≠ 0 := by omega
    rw [dyadicEvalShifted_eq_at_index hT φ n x hx ω e, dyadicAvg_shifted, dif_neg hival]
    change dyadicAvg T φ n (jp n) ω e = _
    rw [dyadicAvg_eq_average_closedBall hT φ n (jp n) ω e]
  exact Filter.Tendsto.congr' (hbridge.mono (fun n h => h.symm)) (h_leb_x w δ hδ_nhds hxball)
omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- If `φ(ω, ·, e)` vanishes identically in time, so does its shifted dyadic eval. -/
lemma dyadicEvalShifted_eq_zero {T : ℝ} (φ : Ω → ℝ → E → ℝ) (n : ℕ) (s : ℝ) (ω : Ω) (e : E)
    (h0 : ∀ u, φ ω u e = 0) : dyadicEvalShifted T φ n s ω e = 0 := by
  unfold dyadicEvalShifted
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have havg : dyadicAvg_shifted T φ n i ω e = 0 := by
    unfold dyadicAvg_shifted
    split_ifs with h
    · rfl
    · unfold dyadicAvg; simp [h0]
  split_ifs with h
  · exact havg
  · rfl
/-- Joint `(s, e)`-measurability of the shifted eval (with `ω` fixed). -/
lemma dyadicEvalShifted_measurable_prod
    {T : ℝ} (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)) (n : ℕ) (ω : Ω) :
    Measurable (fun q : ℝ × E => dyadicEvalShifted T φ n q.1 ω q.2) := by
  unfold dyadicEvalShifted
  refine Finset.measurable_sum _ (fun i _ => ?_)
  refine Measurable.ite (measurable_fst measurableSet_Ioc) ?_ measurable_const
  unfold dyadicAvg_shifted
  by_cases h : i.val = 0
  · simp only [h, ↓reduceDIte]; exact measurable_const
  · simp only [h, ↓reduceDIte]
    exact (dyadicAvg_measurable T φ h_meas n _).comp
      (by fun_prop : Measurable fun q : ℝ × E => ((ω, q.2) : Ω × E))
/-- **Per-`(ω,e)` time-`L²` convergence of the shifted eval.** -/
lemma dyadicEvalShifted_inner_L2_tendsto
    {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M) (ω : Ω) (e : E) :
    Filter.Tendsto
      (fun n => ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      Filter.atTop (nhds 0) := by
  have hM'_nn : 0 ≤ max M 0 := le_max_right _ _
  have hsq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from (ofReal_norm x).symm,
      ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [show (0 : ℝ≥0∞) = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) ∂(volume.restrict (Set.Icc (0 : ℝ) T)) from by simp]
  refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
    (bound := fun _ => ENNReal.ofReal ((2 * max M 0) ^ 2)) ?_ ?_ ?_ ?_
  · intro n
    exact ((ENNReal.continuous_coe.measurable.comp
      ((h_meas.comp (by fun_prop : Measurable fun s : ℝ => ((ω, s, e) : Ω × ℝ × E))).sub
        ((dyadicEvalShifted_measurable_prod φ h_meas n ω).comp
          (by fun_prop : Measurable fun s : ℝ => ((s, e) : ℝ × E)))).nnnorm).pow_const
            2).aemeasurable
  · intro n
    refine Filter.Eventually.of_forall (fun s => ?_)
    simp only []
    rw [hsq]
    refine ENNReal.ofReal_le_ofReal ?_
    have hb : ‖φ ω s e - dyadicEvalShifted T φ n s ω e‖ ≤ 2 * max M 0 := by
      rw [Real.norm_eq_abs]
      calc |φ ω s e - dyadicEvalShifted T φ n s ω e|
          ≤ |φ ω s e| + |dyadicEvalShifted T φ n s ω e| := abs_sub _ _
        _ ≤ max M 0 + max M 0 :=
            add_le_add ((hM ω s e).trans (le_max_left _ _))
              (dyadicEvalShifted_bounded hT φ hM n s ω e)
        _ = 2 * max M 0 := by ring
    nlinarith [norm_nonneg (φ ω s e - dyadicEvalShifted T φ n s ω e), hb, hM'_nn]
  · rw [MeasureTheory.lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (MeasureTheory.measure_ne_top _ _)
  · filter_upwards [dyadicEvalShifted_ae_tendsto_per_param hT φ h_meas hM ω e] with s hs
    have hdiff : Filter.Tendsto (fun n => φ ω s e - dyadicEvalShifted T φ n s ω e)
        Filter.atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := φ ω s e)).sub hs
    have hg : Continuous (fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 2) :=
      (ENNReal.continuous_pow 2).comp (ENNReal.continuous_coe.comp continuous_nnnorm)
    simpa [Function.comp_def] using (hg.tendsto 0).comp hdiff
set_option maxHeartbeats 1000000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **`L²` convergence of the adapted (shifted) eval (finite-mark-support).** -/
lemma dyadicEvalShifted_L2_tendsto
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν] {T : ℝ} (hT : 0 < T)
    (φ : Ω → ℝ → E → ℝ) (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M)
    {S : Set E} (hS_meas : MeasurableSet S) (hS_fin : ν S ≠ ⊤)
    (hSupp : ∀ ω e, e ∉ S → ∀ u, φ ω u e = 0) :
    Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      Filter.atTop (nhds 0) := by
  set M' : ℝ := max M 0 with hM'def
  have hM'_nn : 0 ≤ M' := le_max_right _ _
  have hφM' : ∀ ω s e, |φ ω s e| ≤ M' := fun ω s e => (hM ω s e).trans (le_max_left _ _)
  set cT : ℝ≥0∞ := ENNReal.ofReal ((2 * M') ^ 2 * T) with hcT
  have hFmeas : ∀ n : ℕ, Measurable (fun p : Ω × ℝ × E =>
      (‖φ p.1 p.2.1 p.2.2 - dyadicEvalShifted T φ n p.2.1 p.1 p.2.2‖₊ : ℝ≥0∞) ^ 2) := fun n =>
    (ENNReal.continuous_coe.measurable.comp
      (h_meas.sub (dyadicEvalShifted_measurable_triple φ h_meas n)).nnnorm).pow_const 2
  have hF_se : ∀ n ω, Measurable (fun q : ℝ × E =>
      (‖φ ω q.1 q.2 - dyadicEvalShifted T φ n q.1 ω q.2‖₊ : ℝ≥0∞) ^ 2) := fun n ω =>
    (ENNReal.continuous_coe.measurable.comp
      ((h_meas.comp (by fun_prop : Measurable fun q : ℝ × E => ((ω, q.1, q.2) : Ω × ℝ × E))).sub
        ((dyadicEvalShifted_measurable_prod φ h_meas n ω))).nnnorm).pow_const 2
  have hswap : ∀ n ω, (∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume)
      = ∫⁻ e, (∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂volume) ∂ν := by
    intro n ω
    exact MeasureTheory.lintegral_lintegral_swap (hF_se n ω).aemeasurable
  have h_inner_le : ∀ n ω e,
      (∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂volume)
        ≤ S.indicator (fun _ => cT) e := by
    intro n ω e
    by_cases he : e ∈ S
    · rw [Set.indicator_of_mem he]
      calc (∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂volume)
          ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, ENNReal.ofReal ((2 * M') ^ 2) ∂volume := by
            refine MeasureTheory.lintegral_mono (fun s => ?_)
            rw [show (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2
                  = ENNReal.ofReal (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖ ^ 2) from by
                rw [show (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞)
                      = ENNReal.ofReal ‖φ ω s e - dyadicEvalShifted T φ n s ω e‖ from
                    (ofReal_norm _).symm, ← ENNReal.ofReal_pow (norm_nonneg _)]]
            refine ENNReal.ofReal_le_ofReal ?_
            have hb : ‖φ ω s e - dyadicEvalShifted T φ n s ω e‖ ≤ 2 * M' := by
              rw [Real.norm_eq_abs]
              calc |φ ω s e - dyadicEvalShifted T φ n s ω e|
                  ≤ |φ ω s e| + |dyadicEvalShifted T φ n s ω e| := abs_sub _ _
                _ ≤ M' + M' := add_le_add (hφM' ω s e) (dyadicEvalShifted_bounded hT φ hM n s ω e)
                _ = 2 * M' := by ring
            nlinarith [norm_nonneg (φ ω s e - dyadicEvalShifted T φ n s ω e), hb, hM'_nn]
        _ = cT := by
            rw [MeasureTheory.setLIntegral_const, Real.volume_Icc, hcT,
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1; rw [sub_zero]
    · have hzero : ∀ s, φ ω s e - dyadicEvalShifted T φ n s ω e = 0 := by
        intro s
        rw [hSupp ω e he s, dyadicEvalShifted_eq_zero φ n s ω e (hSupp ω e he), sub_zero]
      rw [Set.indicator_of_notMem he]
      simp only [hzero, nnnorm_zero, ENNReal.coe_zero]
      simp
  simp_rw [hswap]
  rw [show (0 : ℝ≥0∞) = ∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P from by simp]
  refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
    (bound := fun _ => cT * ν S) ?_ ?_ (by
      rw [MeasureTheory.lintegral_const]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS_fin)
        (MeasureTheory.measure_ne_top _ _)) ?_
  · intro n
    refine Measurable.aemeasurable ?_
    have hmeas2 : Measurable (fun q : Ω × E => ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖φ q.1 s q.2 - dyadicEvalShifted T φ n s q.1 q.2‖₊ : ℝ≥0∞) ^ 2 ∂volume) := by
      have hr : Measurable (fun p : (Ω × E) × ℝ =>
          (‖φ p.1.1 p.2 p.1.2 - dyadicEvalShifted T φ n p.2 p.1.1 p.1.2‖₊ : ℝ≥0∞) ^ 2) :=
        (hFmeas n).comp (by fun_prop :
          Measurable fun p : (Ω × E) × ℝ => ((p.1.1, p.2, p.1.2) : Ω × ℝ × E))
      exact hr.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) T))
    exact hmeas2.lintegral_prod_right' (ν := ν)
  · intro n
    refine Filter.Eventually.of_forall (fun ω => ?_)
    calc (∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν)
        ≤ ∫⁻ e, S.indicator (fun _ => cT) e ∂ν :=
          MeasureTheory.lintegral_mono (fun e => h_inner_le n ω e)
      _ = cT * ν S := by
          rw [MeasureTheory.lintegral_indicator hS_meas, MeasureTheory.setLIntegral_const]
  · refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [show (0 : ℝ≥0∞) = ∫⁻ _ : E, (0 : ℝ≥0∞) ∂ν from by simp]
    refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
      (bound := fun e => S.indicator (fun _ => cT) e) ?_ ?_ (by
        rw [MeasureTheory.lintegral_indicator hS_meas, MeasureTheory.setLIntegral_const]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS_fin) ?_
    · intro n
      have hes : Measurable (fun q : E × ℝ =>
          (‖φ ω q.2 q.1 - dyadicEvalShifted T φ n q.2 ω q.1‖₊ : ℝ≥0∞) ^ 2) := by
        refine (ENNReal.continuous_coe.measurable.comp (Measurable.sub ?_ ?_).nnnorm).pow_const 2
        · exact h_meas.comp (by fun_prop : Measurable fun q : E × ℝ => ((ω, q.2, q.1) : Ω × ℝ × E))
        · exact (dyadicEvalShifted_measurable_prod φ h_meas n ω).comp measurable_swap
      exact (hes.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) T))).aemeasurable
    · intro n
      exact Filter.Eventually.of_forall (fun e => h_inner_le n ω e)
    · exact Filter.Eventually.of_forall
        (fun e => dyadicEvalShifted_inner_L2_tendsto hT φ h_meas hM ω e)
end Compensated
end Poisson
end LevyStochCalc


