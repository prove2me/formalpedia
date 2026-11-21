-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoDensityPointwise_F000
-- name    : LevyStochCalc_Brownian_ItoDensityPointwise_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:59:09.286452+00:00
-- url     : https://prove2.me/theorems/c4e51128-e3b5-4a0b-9d11-6be04dc3182f
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoDensityPointwise
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoDensityPointwise. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityShiftedAverages_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityShiftedAverages_F002
import Definitions.Def_SourceProof_02c37e83f498df3491d7f8c9
import Definitions.Def_SourceProof_9261f2942c4ea65092c46566
import Definitions.Def_SourceProof_d2dcdd70ae2c689ce98c5bad
import Definitions.Def_SourceProof_fb9bb6c8d4545e37b51e590f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Almost-everywhere convergence of the dyadic averages

Lebesgue differentiation for a bounded jointly measurable integrand: the dyadic cell
averages, shifted and unshifted, converge to the integrand at almost every point of
`Ω × [0,T]`, and for the unshifted family the convergence also holds in `L²`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Step A1.0: Apply IsUnifLocDoublingMeasure.ae_tendsto_average to `g(ω, ·)`.**
For each ω, the average of g(ω, ·) over shrinking closed balls converges to g(ω, ·)
at almost every point.

This is the direct invocation of the Mathlib Lebesgue differentiation theorem,
made available by `instIsUnifLocDoublingMeasureRealVolume`. -/
private lemma g_omega_ae_tendsto_average
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (ω : Ω) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      ∀ {ι : Type} {l : Filter ι} (w : ι → ℝ) (δ : ι → ℝ),
        Filter.Tendsto δ l (nhdsWithin 0 (Set.Ioi 0)) →
        (∀ᶠ j in l, x ∈ Metric.closedBall (w j) (1 * δ j)) →
        Filter.Tendsto
          (fun j => ⨍ y in Metric.closedBall (w j) (δ j), g ω y ∂volume)
            l (nhds (g ω x)) := by
  have h_loc_int : MeasureTheory.LocallyIntegrable (g ω) volume :=
    _root_.Prove2MeSourceProof.h_02c37e83f498df3491d7f8c9 (g ω)
      (h_meas.comp (by fun_prop : Measurable (fun s : ℝ => (ω, s))))
      M (h_bound ω)
  exact IsUnifLocDoublingMeasure.ae_tendsto_average volume h_loc_int 1
/-- **Sub-sub-lemma A1: per-ω a.e. dyadic convergence.** For each fixed `ω`, the
dyadic averages of `g(ω, ·)` converge to `g(ω, ·)` a.e. on `[0, T]`.

The substantive remaining step is the dyadic-bridge: showing that for a.e. `s`,
the dyadic eval `eval n s ω` (= `(2^n/T) ∫_{(t_i, t_{i+1}]} g(ω, y) dy` for the
dyadic piece containing `s`) coincides with the Mathlib closed-ball average
`⨍ y in closedBall (midpoint) (half-length), g(ω, y) ∂volume`.

The closed-ball-to-dyadic-interval bridge:
- For dyadic level `n`, piece `i`: `t_i := i*T/2^n`, `t_{i+1} := (i+1)*T/2^n`.
- `midpoint := (t_i + t_{i+1})/2 = ((2i+1)*T/2^(n+1))`.
- `half-length := T/2^(n+1)`.
- `closedBall midpoint half-length = [t_i, t_{i+1}]`.
- `volume [t_i, t_{i+1}] = T/2^n = volume (t_i, t_{i+1}]` (boundary `{t_i}` has measure 0).
- Therefore `⨍ y in closedBall = (2^n/T) ∫_{[t_i, t_{i+1}]} g(ω, y) dy
                              = (2^n/T) ∫_{(t_i, t_{i+1}]} g(ω, y) dy = dyadicAvg`.
- And `eval s ω = dyadicAvg n i_n(s) ω` where `i_n(s)` is the dyadic index of `s`. -/
private lemma dyadic_pointwise_tendsto_per_omega
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (ω : Ω) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto
        (fun n => (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval s ω)
        Filter.atTop (nhds (g ω s)) := by
  -- Filter into volume.restrict-a.e. and exclude {0} which has volume 0.
  have h_lebesgue := g_omega_ae_tendsto_average g h_meas M h_bound ω
  -- Restrict the volume-a.e. property to volume.restrict (Icc 0 T)-a.e.
  have h_lebesgue_restrict : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ {ι : Type} {l : Filter ι} (w : ι → ℝ) (δ : ι → ℝ),
        Filter.Tendsto δ l (nhdsWithin 0 (Set.Ioi 0)) →
        (∀ᶠ j in l, x ∈ Metric.closedBall (w j) (1 * δ j)) →
        Filter.Tendsto
          (fun j => ⨍ y in Metric.closedBall (w j) (δ j), g ω y ∂volume) l (nhds (g ω x)) :=
    MeasureTheory.ae_restrict_of_ae h_lebesgue
  -- Exclude {0} via measure-zero set on the full measure.
  have h_pos_ae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have : {x : ℝ | ¬(x ≠ 0)} = {(0 : ℝ)} := by ext; simp
    rw [this, Real.volume_singleton]
  -- Restrict in domain to s ∈ Icc 0 T explicitly.
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc] at h_lebesgue_restrict
  filter_upwards [h_lebesgue_restrict, h_pos_ae] with x h_lebesgue_at_x hx_ne_zero hx_mem
  -- For x ∈ Icc 0 T with x ≠ 0, x > 0 (since x ≥ 0 from Icc).
  have hx_strict_pos : 0 < x := lt_of_le_of_ne hx_mem.1 (Ne.symm hx_ne_zero)
  have hx : 0 < x ∧ x ≤ T := ⟨hx_strict_pos, hx_mem.2⟩
  -- Apply Mathlib lemma with dyadic sequence.
  set w : ℕ → ℝ := fun n =>
    (dyadicPartition_brownian T n (dyadicIndex n T hT x hx).castSucc +
     dyadicPartition_brownian T n (dyadicIndex n T hT x hx).succ) / 2
  set δ : ℕ → ℝ := fun n =>
    (dyadicPartition_brownian T n (dyadicIndex n T hT x hx).succ -
     dyadicPartition_brownian T n (dyadicIndex n T hT x hx).castSucc) / 2
  have h_delta_eq : ∀ n, δ n = T / (2 * (2 ^ n : ℕ)) := by
    intro n
    change (dyadicPartition_brownian T n (dyadicIndex n T hT x hx).succ -
          dyadicPartition_brownian T n (dyadicIndex n T hT x hx).castSucc) / 2 = _
    rw [dyadicPartition_brownian_diff n (dyadicIndex n T hT x hx)]
    ring
  -- δ n → 0 in nhdsWithin 0 (Ioi 0).
  have h_delta_pos : ∀ n, 0 < δ n := by
    intro n
    rw [h_delta_eq]
    have : (0 : ℝ) < 2 * (2 ^ n : ℕ) := by positivity
    exact div_pos hT this
  have h_delta_to_zero : Filter.Tendsto δ Filter.atTop (nhds 0) := by
    have h_eq : δ = fun n => T / (2 * (2 ^ n : ℕ)) := funext h_delta_eq
    rw [h_eq]
    -- 2 * (2^n : ℕ) → ∞ as n → ∞.
    have h_2pow : Filter.Tendsto (fun n : ℕ => 2 * ((2 ^ n : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      have h_pow_atTop : Filter.Tendsto (fun n : ℕ => ((2 ^ n : ℕ) : ℝ))
          Filter.atTop Filter.atTop := by
        have : Filter.Tendsto (fun n : ℕ => (2 ^ n : ℕ)) Filter.atTop Filter.atTop :=
          tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2)
        exact tendsto_natCast_atTop_iff.mpr this
      exact h_pow_atTop.atTop_mul_const' (by norm_num : (0 : ℝ) < 2) |>.congr
        (fun n => by ring)
    -- T / (2 * 2^n) → T / ∞ = 0.
    exact Filter.Tendsto.div_atTop tendsto_const_nhds h_2pow
  have h_delta_tendsto : Filter.Tendsto δ Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨h_delta_to_zero, ?_⟩
    exact Filter.Eventually.of_forall h_delta_pos
  -- x ∈ closedBall (w n) (1 * δ n) for all n.
  have h_x_in_ball : ∀ n, x ∈ Metric.closedBall (w n) (1 * δ n) := by
    intro n
    rw [one_mul]
    change |x - w n| ≤ δ n
    have h_mem := _root_.Prove2MeSourceProof.h_d2dcdd70ae2c689ce98c5bad n T hT x hx
    set t_i := dyadicPartition_brownian T n (dyadicIndex n T hT x hx).castSucc with ht_i
    set t_succ := dyadicPartition_brownian T n (dyadicIndex n T hT x hx).succ with ht_succ
    have h_x1 : t_i < x := by
      have h := h_mem.1
      change dyadicPartition_brownian T n (dyadicIndex n T hT x hx).castSucc < x
      unfold dyadicPartition_brownian
      push_cast at h ⊢
      simpa [Fin.val_castSucc] using h
    have h_x2 : x ≤ t_succ := by
      have h := h_mem.2
      change x ≤ dyadicPartition_brownian T n (dyadicIndex n T hT x hx).succ
      unfold dyadicPartition_brownian
      push_cast at h ⊢
      simpa [Fin.val_succ] using h
    change |x - (t_i + t_succ) / 2| ≤ (t_succ - t_i) / 2
    rw [abs_le]
    refine ⟨by linarith, by linarith⟩
  -- Apply the Mathlib lemma.
  have h_avg_to_g := h_lebesgue_at_x hx_mem (l := Filter.atTop) w δ h_delta_tendsto
    (Filter.Eventually.of_forall h_x_in_ball)
  -- Bridge: ⨍ over closedBall = dyadicAvg = eval.
  have h_bridge : ∀ n,
      (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval x ω =
      ⨍ y in Metric.closedBall (w n) (δ n), g ω y ∂volume := by
    intro n
    rw [_root_.Prove2MeSourceProof.h_9261f2942c4ea65092c46566 hT g h_meas M h_bound n x hx ω]
    exact _root_.Prove2MeSourceProof.h_fb9bb6c8d4545e37b51e590f hT g n (dyadicIndex n T hT x hx) ω
  -- Combine.
  have h_eq_seq : (fun n => (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval x ω)
      = fun n => ⨍ y in Metric.closedBall (w n) (δ n), g ω y ∂volume :=
    funext h_bridge
  rw [h_eq_seq]
  exact h_avg_to_g
/-- **Joint measurability of the convergence set.** The set
`{(ω, s) | Tendsto (eval n s ω) atTop (𝓝 (g ω s))}` is measurable.

Proof: `Tendsto _ atTop (𝓝 (g ω s))` is equivalent to
`Tendsto (eval n - g ω s) atTop (𝓝 0)`,
i.e., convergence to the fixed limit 0 of a jointly measurable sequence. By
`measurableSet_tendsto`, this set is measurable. -/
private lemma convergence_set_measurable
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    MeasurableSet
      {p : Ω × ℝ | Filter.Tendsto
        (fun n => (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2))} := by
  -- Rewrite convergence to (g ω s) as convergence of difference to 0.
  have h_eq : {p : Ω × ℝ | Filter.Tendsto
        (fun n => (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2))}
      = {p : Ω × ℝ | Filter.Tendsto
        (fun n => (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1
          - g p.1 p.2)
        Filter.atTop (nhds 0)} := by
    ext p
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hp
      have h_const : Filter.Tendsto (fun _ : ℕ => g p.1 p.2)
        Filter.atTop (nhds (g p.1 p.2)) := tendsto_const_nhds
      simpa using hp.sub h_const
    · intro hp
      have h_const : Filter.Tendsto (fun _ : ℕ => g p.1 p.2)
        Filter.atTop (nhds (g p.1 p.2)) := tendsto_const_nhds
      simpa using hp.add h_const
  rw [h_eq]
  -- The sequence is jointly measurable in (ω, s).
  have h_seq_meas : ∀ n, Measurable (fun (p : Ω × ℝ) =>
      (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1
        - g p.1 p.2) := by
    intro n
    have h_eval_meas : Measurable (fun p : Ω × ℝ =>
        (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1) := by
      unfold SimplePredictable.eval
      refine Finset.measurable_sum _ ?_
      intro i _
      refine Measurable.ite ?_ ?_ measurable_const
      · refine MeasurableSet.inter ?_ ?_
        · exact measurable_snd (measurableSet_Ioi
            (a := (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).partition i.castSucc))
        · exact measurable_snd (measurableSet_Iic
            (a := (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).partition i.succ))
      · exact (dyadicAvg_brownian_measurable T g h_meas n i).comp measurable_fst
    exact h_eval_meas.sub
      (h_meas.comp (by fun_prop : Measurable (fun (p : Ω × ℝ) => (p.1, p.2))))
  exact measurableSet_tendsto (nhds (0 : ℝ)) h_seq_meas
private lemma dyadicSimplePredictable_brownian_ae_tendsto
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      Filter.Tendsto
        (fun n => (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2)) := by
  -- Use `MeasureTheory.Measure.ae_prod_iff_ae_ae` to lift "for each ω, ∀ᵐ s" to
  -- "∀ᵐ (ω, s) ∂(P × volume.restrict)".
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae
    (convergence_set_measurable hT g h_meas M h_bound)]
  refine Filter.Eventually.of_forall (fun ω => ?_)
  exact dyadic_pointwise_tendsto_per_omega hT g h_meas M h_bound ω
end LevyStochCalc.Brownian.Ito


