-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_MarkStepWeight_F001
-- name    : LevyStochCalc_Poisson_MarkStepWeight_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T12:25:56.671704+00:00
-- url     : https://prove2.me/theorems/067e1fc0-4aa2-4863-b917-c1360232a4bf
-- title:
--   Source declarations: LevyStochCalc.Poisson.MarkStepWeight
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.MarkStepWeight. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_MarkStepWeight_F000
import Definitions.Def_SourceProof_4c9a1a7d6613fd8ee5ec2b8c

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Sums, negations and weightings of mark-step integrands

Two mark-step integrands on a common time grid are added by concatenating their mark
families (`MarkStep.append`), and a mark-step integrand is negated coefficientwise
(`MarkStep.neg`); both operations act additively on the compensated integral and on the
integrand, so the `L²` isometry applies to differences. Multiplying the coefficients from a
given piece on by a bounded measurable weight `w`, and zeroing the earlier ones
(`MarkStep.weight`), yields the isometry for the weighted increment of the integral over a
grid interval.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace MarkStep

section Append

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G G' : MarkStep Ω E ν g)

end Append

section Weight

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν g) {w : Ω → ℝ}
  (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C) (hwm : Measurable w)

/-- The weighted increment of the integral between two grid points, as the integral of
the weighted integrand over the clamped horizon. -/
lemma full_weight_clamp {a b : ℕ} (hab : a ≤ b) (hb : b ≤ g.N₀) (ω : Ω) :
    ((G.clamp (g.p b) (g.p_nonneg hb)).weight w hw hwm a).full N ω
      = w ω * (G.integral N (g.p b) ω - G.integral N (g.p a) ω) := by
  rw [(fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_4c9a1a7d6613fd8ee5ec2b8c p2mMethodArg0 G) N b hb, (fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_4c9a1a7d6613fd8ee5ec2b8c p2mMethodArg0 G) N a (hab.trans hb)]
  have hN : (g.clamp (g.p b) (g.p_nonneg hb)).N₀ = b := g.clampIndex_p hb
  unfold full
  rw [hN]
  change ∑ i ∈ Finset.range b, ∑ k, (if a ≤ i then w ω * G.ξ i k ω else 0)
      * N.compensated (Set.Ioc (min (g.p i) (g.p b)) (min (g.p (i + 1)) (g.p b)) ×ˢ G.B k) ω
    = _
  set F : ℕ → ℝ := fun i => ∑ k, G.ξ i k ω
    * N.compensated (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ω with hF
  have hL : ∀ i ∈ Finset.range b, (∑ k, (if a ≤ i then w ω * G.ξ i k ω else 0)
      * N.compensated (Set.Ioc (min (g.p i) (g.p b)) (min (g.p (i + 1)) (g.p b)) ×ˢ G.B k) ω)
      = if a ≤ i then w ω * F i else 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [min_eq_left (g.p_mono hi.le hb), min_eq_left (g.p_mono hi hb), hF]
    split_ifs
    · simp only [Finset.mul_sum, mul_assoc]
    · simp
  rw [Finset.sum_congr rfl hL]
  have h2 : ∑ i ∈ Finset.range b, (if a ≤ i then 0 else w ω * F i)
      = ∑ i ∈ Finset.range a, w ω * F i := by
    refine (Finset.sum_subset (Finset.range_subset.2 fun i hi =>
      Finset.mem_range.2 (lt_of_lt_of_le hi hab)) ?_).symm.trans
      (Finset.sum_congr rfl fun i hi => ?_)
    · intro i hi hni
      rw [Finset.mem_range] at hni
      simp [not_lt.1 hni]
    · rw [Finset.mem_range] at hi
      simp [not_le.2 hi]
  have hsplit : ∑ i ∈ Finset.range b, (if a ≤ i then w ω * F i else 0)
      + ∑ i ∈ Finset.range a, w ω * F i = ∑ i ∈ Finset.range b, w ω * F i := by
    rw [← h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  linarith [hsplit]
/-- The integrand of the weighted clamped integrand. -/
lemma eval_weight_clamp {a b : ℕ} (hab : a ≤ b) (hb : b ≤ g.N₀) (s : ℝ) (e : E) (ω : Ω) :
    ((G.clamp (g.p b) (g.p_nonneg hb)).weight w hw hwm a).eval s e ω
      = if g.p a < s ∧ s ≤ g.p b then w ω * G.eval s e ω else 0 := by
  have hN : (g.clamp (g.p b) (g.p_nonneg hb)).N₀ = b := g.clampIndex_p hb
  have hL : ((G.clamp (g.p b) (g.p_nonneg hb)).weight w hw hwm a).eval s e ω
      = ∑ i ∈ Finset.range b, (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) s
        * ∑ k, (if a ≤ i then w ω * G.ξ i k ω else 0)
          * (G.B k).indicator (fun _ => (1 : ℝ)) e := by
    unfold eval
    rw [hN]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    change (Set.Ioc (min (g.p i) (g.p b)) (min (g.p (i + 1)) (g.p b))).indicator
        (fun _ => (1 : ℝ)) s * _ = _
    rw [min_eq_left (g.p_mono hi.le hb), min_eq_left (g.p_mono hi hb)]
    rfl
  rw [hL]
  split_ifs with hs
  · unfold eval
    rw [Finset.mul_sum]
    refine (Finset.sum_congr rfl fun i hi => ?_).trans (Finset.sum_subset
      (Finset.range_subset.2 fun i hi => Finset.mem_range.2 (lt_of_lt_of_le hi hb)) ?_)
    · rw [Finset.mem_range] at hi
      by_cases hai : a ≤ i
      · simp only [hai, if_true, Finset.mul_sum, mul_assoc]
        ring_nf
      · have hs0 : s ∉ Set.Ioc (g.p i) (g.p (i + 1)) := fun hs' =>
          absurd (hs'.2.trans (g.p_mono (Nat.succ_le_of_lt (not_le.1 hai)) (hab.trans hb)))
            (not_le.2 hs.1)
        rw [Set.indicator_of_notMem hs0]
        simp
    · intro i hi hni
      rw [Finset.mem_range] at hi hni
      rw [Set.indicator_of_notMem, zero_mul, mul_zero]
      intro hs'
      exact absurd (hs.2.trans (g.p_mono (not_lt.1 hni) hi.le)) (not_le.2 hs'.1)
  · refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_range] at hi
    by_cases hai : a ≤ i
    · rw [Set.indicator_of_notMem, zero_mul]
      intro hs'
      exact hs ⟨(g.p_mono hai (hi.le.trans hb)).trans_lt hs'.1, hs'.2.trans (g.p_mono hi hb)⟩
    · simp [hai]
include hℱ in
/-- The set-level `L²` isometry of the increment of the integral between two grid points,
against a bounded weight measurable at the earlier grid point. -/
theorem integral_weight_increment_sq (hG : G.Adapted ℱ) {w : Ω → ℝ}
    (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C) (hwm : Measurable w) {a b : ℕ} (hab : a ≤ b)
    (hb : b ≤ g.N₀)
    (hwa : @StronglyMeasurable Ω ℝ _ (ℱ (g.p a)) w) :
    ∫ ω, (w ω * (G.integral N (g.p b) ω - G.integral N (g.p a) ω)) ^ 2 ∂P
      = ∫ ω, (w ω) ^ 2 * (∫ e, ∫ s in Set.Ioc (g.p a) (g.p b),
          (G.eval s e ω) ^ 2 ∂volume ∂ν) ∂P := by
  have hb0 := g.p_nonneg hb
  have hwa' : @StronglyMeasurable Ω ℝ _ (ℱ ((g.clamp (g.p b) hb0).p a)) w := by
    change @StronglyMeasurable Ω ℝ _ (ℱ (min (g.p a) (g.p b))) w
    rwa [min_eq_left (g.p_mono hab hb)]
  have key := ((G.clamp (g.p b) hb0).weight w hw hwm a).integral_full_sq N hℱ
    ((hG.clamp (g.p b) hb0).weight hw hwm hwa') (g.clamp_horizon_le (g.p b) hb0)
  simp_rw [G.full_weight_clamp N hw hwm hab hb, G.eval_weight_clamp hw hwm hab hb] at key
  rw [key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  beta_reduce
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  beta_reduce
  rw [← integral_const_mul]
  have hsub : Set.Ioc (g.p a) (g.p b) ⊆ Set.Icc 0 (g.p b) := fun s hs =>
    ⟨(g.p_nonneg (hab.trans hb)).trans hs.1.le, hs.2⟩
  rw [← Set.inter_eq_self_of_subset_right hsub, ← setIntegral_indicator measurableSet_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun s _ => ?_
  by_cases hs : s ∈ Set.Ioc (g.p a) (g.p b)
  · rw [Set.indicator_of_mem hs, if_pos (Set.mem_Ioc.1 hs)]
    ring
  · rw [Set.indicator_of_notMem hs, if_neg (fun h => hs (Set.mem_Ioc.2 h))]
    ring
/-- The weighted integrand from index `0`: every coefficient is multiplied by `w`. -/
lemma full_weight_zero (ω : Ω) : (G.weight w hw hwm 0).full N ω = w ω * G.full N ω := by
  unfold full
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  change (if 0 ≤ i then w ω * G.ξ i k ω else 0) * _ = _
  rw [if_pos (Nat.zero_le i), mul_assoc]
  rfl
/-- The integrand of the integrand weighted from index `0`. -/
lemma eval_weight_zero (s : ℝ) (e : E) (ω : Ω) :
    (G.weight w hw hwm 0).eval s e ω = w ω * G.eval s e ω := by
  unfold eval
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) s
      * ∑ k : Fin G.K, (if 0 ≤ i then w ω * G.ξ i k ω else 0)
        * (G.B k).indicator (fun _ => (1 : ℝ)) e
    = w ω * ((Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) s
      * ∑ k : Fin G.K, G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e)
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [if_pos (Nat.zero_le i)]
  ring
end Weight

end MarkStep

end LevyStochCalc.Poisson.Compensated


