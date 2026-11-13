-- Prove2me | Definitions.Def_ProbabilityTheory_common_support_tv_distance_core
-- name    : ProbabilityTheory_common_support_tv_distance_core
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T08:04:00.394382+00:00
-- url     : https://prove2.me/theorems/1fb05974-57f2-4b7b-b96b-1fc46288d963
-- title:
--   Chapter ?, generated supplement: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter ?, source module `generated supplement`: `d_TV`, `pmfReal`, `pmfDiff`, `pmfPos`, `pmfNeg`, and 48 others. The mathematical interpretation of this bundle needs review.
-- source:
--   Supplemental source module in importer v37; upstream repository https://github.com/wkshum/ProbabilityTheory/tree/e6387d4fd8005d627d2aec40d10f039ddb4e4b40

import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Definitions.Def_ProbabilityTheory_chapter_08_def_8_5_F000

open MeasureTheory Set

noncomputable section

namespace TVCore

def d_TV (f g : ℕ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑' k, |f k - g k|

variable {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

def pmfReal (p : PMF α) (x : α) : ℝ :=
  (p x).toReal

def pmfDiff (p q : PMF α) (x : α) : ℝ :=
  pmfReal p x - pmfReal q x

def pmfPos (p q : PMF α) (x : α) : ℝ :=
  max (pmfDiff p q x) 0

def pmfNeg (p q : PMF α) (x : α) : ℝ :=
  max (-pmfDiff p q x) 0

def positiveSet (p q : PMF α) : Set α :=
  {x | 0 < pmfDiff p q x}

lemma pmfReal_nonneg (p : PMF α) (x : α) : 0 ≤ pmfReal p x := by
  simp [pmfReal]

lemma summable_pmfReal {α : Type*} (p : PMF α) : Summable (pmfReal p) := by
  change Summable (fun x => (p x).toReal)
  exact ENNReal.summable_toReal p.tsum_coe_ne_top

lemma tsum_pmfReal (p : PMF α) : ∑' x, pmfReal p x = 1 := by
  calc
    ∑' x, pmfReal p x = ((∑' x, p x)).toReal := by
      symm
      exact ENNReal.tsum_toReal_eq (fun x => p.apply_ne_top x)
    _ = 1 := by simp [p.tsum_coe]

lemma toMeasure_real_apply_eq_tsum (p : PMF α) (s : Set α) :
    p.toMeasure.real s = ∑' x, s.indicator (pmfReal p) x := by
  rw [Measure.real_def, p.toMeasure_apply_eq_tsum s, ENNReal.tsum_toReal_eq]
  · congr with x
    by_cases hx : x ∈ s <;> simp [pmfReal, Set.indicator_apply, hx]
  · intro x
    by_cases hx : x ∈ s <;> simp [Set.indicator_apply, hx, p.apply_ne_top x]

lemma summable_pmfDiff (p q : PMF α) : Summable (pmfDiff p q) := by
  exact (summable_pmfReal p).sub (summable_pmfReal q)

lemma summable_indicator_pmfDiff (p q : PMF α) (s : Set α) :
    Summable (s.indicator (pmfDiff p q)) := by
  exact (summable_pmfDiff p q).indicator s

lemma pmfPos_nonneg (p q : PMF α) (x : α) : 0 ≤ pmfPos p q x := by
  simp [pmfPos]

lemma pmfNeg_nonneg (p q : PMF α) (x : α) : 0 ≤ pmfNeg p q x := by
  simp [pmfNeg]

lemma pmfPos_le_abs (p q : PMF α) (x : α) : pmfPos p q x ≤ |pmfDiff p q x| := by
  by_cases hx : 0 ≤ pmfDiff p q x
  · rw [pmfPos, max_eq_left hx, abs_of_nonneg hx]
  · have hx' : pmfDiff p q x < 0 := lt_of_not_ge hx
    rw [pmfPos, max_eq_right (le_of_lt hx'), abs_of_neg hx']
    linarith

lemma pmfNeg_le_abs (p q : PMF α) (x : α) : pmfNeg p q x ≤ |pmfDiff p q x| := by
  by_cases hx : 0 ≤ pmfDiff p q x
  · rw [pmfNeg, max_eq_right (by linarith), abs_of_nonneg hx]
    linarith
  · have hx' : pmfDiff p q x < 0 := lt_of_not_ge hx
    rw [pmfNeg, max_eq_left (by linarith), abs_of_neg hx']

lemma summable_abs_pmfDiff (p q : PMF α) : Summable (fun x => |pmfDiff p q x|) := by
  refine Summable.of_nonneg_of_le (f := fun x => pmfReal p x + pmfReal q x) (fun _ => abs_nonneg _) ?_ ?_
  · intro x
    have hp : 0 ≤ (p x).toReal := by simp
    have hq : 0 ≤ (q x).toReal := by simp
    have hupper : (p x).toReal - (q x).toReal ≤ (p x).toReal + (q x).toReal := by linarith
    have hlower : -((p x).toReal + (q x).toReal) ≤ (p x).toReal - (q x).toReal := by linarith
    exact (abs_le.2 ⟨hlower, hupper⟩)
  · exact (summable_pmfReal p).add (summable_pmfReal q)

lemma summable_pmfPos (p q : PMF α) : Summable (pmfPos p q) := by
  exact Summable.of_nonneg_of_le (pmfPos_nonneg p q) (pmfPos_le_abs p q) (summable_abs_pmfDiff p q)

lemma summable_pmfNeg (p q : PMF α) : Summable (pmfNeg p q) := by
  exact Summable.of_nonneg_of_le (pmfNeg_nonneg p q) (pmfNeg_le_abs p q) (summable_abs_pmfDiff p q)

lemma pmfDiff_eq_pos_sub_neg (p q : PMF α) (x : α) :
    pmfDiff p q x = pmfPos p q x - pmfNeg p q x := by
  by_cases hx : 0 ≤ pmfDiff p q x
  · rw [pmfPos, pmfNeg, max_eq_left hx, max_eq_right (by linarith)]
    ring
  · have hx' : pmfDiff p q x < 0 := lt_of_not_ge hx
    rw [pmfPos, pmfNeg, max_eq_right (le_of_lt hx'), max_eq_left (by linarith)]
    ring

lemma abs_pmfDiff_eq_pos_add_neg (p q : PMF α) (x : α) :
    |pmfDiff p q x| = pmfPos p q x + pmfNeg p q x := by
  by_cases hx : 0 ≤ pmfDiff p q x
  · rw [pmfPos, pmfNeg, max_eq_left hx, max_eq_right (by linarith), abs_of_nonneg hx]
    ring
  · have hx' : pmfDiff p q x < 0 := lt_of_not_ge hx
    rw [pmfPos, pmfNeg, max_eq_right (le_of_lt hx'), max_eq_left (by linarith), abs_of_neg hx']
    ring

lemma tsum_pmfDiff_eq_zero (p q : PMF α) : ∑' x, pmfDiff p q x = 0 := by
  change ∑' x, (pmfReal p x - pmfReal q x) = 0
  rw [Summable.tsum_sub (summable_pmfReal p) (summable_pmfReal q), tsum_pmfReal, tsum_pmfReal]
  ring

lemma tsum_pmfPos_eq_tsum_pmfNeg (p q : PMF α) :
    ∑' x, pmfPos p q x = ∑' x, pmfNeg p q x := by
  have hzero := tsum_pmfDiff_eq_zero p q
  rw [tsum_congr (pmfDiff_eq_pos_sub_neg p q)] at hzero
  rw [Summable.tsum_sub (summable_pmfPos p q) (summable_pmfNeg p q)] at hzero
  linarith

lemma tsum_abs_pmfDiff_eq_two_mul_pos (p q : PMF α) :
    ∑' x, |pmfDiff p q x| = 2 * ∑' x, pmfPos p q x := by
  rw [tsum_congr (abs_pmfDiff_eq_pos_add_neg p q)]
  rw [Summable.tsum_add (summable_pmfPos p q) (summable_pmfNeg p q)]
  have hEq := tsum_pmfPos_eq_tsum_pmfNeg p q
  linarith

lemma tsum_pmfPos_eq_half_abs (p q : PMF α) :
    ∑' x, pmfPos p q x = (1 / 2 : ℝ) * ∑' x, |pmfDiff p q x| := by
  rw [tsum_abs_pmfDiff_eq_two_mul_pos]
  ring

lemma real_diff_eq_tsum_indicator (p q : PMF α) (s : Set α) :
    p.toMeasure.real s - q.toMeasure.real s = ∑' x, s.indicator (pmfDiff p q) x := by
  calc
    p.toMeasure.real s - q.toMeasure.real s
        = (∑' x, s.indicator (pmfReal p) x) - ∑' x, s.indicator (pmfReal q) x := by
            rw [toMeasure_real_apply_eq_tsum, toMeasure_real_apply_eq_tsum]
    _ = ∑' x, (s.indicator (pmfReal p) x - s.indicator (pmfReal q) x) := by
            symm
            exact Summable.tsum_sub ((summable_pmfReal p).indicator s) ((summable_pmfReal q).indicator s)
    _ = ∑' x, s.indicator (pmfDiff p q) x := by
            refine tsum_congr ?_
            intro x
            by_cases hx : x ∈ s <;> simp [Set.indicator_apply, hx, pmfDiff, pmfReal]

lemma diff_le_tsum_pos (p q : PMF α) (s : Set α) :
    p.toMeasure.real s - q.toMeasure.real s ≤ ∑' x, pmfPos p q x := by
  rw [real_diff_eq_tsum_indicator]
  exact (summable_indicator_pmfDiff p q s).tsum_le_tsum
    (fun x => by
      by_cases hx : x ∈ s <;> simp [Set.indicator_apply, hx, pmfPos, pmfDiff]
      all_goals linarith)
    (summable_pmfPos p q)

lemma positiveSet_measurable (p q : PMF α) : MeasurableSet (positiveSet p q) := by
  classical
  simpa [positiveSet] using (Set.to_countable (positiveSet p q)).measurableSet

lemma positiveSet_indicator_eq_pos (p q : PMF α) :
    (positiveSet p q).indicator (pmfDiff p q) = pmfPos p q := by
  funext x
  by_cases hx : 0 < pmfDiff p q x
  · simp [positiveSet, Set.indicator_of_mem, hx, pmfPos, le_of_lt hx, max_eq_left]
  · have hx' : pmfDiff p q x ≤ 0 := le_of_not_gt hx
    simp [positiveSet, hx, pmfPos, hx', max_eq_right]

lemma positiveSet_real_diff_eq_tsum_pos (p q : PMF α) :
    p.toMeasure.real (positiveSet p q) - q.toMeasure.real (positiveSet p q)
      = ∑' x, pmfPos p q x := by
  rw [real_diff_eq_tsum_indicator, positiveSet_indicator_eq_pos]

lemma positiveSet_real_diff_eq_half_abs (p q : PMF α) :
    p.toMeasure.real (positiveSet p q) - q.toMeasure.real (positiveSet p q)
      = (1 / 2 : ℝ) * ∑' x, |pmfDiff p q x| := by
  rw [positiveSet_real_diff_eq_tsum_pos, tsum_pmfPos_eq_half_abs]

lemma real_compl_eq_one_sub (p : PMF α) (s : Set α) :
    p.toMeasure.real sᶜ = 1 - p.toMeasure.real s := by
  have hs : MeasurableSet s := by
    simpa using (Set.to_countable s).measurableSet
  have hsum : p.toMeasure s + p.toMeasure sᶜ = 1 := by
    simpa using measure_add_measure_compl (μ := p.toMeasure) hs
  have hA : p.toMeasure s ≠ ⊤ := by
    intro hA
    rw [hA, top_add] at hsum
    simp at hsum
  have hAc : p.toMeasure sᶜ ≠ ⊤ := by
    intro hAc
    rw [hAc, add_top] at hsum
    simp at hsum
  have hreal : p.toMeasure.real s + p.toMeasure.real sᶜ = 1 := by
    simpa [Measure.real_def, ENNReal.toReal_add, hA, hAc] using congrArg ENNReal.toReal hsum
  linarith

theorem discrete_totalVariationDistance_eq_half_tsum_abs (p q : PMF α) :
    totalVariationDistance p.toMeasure q.toMeasure
      = (1 / 2 : ℝ) * ∑' x, |pmfDiff p q x| := by
  let S : Set ℝ :=
    {d : ℝ | ∃ A : Set α, MeasurableSet A ∧ d = |p.toMeasure.real A - q.toMeasure.real A|}
  have hnonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨∅, MeasurableSet.empty, ?_⟩
    simp
  have hupper :
      ∀ d ∈ S, d ≤ (1 / 2 : ℝ) * ∑' x, |pmfDiff p q x| := by
    intro d hd
    rcases hd with ⟨A, hA, rfl⟩
    let δ := p.toMeasure.real A - q.toMeasure.real A
    by_cases hδ : 0 ≤ δ
    · have hbound := diff_le_tsum_pos p q A
      rw [abs_of_nonneg hδ]
      exact hbound.trans_eq (tsum_pmfPos_eq_half_abs p q)
    · have hδ' : δ < 0 := lt_of_not_ge hδ
      have hcomp :
          |δ| = p.toMeasure.real Aᶜ - q.toMeasure.real Aᶜ := by
        have hpcompl := real_compl_eq_one_sub p A
        have hqcompl := real_compl_eq_one_sub q A
        have hδreal : p.toMeasure.real A - q.toMeasure.real A < 0 := by
          simpa [δ] using hδ'
        rw [abs_of_neg hδreal, hpcompl, hqcompl]
        ring_nf
      rw [hcomp]
      exact (diff_le_tsum_pos p q Aᶜ).trans_eq (tsum_pmfPos_eq_half_abs p q)
  have hbounded : BddAbove S := ⟨(1 / 2 : ℝ) * ∑' x, |pmfDiff p q x|, hupper⟩
  have hlower :
      (1 / 2 : ℝ) * ∑' x, |pmfDiff p q x| ≤ totalVariationDistance p.toMeasure q.toMeasure := by
    unfold totalVariationDistance
    have hnonnegA :
        0 ≤ p.toMeasure.real (positiveSet p q) - q.toMeasure.real (positiveSet p q) := by
      rw [positiveSet_real_diff_eq_tsum_pos]
      exact tsum_nonneg (pmfPos_nonneg p q)
    have hmem : (1 / 2 : ℝ) * ∑' x, |pmfDiff p q x| ∈ S := by
      refine ⟨positiveSet p q, positiveSet_measurable p q, ?_⟩
      rw [← positiveSet_real_diff_eq_half_abs]
      rw [abs_of_nonneg hnonnegA]
    exact le_csSup hbounded hmem
  unfold totalVariationDistance
  apply le_antisymm
  · exact csSup_le hnonempty hupper
  · exact hlower

theorem d_TV_toReal_eq_totalVariationDistance (p q : PMF ℕ) :
    d_TV (fun n => (p n).toReal) (fun n => (q n).toReal)
      = totalVariationDistance p.toMeasure q.toMeasure := by
  rw [discrete_totalVariationDistance_eq_half_tsum_abs]
  rfl

section Continuous

noncomputable def densityMeasure (f : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (f x)

def densityDiff (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  f x - g x

def densityPos (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  max (densityDiff f g x) 0

def densityPositiveSet (f g : ℝ → ℝ) : Set ℝ :=
  {x | 0 < densityDiff f g x}

lemma densityMeasure_real_apply
    {f : ℝ → ℝ} (hf_int : Integrable f volume) (hf_nonneg : ∀ x, 0 ≤ f x)
    (s : Set ℝ) (hs : MeasurableSet s) :
    (densityMeasure f).real s = ∫ x in s, f x := by
  rw [densityMeasure, Measure.real_def, withDensity_apply _ hs]
  have h_int : Integrable f (volume.restrict s) := hf_int.restrict
  have h_nonneg : 0 ≤ᵐ[volume.restrict s] f := Filter.Eventually.of_forall hf_nonneg
  have hEq :
      ENNReal.ofReal (∫ x in s, f x) = ∫⁻ x in s, ENNReal.ofReal (f x) := by
    simpa using MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int h_nonneg
  have hint_nonneg : 0 ≤ ∫ x in s, f x := by
    exact MeasureTheory.integral_nonneg fun x => hf_nonneg x
  simpa [ENNReal.toReal_ofReal hint_nonneg] using (congrArg ENNReal.toReal hEq).symm

lemma densityMeasure_apply_univ
    {f : ℝ → ℝ} (hf_int : Integrable f volume) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_prob : ∫ x, f x = 1) :
    densityMeasure f Set.univ = 1 := by
  rw [densityMeasure, withDensity_apply' _ Set.univ, Measure.restrict_univ]
  have h_nonneg : 0 ≤ᵐ[volume] f := Filter.Eventually.of_forall hf_nonneg
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_int h_nonneg, hf_prob]
  norm_num

lemma densityMeasure_real_univ
    {f : ℝ → ℝ} (hf_int : Integrable f volume) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_prob : ∫ x, f x = 1) :
    (densityMeasure f).real Set.univ = 1 := by
  rw [Measure.real_def, densityMeasure_apply_univ hf_int hf_nonneg hf_prob]
  norm_num

lemma densityMeasure_real_compl_eq_one_sub
    {f : ℝ → ℝ} (hf_int : Integrable f volume) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_prob : ∫ x, f x = 1) (s : Set ℝ) (hs : MeasurableSet s) :
    (densityMeasure f).real sᶜ = 1 - (densityMeasure f).real s := by
  have hsum : densityMeasure f s + densityMeasure f sᶜ = 1 := by
    calc
      densityMeasure f s + densityMeasure f sᶜ = densityMeasure f Set.univ := by
        simpa using (measure_add_measure_compl (μ := densityMeasure f) hs)
      _ = 1 := densityMeasure_apply_univ hf_int hf_nonneg hf_prob
  have hs_ne_top : densityMeasure f s ≠ ⊤ := by
    intro hs_top
    rw [hs_top, top_add] at hsum
    simp at hsum
  have hsc_ne_top : densityMeasure f sᶜ ≠ ⊤ := by
    intro hsc_top
    rw [hsc_top, add_top] at hsum
    simp at hsum
  have hreal :
      (densityMeasure f).real s + (densityMeasure f).real sᶜ = 1 := by
    simpa [Measure.real_def, ENNReal.toReal_add, hs_ne_top, hsc_ne_top] using
      congrArg ENNReal.toReal hsum
  linarith

lemma densityDiff_measurable {f g : ℝ → ℝ}
    (hf_meas : Measurable f) (hg_meas : Measurable g) :
    Measurable (densityDiff f g) := by
  change Measurable (fun x => f x - g x)
  exact hf_meas.sub hg_meas

lemma densityPositiveSet_measurable {f g : ℝ → ℝ}
    (hf_meas : Measurable f) (hg_meas : Measurable g) :
    MeasurableSet (densityPositiveSet f g) := by
  have hdiff : Measurable (densityDiff f g) := densityDiff_measurable hf_meas hg_meas
  simpa [densityPositiveSet] using measurableSet_lt measurable_const hdiff

lemma densityPos_eq_half_abs_add {f g : ℝ → ℝ} (x : ℝ) :
    densityPos f g x = (|densityDiff f g x| + densityDiff f g x) / 2 := by
  by_cases hx : 0 ≤ densityDiff f g x
  · rw [densityPos, max_eq_left hx, abs_of_nonneg hx]
    ring
  · have hx' : densityDiff f g x < 0 := lt_of_not_ge hx
    rw [densityPos, max_eq_right (le_of_lt hx'), abs_of_neg hx']
    ring

lemma integrable_densityPos {f g : ℝ → ℝ}
    (hf_int : Integrable f volume) (hg_int : Integrable g volume) :
    Integrable (densityPos f g) volume := by
  have hdiff : Integrable (densityDiff f g) volume := by
    change Integrable (fun x => f x - g x) volume
    exact hf_int.sub hg_int
  have habs : Integrable (fun x => |densityDiff f g x|) volume := hdiff.norm
  have hadd : Integrable (fun x => |densityDiff f g x| + densityDiff f g x) volume := habs.add hdiff
  have hformula :
      densityPos f g = fun x => (|densityDiff f g x| + densityDiff f g x) / 2 := by
    funext x
    exact densityPos_eq_half_abs_add (f := f) (g := g) x
  rw [hformula]
  exact hadd.div_const 2

lemma densityPositiveSet_indicator_eq_pos {f g : ℝ → ℝ} :
    (densityPositiveSet f g).indicator (densityDiff f g) = densityPos f g := by
  funext x
  by_cases hx : 0 < densityDiff f g x
  · simp [densityPositiveSet, Set.indicator_of_mem, hx, densityPos, le_of_lt hx, max_eq_left]
  · have hx' : densityDiff f g x ≤ 0 := le_of_not_gt hx
    simp [densityPositiveSet, hx, densityPos, hx', max_eq_right]

lemma densityMeasure_real_diff_eq_integral_indicator
    {f g : ℝ → ℝ} (hf_int : Integrable f volume) (hg_int : Integrable g volume)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x)
    (s : Set ℝ) (hs : MeasurableSet s) :
    (densityMeasure f).real s - (densityMeasure g).real s
      = ∫ x, s.indicator (densityDiff f g) x := by
  calc
    (densityMeasure f).real s - (densityMeasure g).real s
        = (∫ x in s, f x) - ∫ x in s, g x := by
            rw [densityMeasure_real_apply hf_int hf_nonneg s hs,
              densityMeasure_real_apply hg_int hg_nonneg s hs]
    _ = (∫ x, s.indicator f x) - ∫ x, s.indicator g x := by
            rw [← integral_indicator hs, ← integral_indicator hs]
    _ = ∫ x, (s.indicator f x - s.indicator g x) := by
            symm
            exact MeasureTheory.integral_sub (hf_int.indicator hs) (hg_int.indicator hs)
    _ = ∫ x, s.indicator (densityDiff f g) x := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro x
            by_cases hx : x ∈ s <;> simp [Set.indicator_apply, hx, densityDiff]

lemma densityDiff_indicator_le_pos
    {f g : ℝ → ℝ} (s : Set ℝ) :
    ∀ x, s.indicator (densityDiff f g) x ≤ densityPos f g x := by
  intro x
  by_cases hx : x ∈ s
  · simpa [Set.indicator_apply, hx, densityPos] using
      (le_max_left (densityDiff f g x) 0)
  · simpa [Set.indicator_apply, hx, densityPos] using
      (le_max_right (densityDiff f g x) 0)

lemma densityDiff_le_integral_pos
    {f g : ℝ → ℝ} (hf_int : Integrable f volume) (hg_int : Integrable g volume)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x)
    (s : Set ℝ) (hs : MeasurableSet s) :
    (densityMeasure f).real s - (densityMeasure g).real s ≤ ∫ x, densityPos f g x := by
  rw [densityMeasure_real_diff_eq_integral_indicator hf_int hg_int hf_nonneg hg_nonneg s hs]
  have hdiff : Integrable (densityDiff f g) volume := by
    change Integrable (fun x => f x - g x) volume
    exact hf_int.sub hg_int
  exact MeasureTheory.integral_mono_ae
    (hdiff.indicator hs)
    (integrable_densityPos hf_int hg_int)
    (Filter.Eventually.of_forall (densityDiff_indicator_le_pos (f := f) (g := g) s))

lemma densityPos_integral_eq_half_abs
    {f g : ℝ → ℝ} (hf_int : Integrable f volume) (hg_int : Integrable g volume)
    (hf_prob : ∫ x, f x = 1) (hg_prob : ∫ x, g x = 1) :
    ∫ x, densityPos f g x = (1 / 2 : ℝ) * ∫ x, |densityDiff f g x| := by
  have hdiff : Integrable (densityDiff f g) volume := by
    change Integrable (fun x => f x - g x) volume
    exact hf_int.sub hg_int
  have habs : Integrable (fun x => |densityDiff f g x|) volume := hdiff.norm
  calc
    ∫ x, densityPos f g x
        = ∫ x, (|densityDiff f g x| + densityDiff f g x) / 2 := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro x
            exact densityPos_eq_half_abs_add (f := f) (g := g) x
    _ = ((∫ x, |densityDiff f g x|) + ∫ x, densityDiff f g x) / 2 := by
            rw [MeasureTheory.integral_div 2, MeasureTheory.integral_add habs hdiff]
    _ = ((∫ x, |densityDiff f g x|) + ((∫ x, f x) - ∫ x, g x)) / 2 := by
            have hsub : ∫ x, densityDiff f g x = (∫ x, f x) - ∫ x, g x := by
              simpa [densityDiff] using (MeasureTheory.integral_sub hf_int hg_int)
            rw [hsub]
    _ = (1 / 2 : ℝ) * ∫ x, |densityDiff f g x| := by
            rw [hf_prob, hg_prob]
            ring

lemma densityPositiveSet_real_diff_eq_half_abs
    {f g : ℝ → ℝ} (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_int : Integrable f volume) (hg_int : Integrable g volume)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hf_prob : ∫ x, f x = 1) (hg_prob : ∫ x, g x = 1) :
    (densityMeasure f).real (densityPositiveSet f g)
      - (densityMeasure g).real (densityPositiveSet f g)
      = (1 / 2 : ℝ) * ∫ x, |densityDiff f g x| := by
  rw [densityMeasure_real_diff_eq_integral_indicator hf_int hg_int hf_nonneg hg_nonneg
      (densityPositiveSet f g) (densityPositiveSet_measurable hf_meas hg_meas)]
  rw [densityPositiveSet_indicator_eq_pos]
  exact densityPos_integral_eq_half_abs hf_int hg_int hf_prob hg_prob

theorem continuous_totalVariationDistance_eq_half_integral_abs
    {f g : ℝ → ℝ} (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_int : Integrable f volume) (hg_int : Integrable g volume)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hf_prob : ∫ x, f x = 1) (hg_prob : ∫ x, g x = 1) :
    totalVariationDistance (densityMeasure f) (densityMeasure g)
      = (1 / 2 : ℝ) * ∫ x, |densityDiff f g x| := by
  let S : Set ℝ :=
    {d : ℝ | ∃ A : Set ℝ, MeasurableSet A ∧ d = |(densityMeasure f).real A - (densityMeasure g).real A|}
  have hnonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨∅, MeasurableSet.empty, ?_⟩
    simp
  have hupper :
      ∀ d ∈ S, d ≤ (1 / 2 : ℝ) * ∫ x, |densityDiff f g x| := by
    intro d hd
    rcases hd with ⟨A, hA, rfl⟩
    let δ := (densityMeasure f).real A - (densityMeasure g).real A
    by_cases hδ : 0 ≤ δ
    · rw [abs_of_nonneg hδ]
      exact (densityDiff_le_integral_pos hf_int hg_int hf_nonneg hg_nonneg A hA).trans_eq
        (densityPos_integral_eq_half_abs hf_int hg_int hf_prob hg_prob)
    · have hδ' : δ < 0 := lt_of_not_ge hδ
      have hcomp :
          |δ| = (densityMeasure f).real Aᶜ - (densityMeasure g).real Aᶜ := by
        rw [abs_of_neg hδ']
        rw [densityMeasure_real_compl_eq_one_sub hf_int hf_nonneg hf_prob A hA,
          densityMeasure_real_compl_eq_one_sub hg_int hg_nonneg hg_prob A hA]
        dsimp [δ]
        ring
      rw [hcomp]
      exact (densityDiff_le_integral_pos hf_int hg_int hf_nonneg hg_nonneg Aᶜ hA.compl).trans_eq
        (densityPos_integral_eq_half_abs hf_int hg_int hf_prob hg_prob)
  have hbounded : BddAbove S := ⟨(1 / 2 : ℝ) * ∫ x, |densityDiff f g x|, hupper⟩
  have hlower :
      (1 / 2 : ℝ) * ∫ x, |densityDiff f g x| ≤
        totalVariationDistance (densityMeasure f) (densityMeasure g) := by
    unfold totalVariationDistance
    have hnonnegA :
        0 ≤ (densityMeasure f).real (densityPositiveSet f g)
          - (densityMeasure g).real (densityPositiveSet f g) := by
      rw [densityPositiveSet_real_diff_eq_half_abs hf_meas hg_meas hf_int hg_int
        hf_nonneg hg_nonneg hf_prob hg_prob]
      positivity
    have hmem :
        (1 / 2 : ℝ) * ∫ x, |densityDiff f g x| ∈ S := by
      refine ⟨densityPositiveSet f g, densityPositiveSet_measurable hf_meas hg_meas, ?_⟩
      rw [← densityPositiveSet_real_diff_eq_half_abs hf_meas hg_meas hf_int hg_int
        hf_nonneg hg_nonneg hf_prob hg_prob]
      rw [abs_of_nonneg hnonnegA]
    exact le_csSup hbounded hmem
  unfold totalVariationDistance
  apply le_antisymm
  · exact csSup_le hnonempty hupper
  · exact hlower

end Continuous

end TVCore


