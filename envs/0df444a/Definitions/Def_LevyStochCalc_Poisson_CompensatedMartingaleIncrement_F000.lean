-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleIncrement_F000
-- name    : LevyStochCalc_Poisson_CompensatedMartingaleIncrement_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T17:00:30.197588+00:00
-- url     : https://prove2.me/theorems/32637dec-bbaa-4b9e-86bd-20447a0fc262
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedMartingaleIncrement
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedMartingaleIncrement. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleAdapted_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleAdapted_F001
import Definitions.Def_SourceProof_1fd4456750d7da453c9297b3

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Clamped compensator and increment boxes of the compensated simple integral

The compensator `∫₀ᵗ ∫_E |φ(s,e)|² ν(de) ds` of the quadratic variation in its explicit
clamped form `∑_i ν̂(timeRect i t) · ξᵢ²`, the a.e. decomposition of the increment
`simpleIntegral t − simpleIntegral s` over the increment rectangles
`timeRect i t \ timeRect i s` (each a clean box `Ioc a b ×ˢ Aᵢ`), and the box-level moment
identities behind the set-level isometry: independence of a future box increment from the
past, the weighted diagonal second moment, the vanishing of the weighted off-diagonal cross
terms, and cross-integrability of two compensated masses.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Clamped compensator

The compensator of the quadratic variation, `∫₀ᵗ ∫_E |φ(s,e)|² ν(de) ds`, in its
explicit clamped form `∑_i (referenceIntensity ν (timeRect i t)) · ξᵢ²`. -/

/-- The clamped time-interval `Ioc pc ps ∩ Icc 0 t` (the part of a full
time-interval visible up to running time `t`) equals `Ioc (min pc t) (min ps t)`,
when `0 ≤ pc`. -/
lemma Ioc_inter_Icc_eq_Ioc_min {pc ps t : ℝ} (hpc : 0 ≤ pc) :
    Set.Ioc pc ps ∩ Set.Icc 0 t = Set.Ioc (min pc t) (min ps t) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc]
  constructor
  · rintro ⟨⟨hpcx, hxps⟩, _, hxt⟩
    exact ⟨lt_of_le_of_lt (min_le_left _ _) hpcx, le_min hxps hxt⟩
  · rintro ⟨hmin, hx_min⟩
    have hxt : x ≤ t := hx_min.trans (min_le_right _ _)
    have hpcx : pc < x := (min_lt_iff.mp hmin).resolve_right (not_lt.mpr hxt)
    exact ⟨⟨hpcx, hx_min.trans (min_le_left _ _)⟩, le_of_lt (lt_of_le_of_lt hpc hpcx), hxt⟩
/-- The reference intensity of a clamped time-rectangle, evaluated explicitly:
`referenceIntensity ν (timeRect i t) = ENNReal.ofReal (min tᵢ₊₁ t − min tᵢ t) · ν(Aᵢ)`
for `0 ≤ t` (so both clamp points are `≥ 0`). -/
lemma referenceIntensity_timeRect_eq
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) {t : ℝ} (ht : 0 ≤ t) :
    LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i t)
      = ENNReal.ofReal (min (φ.partition i.succ) t - min (φ.partition i.castSucc) t)
          * ν (φ.A i) := by
  have hpc_nn : 0 ≤ φ.partition i.castSucc := by
    have := φ.partition_strictMono.monotone (Fin.zero_le i.castSucc)
    rwa [φ.partition_zero] at this
  unfold SimplePredictable.timeRect LevyStochCalc.Poisson.referenceIntensity
  rw [MeasureTheory.Measure.prod_prod]
  congr 1
  have h_subset : Set.Ioc (min (φ.partition i.castSucc) t) (min (φ.partition i.succ) t)
      ⊆ Set.Ici (0 : ℝ) :=
    fun x hx => (le_min hpc_nn ht).trans (le_of_lt hx.1)
  rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioc, Set.inter_eq_left.mpr h_subset,
    Real.volume_Ioc]
/-- The clamped double-lintegral of the constant-indicator on `fullRect i` over
`[0, t] × E` equals `c · referenceIntensity ν (timeRect i t)`. Clamped analogue of
`SimplePredictable.lintegral_indicator_fullRect`. -/
lemma lintegral_indicator_fullRect_clamped
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) (c : ℝ≥0∞) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
        (φ.fullRect i).indicator (fun _ : ℝ × E => c) (s, e) ∂ν ∂volume
      = c * LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i t) := by
  have hpc_nn : 0 ≤ φ.partition i.castSucc := by
    have := φ.partition_strictMono.monotone (Fin.zero_le i.castSucc)
    rwa [φ.partition_zero] at this
  have h_meas_fullRect : MeasurableSet (φ.fullRect i) := by
    unfold SimplePredictable.fullRect
    exact measurableSet_Ioc.prod (φ.A_measurable i)
  rw [MeasureTheory.lintegral_lintegral
    (f := fun s e => (φ.fullRect i).indicator (fun _ : ℝ × E => c) (s, e))
    (Measurable.indicator measurable_const h_meas_fullRect).aemeasurable]
  rw [show (fun (z : ℝ × E) => (φ.fullRect i).indicator (fun _ : ℝ × E => c) (z.1, z.2))
        = (φ.fullRect i).indicator (fun _ : ℝ × E => c) from by funext z; rfl]
  rw [MeasureTheory.lintegral_indicator_const h_meas_fullRect]
  rw [referenceIntensity_timeRect_eq φ i ht]
  unfold SimplePredictable.fullRect
  rw [MeasureTheory.Measure.prod_prod, MeasureTheory.Measure.restrict_apply measurableSet_Ioc,
    Ioc_inter_Icc_eq_Ioc_min hpc_nn, Real.volume_Ioc]
/-- **Clamped inner double-lintegral of `‖φ.eval‖²`** over `[0, t] × E`:
`∫₀ᵗ ∫_E ‖φ.eval s e ω‖² ∂ν ∂s = ∑_i ‖ξᵢ ω‖² · referenceIntensity ν (timeRect i t)`.
Clamped analogue of `SimplePredictable.lintegral_eval_sq`. -/
lemma lintegral_eval_sq_clamped
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (ω : Ω) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
        (‖φ.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume
      = ∑ i : Fin φ.N,
        (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2
          * LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i t) := by
  simp_rw [_root_.Prove2MeSourceProof.h_6112cafec42c0a69bf932916 φ _ _ ω]
  have h_inner_meas : ∀ s : ℝ, ∀ i : Fin φ.N,
      Measurable (fun e : E =>
        (φ.fullRect i).indicator (fun _ : ℝ × E => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e)) := by
    intro s i
    have h_meas_fullRect : MeasurableSet (φ.fullRect i) := by
      unfold SimplePredictable.fullRect
      exact measurableSet_Ioc.prod (φ.A_measurable i)
    exact (Measurable.indicator measurable_const h_meas_fullRect).comp measurable_prodMk_left
  rw [show (fun s : ℝ => ∫⁻ e, ∑ i : Fin φ.N,
        (φ.fullRect i).indicator (fun _ : ℝ × E => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e) ∂ν)
        = (fun s : ℝ => ∑ i : Fin φ.N, ∫⁻ e,
            (φ.fullRect i).indicator (fun _ : ℝ × E => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e) ∂ν) from by
    funext s
    exact MeasureTheory.lintegral_finsetSum _ (fun i _ => h_inner_meas s i)]
  have h_outer_meas : ∀ i : Fin φ.N,
      Measurable (fun s : ℝ => ∫⁻ e,
        (φ.fullRect i).indicator (fun _ : ℝ × E => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e) ∂ν) := by
    intro i
    have h_meas_fullRect : MeasurableSet (φ.fullRect i) := by
      unfold SimplePredictable.fullRect
      exact measurableSet_Ioc.prod (φ.A_measurable i)
    exact (Measurable.indicator measurable_const h_meas_fullRect).lintegral_prod_right'
  rw [MeasureTheory.lintegral_finsetSum _ (fun i _ => h_outer_meas i)]
  exact Finset.sum_congr rfl (fun i _ => lintegral_indicator_fullRect_clamped φ i _ ht)
/-- The simple integrand `eval`, as a function of the mark `e` (with `s`, `ω`
fixed), is measurable: it is a finite sum of indicators of the measurable mark
sets `Aᵢ` (cut by whether `s` lies in the `i`-th time interval). -/
lemma eval_mark_measurable
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (s : ℝ) (ω : Ω) :
    Measurable (fun e : E => φ.eval s e ω) := by
  simp_rw [_root_.Prove2MeSourceProof.h_1fd4456750d7da453c9297b3 φ s _ ω]
  refine Finset.measurable_sum _ (fun i _ => ?_)
  have h_meas_fullRect : MeasurableSet (φ.fullRect i) := by
    unfold SimplePredictable.fullRect
    exact measurableSet_Ioc.prod (φ.A_measurable i)
  exact (Measurable.indicator measurable_const h_meas_fullRect).comp measurable_prodMk_left
/-- The inner mark-integral `∫⁻_E ‖φ.eval s e ω‖² ∂ν`, as an explicit function of
the running time `s`: `∑_i 1_{(tᵢ, tᵢ₊₁]}(s) · ‖ξᵢ ω‖² · ν(Aᵢ)`. Measurable in `s`
and finite at each `s`. -/
lemma inner_lintegral_eval_sq_eq
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (s : ℝ) (ω : Ω) :
    ∫⁻ e, (‖φ.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν
      = ∑ i : Fin φ.N,
        (Set.Ioc (φ.partition i.castSucc) (φ.partition i.succ)).indicator
          (fun _ => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2 * ν (φ.A i)) s := by
  simp_rw [_root_.Prove2MeSourceProof.h_6112cafec42c0a69bf932916 φ s _ ω]
  have h_inner_meas : ∀ i : Fin φ.N,
      Measurable (fun e : E =>
        (φ.fullRect i).indicator (fun _ : ℝ × E => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e)) := by
    intro i
    have h_meas_fullRect : MeasurableSet (φ.fullRect i) := by
      unfold SimplePredictable.fullRect
      exact measurableSet_Ioc.prod (φ.A_measurable i)
    exact (Measurable.indicator measurable_const h_meas_fullRect).comp measurable_prodMk_left
  rw [MeasureTheory.lintegral_finsetSum _ (fun i _ => h_inner_meas i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hs : s ∈ Set.Ioc (φ.partition i.castSucc) (φ.partition i.succ)
  · rw [Set.indicator_of_mem hs]
    rw [show (fun e : E => (φ.fullRect i).indicator
          (fun _ : ℝ × E => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e))
        = (φ.A i).indicator (fun _ : E => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) from by
      funext e
      by_cases he : e ∈ φ.A i
      · rw [Set.indicator_of_mem he, Set.indicator_of_mem
          (show (s, e) ∈ φ.fullRect i from Set.mem_prod.mpr ⟨hs, he⟩)]
      · rw [Set.indicator_of_notMem he, Set.indicator_of_notMem
          (show (s, e) ∉ φ.fullRect i from fun hmem => he (Set.mem_prod.mp hmem).2)]]
    rw [MeasureTheory.lintegral_indicator_const (φ.A_measurable i)]
  · rw [Set.indicator_of_notMem hs]
    rw [show (fun e : E => (φ.fullRect i).indicator
          (fun _ : ℝ × E => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e)) = fun _ => 0 from by
      funext e
      rw [Set.indicator_of_notMem (show (s, e) ∉ φ.fullRect i from
        fun hmem => hs (Set.mem_prod.mp hmem).1)]]
    simp
/-- The inner mark-integral `∫⁻_E ‖φ.eval s e ω‖² ∂ν` is finite at each `s`
(each summand is bounded by `‖ξᵢ ω‖² · ν(Aᵢ) < ⊤`). -/
lemma inner_lintegral_eval_sq_ne_top
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (s : ℝ) (ω : Ω) :
    ∫⁻ e, (‖φ.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ≠ ⊤ := by
  rw [inner_lintegral_eval_sq_eq φ s ω]
  refine (ENNReal.sum_lt_top.mpr (fun i _ => ?_)).ne
  refine lt_of_le_of_lt (Set.indicator_le_self _ _ s) ?_
  exact ENNReal.mul_lt_top (by simp) (lt_top_iff_ne_top.mpr (φ.A_finite i))
/-- Measurability of the inner mark-integral as a function of running time `s`. -/
lemma measurable_inner_lintegral_eval_sq
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (ω : Ω) :
    Measurable (fun s : ℝ => ∫⁻ e, (‖φ.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν) := by
  simp_rw [inner_lintegral_eval_sq_eq φ _ ω]
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact (measurable_const.indicator measurableSet_Ioc)
/-! ### Increment decomposition

The increment `simpleIntegral t − simpleIntegral s` decomposes (a.e.) over the
increment rectangles `timeRect i t \ timeRect i s`, the basis for the set-level
quadratic-variation isometry. -/

/-! ### Set-level quadratic-variation isometry

The increment squares onto the increment boxes; off-diagonal cross terms vanish
(independence + zero mean), and diagonal terms give the box intensities
(independence + `compensated_second_moment`). -/

end LevyStochCalc.Poisson.Compensated


