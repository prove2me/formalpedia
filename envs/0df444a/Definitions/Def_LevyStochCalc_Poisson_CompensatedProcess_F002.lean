-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedProcess_F002
-- name    : LevyStochCalc_Poisson_CompensatedProcess_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:03:18.814768+00:00
-- url     : https://prove2.me/theorems/afc3e158-c9c9-4b96-8271-40823e966caf
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedProcess
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedProcess. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedApprox_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedApprox_F001
import Definitions.Def_SourceProof_7a12160ca4d56ce7d0871bc7

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated-Poisson `L²` integral process

The process `t ↦ ∫_0^t ∫_E φ(s, e) Ñ(ds, de)` is the `L²`-limit, at each time `t`, of the
compensated integrals of the master approximating sequence (`stageIntegral`). It is taken as
the `ℱ_t`-measurable representative of the `L²`-limit, so that it is adapted to the natural
filtration of the Poisson random measure; it is a square-integrable martingale, vanishes at
nonpositive times, and satisfies the Itô–Lévy isometry at every time.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration
    N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

section Process

end Process

section Isometry

/-- The mark integral `∫⁻_E ‖φ(ω, u, e)‖² ν(de)`. -/
noncomputable def markSq (ω : Ω) (u : ℝ) : ℝ≥0∞ := ∫⁻ e, (‖φ ω u e‖₊ : ℝ≥0∞) ^ 2 ∂ν
omit [IsProbabilityMeasure P] in
include h_meas in
lemma measurable_markSq : Measurable (Function.uncurry (markSq (ν := ν) φ)) := by
  have h : Measurable (fun r : (Ω × ℝ) × E => (‖φ r.1.1 r.1.2 r.2‖₊ : ℝ≥0∞) ^ 2) :=
    (ENNReal.continuous_coe.measurable.comp (h_meas.comp (by fun_prop :
      Measurable fun r : (Ω × ℝ) × E => ((r.1.1, r.1.2, r.2) : Ω × ℝ × E))).nnnorm).pow_const 2
  exact h.lintegral_prod_right'
/-- The horizon integral `∫⁻_Ω ∫⁻_{[0,t]} ∫⁻_E ‖φ‖²`. -/
noncomputable def horizonInt (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, markSq (ν := ν) φ ω s ∂volume ∂P
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
lemma horizonInt_eq (t : ℝ) :
    horizonInt (P := P) (ν := ν) φ t = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := rfl
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
lemma horizonInt_mono {s r : ℝ} (h : s ≤ r) :
    horizonInt (P := P) (ν := ν) φ s ≤ horizonInt (P := P) (ν := ν) φ r :=
  lintegral_mono fun _ => lintegral_mono_set (Set.Icc_subset_Icc_right h)
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
include h_sq_int_global in
lemma horizonInt_lt_top (t : ℝ) : horizonInt (P := P) (ν := ν) φ t < ⊤ :=
  (horizonInt_mono φ (le_trans (le_max_left t 0) (le_add_of_nonneg_right zero_le_one))).trans_lt
    (h_sq_int_global (max t 0 + 1) (by positivity))
omit [IsProbabilityMeasure P] in
include h_meas in
lemma horizonInt_add {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) :
    horizonInt (P := P) (ν := ν) φ r
      = horizonInt (P := P) (ν := ν) φ s
        + ∫⁻ ω, ∫⁻ u in Set.Ioc s r, markSq (ν := ν) φ ω u ∂volume ∂P := by
  have hinner : ∀ ω, ∫⁻ u in Set.Icc (0 : ℝ) r, markSq (ν := ν) φ ω u ∂volume
      = ∫⁻ u in Set.Icc (0 : ℝ) s, markSq (ν := ν) φ ω u ∂volume
        + ∫⁻ u in Set.Ioc s r, markSq (ν := ν) φ ω u ∂volume := by
    intro ω
    rw [← Set.Icc_union_Ioc_eq_Icc hs hsr, lintegral_union measurableSet_Ioc
      (Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx2.1 (not_lt.mpr hx1.2)))]
  rw [horizonInt, horizonInt, lintegral_congr hinner]
  exact lintegral_add_left' ((measurable_markSq φ h_meas).lintegral_prod_right'
    (ν := volume.restrict (Set.Icc (0 : ℝ) s))).aemeasurable _
include h_meas h_sq_int_global in
/-- Right-continuity of the horizon integral. -/
lemma horizonInt_right_tendsto {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (horizonInt (P := P) (ν := ν) φ) (𝓝[>] s) (𝓝 (horizonInt (P := P) (ν := ν) φ s)) := by
  have hz := _root_.Prove2MeSourceProof.h_7a12160ca4d56ce7d0871bc7 (P := P)
    (markSq (ν := ν) φ) (measurable_markSq φ h_meas) hs (lt_add_one s)
    (horizonInt_lt_top φ h_sq_int_global (s + 1)).ne
  have ht := (tendsto_const_nhds (x := horizonInt (P := P) (ν := ν) φ s)).add hz
  rw [add_zero] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (horizonInt_add φ h_meas hs hr.le).symm
omit [IsProbabilityMeasure P] in
/-- The nested triple integral over `Ω × E × [0, t]` as an integral for the product measure. -/
lemma triple_eq_lintegral_prod [SFinite P] {t : ℝ} (f : Ω → ℝ → E → ℝ≥0∞)
    (hf : Measurable (fun p : Ω × ℝ × E => f p.1 p.2.1 p.2.2)) :
    ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) t, f ω s e ∂volume ∂ν ∂P
      = ∫⁻ q : Ω × E × ℝ, f q.1 q.2.2 q.2.1
          ∂(P.prod (ν.prod (volume.restrict (Set.Icc (0 : ℝ) t)))) := by
  have hm : Measurable (fun q : Ω × E × ℝ => f q.1 q.2.2 q.2.1) :=
    hf.comp (by fun_prop : Measurable fun q : Ω × E × ℝ => ((q.1, q.2.2, q.2.1) : Ω × ℝ × E))
  rw [lintegral_prod _ hm.aemeasurable]
  refine lintegral_congr fun ω => ?_
  rw [lintegral_prod (fun y : E × ℝ => f (ω, y).1 (ω, y).2.2 (ω, y).2.1)
    (hm.comp (measurable_prodMk_left (x := ω))).aemeasurable]
end Isometry

end LevyStochCalc.Poisson.Compensated


