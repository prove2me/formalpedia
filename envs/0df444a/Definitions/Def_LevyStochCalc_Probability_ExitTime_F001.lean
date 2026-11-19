-- Prove2me | Definitions.Def_LevyStochCalc_Probability_ExitTime_F001
-- name    : LevyStochCalc_Probability_ExitTime_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:34:35.731757+00:00
-- url     : https://prove2.me/theorems/b42f2efd-a37e-4366-855f-31fe4b245a96
-- title:
--   Source declarations: LevyStochCalc.Probability.ExitTime
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.ExitTime. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_ExitTime_F000
import Definitions.Def_SourceProof_0ae884fc5aa0cf4d6b9eb536

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Exit times of a process with continuous paths

`exitTime X k ω` is the first nonnegative time at which the path `X ω` has norm at least `k`, and
`⊤` when the path never reaches that norm. For continuous paths the comparison `exitTime X k ω ≤ t`
is decided by the values of the path on the rationals of `[0, t]`, so the exit time is a stopping
time for any filtration the process is adapted to. Letting `k` grow gives a localising sequence:
every time lies strictly below `exitTime X k` for all large `k`.
-/

open MeasureTheory

namespace LevyStochCalc.Probability

universe u v

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [NormedAddCommGroup E]

theorem gridPt_mem_Icc {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : gridPt t n ∈ Set.Icc (0 : ℝ) t :=
  ⟨le_max_left _ _, max_le ht (min_le_left _ _)⟩
/-- Clamping to `[0, t]` does not increase the distance to a point of `[0, t]`. -/
theorem abs_clamp_sub_le {t : ℝ} (ht : 0 ≤ t) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) t) (x : ℝ) :
    |max 0 (min t x) - s| ≤ |x - s| := by
  obtain ⟨hs0, hst⟩ := hs
  rcases lt_or_ge x 0 with hx | hx
  · rw [min_eq_right (hx.le.trans ht), max_eq_left hx.le,
      abs_of_nonpos (by linarith : (0 : ℝ) - s ≤ 0), abs_of_nonpos (by linarith : x - s ≤ 0)]
    linarith
  · rcases lt_or_ge t x with hxt | hxt
    · rw [min_eq_left hxt.le, max_eq_right ht,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - s),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - s)]
      linarith
    · rw [min_eq_right hxt, max_eq_right hx]
theorem exists_gridPt_near {t : ℝ} (ht : 0 ≤ t) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) t) {δ : ℝ}
    (hδ : 0 < δ) : ∃ n : ℕ, |gridPt t n - s| < δ := by
  obtain ⟨q, hq⟩ := exists_rat_near s hδ
  refine ⟨Denumerable.eqv ℚ q, ?_⟩
  have hqn : ((Denumerable.eqv ℚ).symm (Denumerable.eqv ℚ q) : ℚ) = q := Equiv.symm_apply_apply _ _
  rw [gridPt, hqn]
  refine lt_of_le_of_lt (abs_clamp_sub_le ht hs _) ?_
  rwa [abs_sub_comm]
/-- The comparison `exitTime X k ω ≤ t` is decided by the values of a continuous path on the
rationals of `[0, t]`. -/
theorem exitTime_le_iff_forall {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) (k : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    exitTime X k ω ≤ (t : WithTop ℝ) ↔
      ∀ n : ℕ, ∃ m : ℕ, k - ((n : ℝ) + 1)⁻¹ < ‖X ω (gridPt t m)‖ := by
  rw [_root_.Prove2MeSourceProof.h_0ae884fc5aa0cf4d6b9eb536 hX]
  constructor
  · rintro ⟨s, hs, hks⟩ n
    have hε : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    have hca : ContinuousAt (fun r => ‖X ω r‖) s := hX.norm.continuousAt
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hca _ hε
    obtain ⟨m, hm⟩ := exists_gridPt_near ht hs hδ
    refine ⟨m, ?_⟩
    have hdist : dist (gridPt t m) s < δ := by rwa [Real.dist_eq]
    have hclose := hδ' hdist
    rw [Real.dist_eq] at hclose
    have hle : ‖X ω s‖ - ‖X ω (gridPt t m)‖ ≤ |‖X ω (gridPt t m)‖ - ‖X ω s‖| := by
      rw [abs_sub_comm]; exact le_abs_self _
    linarith
  · intro hall
    obtain ⟨s₀, hs₀, hmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_isMaxOn
      (Set.nonempty_Icc.2 ht) hX.norm.continuousOn
    refine ⟨s₀, hs₀, ?_⟩
    rcases lt_or_ge ‖X ω s₀‖ k with hlt | hge
    · exfalso
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < k - ‖X ω s₀‖ by linarith)
      obtain ⟨m, hm⟩ := hall n
      have hle : ‖X ω (gridPt t m)‖ ≤ ‖X ω s₀‖ := hmax (gridPt_mem_Icc ht m)
      rw [one_div] at hn
      linarith
    · exact hge
theorem measurable_norm_of_adapted [MeasurableSpace E] [OpensMeasurableSpace E]
    {ℱ : Filtration ℝ mΩ} {X : Ω → ℝ → E} (hadapt : Adapted ℱ fun r ω => X ω r) (r : ℝ) :
    Measurable[ℱ r] fun ω => ‖X ω r‖ := by
  letI : MeasurableSpace Ω := ℱ r
  exact Measurable.norm (hadapt r)
theorem measurableSet_exitTime_le {ℱ : Filtration ℝ mΩ} [MeasurableSpace E]
    [OpensMeasurableSpace E] {X : Ω → ℝ → E} (hadapt : Adapted ℱ fun r ω => X ω r)
    (hcont : ∀ ω, Continuous (X ω)) (k t : ℝ) :
    MeasurableSet[ℱ t] {ω | exitTime X k ω ≤ (t : WithTop ℝ)} := by
  rcases lt_or_ge t 0 with ht | ht
  · have hempty : {ω | exitTime X k ω ≤ (t : WithTop ℝ)} = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hle
      obtain ⟨s, hs, -⟩ := (_root_.Prove2MeSourceProof.h_0ae884fc5aa0cf4d6b9eb536 (hcont ω) k t).1 hle
      exact absurd (hs.1.trans hs.2) (not_le.2 ht)
    rw [hempty]
    exact @MeasurableSet.empty Ω (ℱ t)
  · have hset : {ω | exitTime X k ω ≤ (t : WithTop ℝ)}
        = ⋂ n : ℕ, ⋃ m : ℕ, {ω | k - ((n : ℝ) + 1)⁻¹ < ‖X ω (gridPt t m)‖} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
      exact exitTime_le_iff_forall (hcont ω) k ht
    rw [hset]
    have hmeas : ∀ m : ℕ, Measurable[ℱ t] fun ω => ‖X ω (gridPt t m)‖ := fun m =>
      (measurable_norm_of_adapted hadapt (gridPt t m)).mono
        (ℱ.mono (gridPt_mem_Icc ht m).2) le_rfl
    letI : MeasurableSpace Ω := ℱ t
    exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun m =>
      measurableSet_lt measurable_const (hmeas m)
/-- The exit time of a continuous adapted process is a stopping time. -/
theorem isStoppingTime_exitTime {ℱ : Filtration ℝ mΩ} [MeasurableSpace E]
    [OpensMeasurableSpace E] {X : Ω → ℝ → E} (hadapt : Adapted ℱ fun r ω => X ω r)
    (hcont : ∀ ω, Continuous (X ω)) (k : ℝ) :
    IsStoppingTime ℱ (exitTime X k) := fun t => measurableSet_exitTime_le hadapt hcont k t
theorem exitTime_mono (X : Ω → ℝ → E) (ω : Ω) {k k' : ℝ} (h : k ≤ k') :
    exitTime X k ω ≤ exitTime X k' ω := by
  have hsub : exitSet X k' ω ⊆ exitSet X k ω := fun r hr => ⟨hr.1, h.trans hr.2⟩
  rw [exitTime, exitTime]
  split_ifs with h1 h2 h2
  · exact_mod_cast csInf_le_csInf (bddBelow_exitSet X k ω) h2 hsub
  · exact le_top
  · exact absurd (Set.Nonempty.mono hsub h2) h1
  · exact le_rfl
end LevyStochCalc.Probability


