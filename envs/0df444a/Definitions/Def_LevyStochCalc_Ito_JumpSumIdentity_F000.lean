-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpSumIdentity_F000
-- name    : LevyStochCalc_Ito_JumpSumIdentity_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:21:34.569681+00:00
-- url     : https://prove2.me/theorems/e2b0bdcb-2275-4940-92e2-e625685f0552
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpSumIdentity
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpSumIdentity. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_JumpTimesEnum_F002
import Definitions.Def_LevyStochCalc_Poisson_JumpTimesEnum_F003
import Definitions.Def_LevyStochCalc_Poisson_JumpTimesEnum_F004
import Definitions.Def_LevyStochCalc_Poisson_PathwiseIdentity_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The jump sum of a finite-activity window

On a window `(0, T] × A` of finite intensity a Poisson random measure is almost surely a finite
sum of Dirac masses. Integer-valuedness makes each of those masses a natural number and
time-simplicity caps it at one, so the integral of a function against the random measure over the
window is the plain sum of the function's values over a finite set of window points carrying
pairwise distinct times. Those times are exactly the arrival times of the mark set inside the
window, so the sum is indexed by the strictly monotone enumeration of the arrival times, each
paired with the unique mark carried at that time.

Chaining that identity with `LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_pathwise`
writes the jump sum of a predictable integrand `φ` as the Itô–Lévy integral of `φ` plus the
integral of `φ` itself against the reference intensity. That second term is not the compensator
drift of the Itô–Lévy formula: the latter integrates `u (x + γ e) - u x - ∑ i, γ i e * ∂ i u x`,
which differs from `φ = u (x + γ e) - u x` by the first-order term `∑ i, γ i e * ∂ i u x`.

## Main statements

* `LevyStochCalc.Poisson.exists_atomFinset_integral_eq_sum` — the integral over a window whose
  restricted measure is integer-valued and time-simple is a plain finite sum over window points.
* `LevyStochCalc.Poisson.ae_exists_atomEnum_integral_eq_sum` — almost surely that sum is indexed
  by the strictly monotone enumeration of the arrival times in the window.
* `LevyStochCalc.Poisson.ae_exists_atomEnum_sum_eq_stochasticIntegral_add` — almost surely the
  jump sum of a predictable integrand is its Itô–Lévy integral plus its integral against the
  reference intensity.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §2.3, §4.4.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section AtomMass

variable [MeasurableSingletonClass E] (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

/-- A time–mark point of positive mass for the measure restricted to a window lies in that
window. -/
theorem mem_window_of_restrict_ne_zero {T : ℝ} {ω : Ω} {p : ℝ × E}
    (hp : ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p} ≠ 0) :
    p ∈ Set.Ioc (0 : ℝ) T ×ˢ A := by
  by_contra hc
  exact hp (by rw [Measure.restrict_apply (measurableSet_singleton p),
    Set.singleton_inter_eq_empty.mpr hc, measure_empty])
/-- At a point of the window the measure restricted to the window carries the same mass as the
measure itself. -/
theorem restrict_singleton_eq_count_of_mem {T : ℝ} {ω : Ω} {p : ℝ × E}
    (hp : p ∈ Set.Ioc (0 : ℝ) T ×ˢ A) :
    ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p} = N.N ω ({p} : Set (ℝ × E)) := by
  rw [Measure.restrict_apply (measurableSet_singleton p),
    Set.inter_eq_self_of_subset_left (Set.singleton_subset_iff.mpr hp)]
/-- On a window carrying integer mass no two of whose points share a time, a point of the window
carrying mass carries mass exactly one. -/
theorem count_singleton_eq_one_of_restrict_ne_zero {T : ℝ} {ω : Ω}
    (hint : Probability.IsIntegerValued ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T + 1) ×ˢ A)))
    (hsimple : ∀ u : ℝ,
      N.N ω (Set.Ioc (0 : ℝ) (T + 1) ×ˢ A ∩ ({u} : Set ℝ) ×ˢ (Set.univ : Set E)) ≤ 1)
    {p : ℝ × E} (hp : ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p} ≠ 0) :
    N.N ω ({p} : Set (ℝ × E)) = 1 := by
  have hpW : p ∈ Set.Ioc (0 : ℝ) T ×ˢ A := mem_window_of_restrict_ne_zero N A hp
  have hpW' : p ∈ Set.Ioc (0 : ℝ) (T + 1) ×ˢ A :=
    Set.prod_mono (Set.Ioc_subset_Ioc_right (by linarith)) le_rfl hpW
  have hne : N.N ω ({p} : Set (ℝ × E)) ≠ 0 := by
    rw [← restrict_singleton_eq_count_of_mem N A hpW]
    exact hp
  have hle : N.N ω ({p} : Set (ℝ × E)) ≤ 1 := by
    refine le_trans (measure_mono ?_) (hsimple p.1)
    exact Set.singleton_subset_iff.mpr ⟨hpW', rfl, Set.mem_univ _⟩
  obtain ⟨n, hn⟩ := hint ({p} : Set (ℝ × E)) (measurableSet_singleton p)
  rw [restrict_singleton_eq_count_of_mem N A hpW'] at hn
  rw [hn] at hne hle ⊢
  have hn0 : n ≠ 0 := fun h => hne (by simp [h])
  have hn1 : n ≤ 1 := by exact_mod_cast hle
  have hn' : n = 1 := by omega
  rw [hn']
  simp
/-- On a window carrying integer mass no two of whose points share a time, the measure restricted
to the window carries mass exactly one at each of its points. -/
theorem restrict_singleton_eq_one_of_ne_zero {T : ℝ} {ω : Ω}
    (hint : Probability.IsIntegerValued ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T + 1) ×ˢ A)))
    (hsimple : ∀ u : ℝ,
      N.N ω (Set.Ioc (0 : ℝ) (T + 1) ×ˢ A ∩ ({u} : Set ℝ) ×ˢ (Set.univ : Set E)) ≤ 1)
    {p : ℝ × E} (hp : ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p} ≠ 0) :
    ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p} = 1 := by
  rw [restrict_singleton_eq_count_of_mem N A (mem_window_of_restrict_ne_zero N A hp)]
  exact count_singleton_eq_one_of_restrict_ne_zero N A hint hsimple hp
/-- On a window carrying integer mass no two of whose points share a time, two points of the
window carrying mass at the same time coincide. -/
theorem eq_of_fst_eq_of_restrict_ne_zero {T : ℝ} {ω : Ω}
    (hint : Probability.IsIntegerValued ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T + 1) ×ˢ A)))
    (hsimple : ∀ u : ℝ,
      N.N ω (Set.Ioc (0 : ℝ) (T + 1) ×ˢ A ∩ ({u} : Set ℝ) ×ˢ (Set.univ : Set E)) ≤ 1)
    {p q : ℝ × E} (hp : ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p} ≠ 0)
    (hq : ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {q} ≠ 0) (hpq : p.1 = q.1) : p = q := by
  by_contra hne
  have hp1 := count_singleton_eq_one_of_restrict_ne_zero N A hint hsimple hp
  have hq1 := count_singleton_eq_one_of_restrict_ne_zero N A hint hsimple hq
  have hpW' : p ∈ Set.Ioc (0 : ℝ) (T + 1) ×ˢ A :=
    Set.prod_mono (Set.Ioc_subset_Ioc_right (by linarith)) le_rfl
      (mem_window_of_restrict_ne_zero N A hp)
  have hqW' : q ∈ Set.Ioc (0 : ℝ) (T + 1) ×ˢ A :=
    Set.prod_mono (Set.Ioc_subset_Ioc_right (by linarith)) le_rfl
      (mem_window_of_restrict_ne_zero N A hq)
  have hsub : ({p} : Set (ℝ × E)) ∪ {q}
      ⊆ Set.Ioc (0 : ℝ) (T + 1) ×ˢ A ∩ ({p.1} : Set ℝ) ×ˢ (Set.univ : Set E) :=
    Set.union_subset (Set.singleton_subset_iff.mpr ⟨hpW', rfl, Set.mem_univ _⟩)
      (Set.singleton_subset_iff.mpr ⟨hqW', hpq.symm, Set.mem_univ _⟩)
  have hcon : (2 : ℝ≥0∞) ≤ 1 := by
    calc (2 : ℝ≥0∞) = N.N ω ({p} : Set (ℝ × E)) + N.N ω ({q} : Set (ℝ × E)) := by
          rw [hp1, hq1]; norm_num
      _ = N.N ω (({p} : Set (ℝ × E)) ∪ {q}) :=
          (measure_union (Set.disjoint_singleton.mpr hne) (measurableSet_singleton q)).symm
      _ ≤ N.N ω (Set.Ioc (0 : ℝ) (T + 1) ×ˢ A ∩ ({p.1} : Set ℝ) ×ˢ (Set.univ : Set E)) :=
          measure_mono hsub
      _ ≤ 1 := hsimple p.1
  norm_num at hcon
end AtomMass

section AtomFinset

variable [MeasurableSingletonClass E] (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

/-- **The jump sum over the atoms of a window.** On a window carrying integer mass no two of
whose points share a time, the integral of a function against the random measure is the plain sum
of the function's values over a finite set of window points with pairwise distinct times, and
those times are the arrival times of the mark set inside the window. -/
theorem exists_atomFinset_integral_eq_sum (hA : MeasurableSet A) {T : ℝ} {ω : Ω}
    {s : Finset (ℝ × E)}
    (hlint : ∀ g : ℝ × E → ℝ≥0∞,
      ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω)
        = ∑ p ∈ s, ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p} * g p)
    (hbochner : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω)
        = ∑ p ∈ s, (((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p}).toReal * g p)
    (hint : Probability.IsIntegerValued ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T + 1) ×ˢ A)))
    (hsimple : ∀ u : ℝ,
      N.N ω (Set.Ioc (0 : ℝ) (T + 1) ×ˢ A ∩ ({u} : Set ℝ) ×ˢ (Set.univ : Set E)) ≤ 1) :
    ∃ t : Finset (ℝ × E), (∀ p ∈ t, p ∈ Set.Ioc (0 : ℝ) T ×ˢ A) ∧
      (∀ p ∈ t, ∀ q ∈ t, p.1 = q.1 → p = q) ∧
      (jumpTimes t : Set ℝ)
        = {u : ℝ | ∃ i : ℕ, jumpTime N A i ω = (u : WithTop ℝ) ∧ 0 < u ∧ u ≤ T} ∧
      ∀ g : ℝ × E → ℝ, ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ p ∈ t, g p := by
  classical
  refine ⟨s.filter (fun p => ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p} ≠ 0),
    fun p hp => mem_window_of_restrict_ne_zero N A (Finset.mem_filter.mp hp).2,
    fun p hp q hq hpq => eq_of_fst_eq_of_restrict_ne_zero N A hint hsimple
      (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2 hpq, ?_, ?_⟩
  · rw [_root_.Prove2MeSourceProof.h_fd1036cdbd6026022399ce5b N A hA hint]
    ext x
    constructor
    · intro hx
      obtain ⟨p, hps, hpx⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      rw [← hpx]
      exact _root_.Prove2MeSourceProof.h_6a21e32323164b04c65b4566 N A (Finset.mem_filter.mp hps).2
    · rintro ⟨⟨hx0, hxT⟩, hne⟩
      obtain ⟨p, hps, hpm, hpx⟩ :=
        _root_.Prove2MeSourceProof.h_935684fe1e6aea9a3a83dadb N A hA hlint hx0 hxT hne
      exact Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hps, hpm⟩, hpx⟩)
  · intro g
    have hfilt : ∑ q ∈ s, (((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {q}).toReal * g q
        = ∑ q ∈ s.filter (fun q => ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {q} ≠ 0),
            (((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {q}).toReal * g q := by
      refine (Finset.sum_filter_of_ne ?_).symm
      intro x _ hx hzero
      exact hx (by rw [hzero, ENNReal.toReal_zero, zero_mul])
    rw [hbochner g, hfilt]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [restrict_singleton_eq_one_of_ne_zero N A hint hsimple (Finset.mem_filter.mp hq).2,
      ENNReal.toReal_one, one_mul]
end AtomFinset

section Enumeration

omit [MeasurableSpace E] in
/-- **A finite set of time–mark points with pairwise distinct times is enumerated by its
times.** -/
theorem exists_strictMono_enum_of_fst_inj (t : Finset (ℝ × E))
    (hinj : ∀ p ∈ t, ∀ q ∈ t, p.1 = q.1 → p = q) :
    ∃ (k : ℕ) (θ : Fin k → ℝ) (ε : Fin k → E), StrictMono θ ∧
      Set.range θ = (jumpTimes t : Set ℝ) ∧ (∀ i, (θ i, ε i) ∈ t) ∧
      ∀ g : ℝ × E → ℝ, ∑ p ∈ t, g p = ∑ i : Fin k, g (θ i, ε i) := by
  classical
  obtain ⟨k, θ, hmono, hrange⟩ := exists_strictMono_enum (jumpTimes t)
  have hex : ∀ i : Fin k, ∃ p : ℝ × E, p ∈ t ∧ p.1 = θ i := by
    intro i
    have hθ : θ i ∈ (jumpTimes t : Set ℝ) := by
      rw [← hrange]
      exact Set.mem_range_self i
    exact Finset.mem_image.mp (Finset.mem_coe.mp hθ)
  choose pt hpt hpθ using hex
  have hpair : ∀ i : Fin k, ((θ i, (pt i).2) : ℝ × E) = pt i := by
    intro i
    rw [← hpθ i]
  refine ⟨k, θ, fun i => (pt i).2, hmono, hrange, fun i => ?_, fun g => ?_⟩
  · rw [hpair i]
    exact hpt i
  · refine (Finset.sum_bij (fun (i : Fin k) _ => pt i) (fun i _ => hpt i) ?_ ?_ ?_).symm
    · intro a₁ _ a₂ _ hEq
      apply hmono.injective
      rw [← hpθ a₁, ← hpθ a₂, hEq]
    · intro b hb
      have hb1 : b.1 ∈ Set.range θ := by
        rw [hrange]
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
      obtain ⟨a, ha⟩ := hb1
      exact ⟨a, Finset.mem_univ a, hinj _ (hpt a) _ hb (by rw [hpθ a, ha])⟩
    · intro a _
      rw [hpair a]
end Enumeration

section AlmostEverywhere

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

end AlmostEverywhere

section Compensated

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

end Compensated

end LevyStochCalc.Poisson


