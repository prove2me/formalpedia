-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_JumpTimes_F000
-- name    : LevyStochCalc_Poisson_JumpTimes_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T12:49:46.7101+00:00
-- url     : https://prove2.me/theorems/74827378-3122-4a9d-bf34-a0dd5b796fe3
-- title:
--   Source declarations: LevyStochCalc.Poisson.JumpTimes
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.JumpTimes. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Filtered_F000
import Definitions.Def_LevyStochCalc_Poisson_JumpSum_F000
import Mathlib.Probability.Process.Stopping

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Arrival times of a Poisson random measure on a mark set

`arrivalCount N A t ω` is the number of points of a Poisson random measure `N` whose time lies in
`(0, t]` and whose mark lies in `A`. It is monotone in the time, measurable for every filtration
for which `N` is a Poisson random measure, and right-continuous at every time from which it stays
finite. The `i`-th arrival time `jumpTime N A i` is the first nonnegative time at which the count
reaches `i`, and `⊤` when the count never reaches `i`; it is a stopping time for the
right-continuous filtration `ℱ₊`, and for `ℱ` itself when the counting process is everywhere
finite. Over a window on which the count is finite only finitely many arrival times occur, and
they carry a strictly monotone enumeration.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section MarkCount

/-- The number of points of the Poisson random measure `N` with time in `(0, t]` and mark in the
set `A`. -/
noncomputable def arrivalCount (N : PoissonRandomMeasure P ν) (A : Set E) (t : ℝ) (ω : Ω) : ℝ≥0∞ :=
  N.N ω (Set.Ioc (0 : ℝ) t ×ˢ A)
variable (N : PoissonRandomMeasure P ν) (A : Set E)

/-- The counting process vanishes at nonpositive times. -/
theorem arrivalCount_of_nonpos {t : ℝ} (ht : t ≤ 0) (ω : Ω) : arrivalCount N A t ω = 0 := by
  rw [arrivalCount, Set.Ioc_eq_empty (not_lt.mpr ht), Set.empty_prod, measure_empty]
/-- The counting process is monotone in the time. -/
theorem arrivalCount_mono (ω : Ω) : Monotone fun t => arrivalCount N A t ω := fun _ _ hst =>
  measure_mono (Set.prod_mono (Set.Ioc_subset_Ioc_right hst) le_rfl)
/-- The counting process on a measurable mark set is measurable for the time-`t` σ-algebra of any
filtration for which `N` is a Poisson random measure. -/
theorem measurable_arrivalCount {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A) (t : ℝ) :
    Measurable[ℱ t] (arrivalCount N A t) :=
  hℱ.measurable (Set.prod_mono Set.Ioc_subset_Iic_self (Set.subset_univ A))
    (measurableSet_Ioc.prod hA)
/-- The counting process on a measurable mark set is adapted to any filtration for which `N` is a
Poisson random measure. -/
theorem adapted_arrivalCount {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A) :
    Adapted ℱ (arrivalCount N A) :=
  fun t => measurable_arrivalCount N A hℱ hA t
/-- **Right-continuity of the counting process.** At a time from which the count stays finite the
count is the infimum of the counts at later times. -/
theorem iInf_arrivalCount_gt (hA : MeasurableSet A) {t u : ℝ} (htu : t < u) {ω : Ω}
    (hu : arrivalCount N A u ω ≠ ⊤) :
    ⨅ s ∈ Set.Ioi t, arrivalCount N A s ω = arrivalCount N A t ω := by
  refine le_antisymm ?_ (le_iInf₂ fun s hs => arrivalCount_mono N A ω (le_of_lt hs))
  obtain ⟨r, hr_anti, hr_mem, hr_tend⟩ := exists_seq_strictAnti_tendsto' htu
  have hanti : Antitone fun n : ℕ => Set.Ioc (0 : ℝ) (r n) ×ˢ A := fun _ _ hmn =>
    Set.prod_mono (Set.Ioc_subset_Ioc_right (hr_anti.antitone hmn)) le_rfl
  have hInter : (⋂ n, Set.Ioc (0 : ℝ) (r n) ×ˢ A) = Set.Ioc (0 : ℝ) t ×ˢ A := by
    ext x
    simp only [Set.mem_iInter, Set.mem_prod, Set.mem_Ioc]
    exact ⟨fun h => ⟨⟨(h 0).1.1, ge_of_tendsto' hr_tend fun n => (h n).1.2⟩, (h 0).2⟩,
      fun h n => ⟨⟨h.1.1, h.1.2.trans (hr_mem n).1.le⟩, h.2⟩⟩
  have hfin : ∃ n, N.N ω (Set.Ioc (0 : ℝ) (r n) ×ˢ A) ≠ ⊤ := by
    refine ⟨0, fun hcon => hu ?_⟩
    have hle : arrivalCount N A (r 0) ω ≤ arrivalCount N A u ω :=
      arrivalCount_mono N A ω (hr_mem 0).2.le
    exact top_le_iff.mp (hcon ▸ hle)
  have hkey := hanti.measure_iInter
    (fun _ => (measurableSet_Ioc.prod hA).nullMeasurableSet) hfin
  rw [hInter] at hkey
  calc ⨅ s ∈ Set.Ioi t, arrivalCount N A s ω
      ≤ ⨅ n : ℕ, arrivalCount N A (r n) ω :=
        le_iInf fun n => iInf₂_le (r n) (Set.mem_Ioi.mpr (hr_mem n).1)
    _ = arrivalCount N A t ω := hkey.symm
/-- The counting process on a mark set of finite intensity is almost surely finite at every
time. -/
theorem ae_forall_arrivalCount_ne_top (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, arrivalCount N A t ω ≠ ⊤ := by
  have h : ∀ n : ℕ, ∀ᵐ ω ∂P, N.N ω (Set.Ioc (0 : ℝ) (n : ℝ) ×ˢ A) ≠ ⊤ :=
    fun n => count_Ioc_ne_top N hA hAν (n : ℝ)
  filter_upwards [ae_all_iff.mpr h] with ω hω t
  obtain ⟨n, hn⟩ := exists_nat_gt t
  exact fun hcon => hω n (top_le_iff.mp (hcon ▸ arrivalCount_mono N A ω hn.le))
end MarkCount

section JumpTime

/-- The nonnegative times by which at least `i` points of `N` with mark in `A` have arrived. -/
def jumpTimeSet (N : PoissonRandomMeasure P ν) (A : Set E) (i : ℕ) (ω : Ω) : Set ℝ :=
  {t : ℝ | 0 ≤ t ∧ (i : ℝ≥0∞) ≤ arrivalCount N A t ω}
open scoped Classical in
/-- The `i`-th arrival time of `N` in the mark set `A`: the first nonnegative time at which the
number of points with mark in `A` reaches `i`, and `⊤` when it never does. -/
noncomputable def jumpTime (N : PoissonRandomMeasure P ν) (A : Set E) (i : ℕ) (ω : Ω) :
    WithTop ℝ :=
  if (jumpTimeSet N A i ω).Nonempty then ((sInf (jumpTimeSet N A i ω) : ℝ) : WithTop ℝ) else ⊤
variable (N : PoissonRandomMeasure P ν) (A : Set E)

theorem bddBelow_jumpTimeSet (i : ℕ) (ω : Ω) : BddBelow (jumpTimeSet N A i ω) :=
  ⟨0, fun _ ht => ht.1⟩
/-- Arrival times are nonnegative. -/
theorem coe_zero_le_jumpTime (i : ℕ) (ω : Ω) : ((0 : ℝ) : WithTop ℝ) ≤ jumpTime N A i ω := by
  rw [jumpTime]
  split_ifs with h
  · exact_mod_cast le_csInf h fun _ hr => hr.1
  · exact le_top
theorem jumpTimeSet_zero (ω : Ω) : jumpTimeSet N A 0 ω = Set.Ici (0 : ℝ) := by
  ext t
  simp [jumpTimeSet]
/-- The zeroth arrival time is the origin. -/
theorem jumpTime_zero (ω : Ω) : jumpTime N A 0 ω = ((0 : ℝ) : WithTop ℝ) := by
  have hInf : sInf (Set.Ici (0 : ℝ)) = 0 :=
    le_antisymm (csInf_le bddBelow_Ici Set.self_mem_Ici)
      (le_csInf Set.nonempty_Ici fun _ hx => hx)
  rw [jumpTime, jumpTimeSet_zero, if_pos Set.nonempty_Ici, hInf]
theorem jumpTimeSet_subset {i j : ℕ} (hij : i ≤ j) (ω : Ω) :
    jumpTimeSet N A j ω ⊆ jumpTimeSet N A i ω := fun _ ht =>
  ⟨ht.1, le_trans (by exact_mod_cast hij) ht.2⟩
/-- Arrival times increase with the index. -/
theorem jumpTime_mono {i j : ℕ} (hij : i ≤ j) (ω : Ω) :
    jumpTime N A i ω ≤ jumpTime N A j ω := by
  rw [jumpTime, jumpTime]
  split_ifs with h1 h2 h2
  · exact_mod_cast csInf_le_csInf (bddBelow_jumpTimeSet N A i ω) h2
      (jumpTimeSet_subset N A hij ω)
  · exact le_top
  · exact absurd (h2.mono (jumpTimeSet_subset N A hij ω)) h1
  · exact le_rfl
end JumpTime

section Finiteness

variable (N : PoissonRandomMeasure P ν) (A : Set E)

end Finiteness

end LevyStochCalc.Poisson


