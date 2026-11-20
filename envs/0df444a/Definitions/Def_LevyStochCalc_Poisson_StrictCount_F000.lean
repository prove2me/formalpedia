-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_StrictCount_F000
-- name    : LevyStochCalc_Poisson_StrictCount_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T12:55:22.81308+00:00
-- url     : https://prove2.me/theorems/09c8e984-aeaf-4d52-bfc9-90b51a57835c
-- title:
--   Source declarations: LevyStochCalc.Poisson.StrictCount
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.StrictCount. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Filtered_F000
import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F000
import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F002
import Definitions.Def_LevyStochCalc_Probability_MarkedPredictable_F001
import Definitions.Def_SourceProof_521bf039082cd15fcfae08ee
import Definitions.Def_SourceProof_fdeeab164202d120da06e07d

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The strictly-past count of a Poisson random measure is predictable

The left endpoint of the level-`n` dyadic slab containing a positive time increases to that time
from strictly below, so the count of a set strictly before the time is the supremum over the
levels of the counts up to those endpoints. Each of those is a step process constant on the slabs
with a coefficient known at the left endpoint, hence predictable, and a countable supremum in the
extended nonnegative reals is measurable: the strictly-past count is predictable for every sample
point, with no null set involved.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Dyadic

/-- The left endpoint of the level-`n` dyadic slab containing a positive time. -/
noncomputable def dyadicLeft (n : ℕ) (s : ℝ) : ℝ := ((⌈s * 2 ^ n⌉₊ : ℝ) - 1) / 2 ^ n
theorem one_le_ceil_mul_pow {s : ℝ} (hs : 0 < s) (n : ℕ) : 1 ≤ ⌈s * 2 ^ n⌉₊ :=
  Nat.one_le_ceil_iff.mpr (by positivity)
theorem cast_ceil_pred {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ((⌈s * 2 ^ n⌉₊ - 1 : ℕ) : ℝ) = (⌈s * 2 ^ n⌉₊ : ℝ) - 1 := by
  rw [Nat.cast_sub (one_le_ceil_mul_pow hs n), Nat.cast_one]
theorem dyadicLeft_lt {s : ℝ} (hs : 0 < s) (n : ℕ) : dyadicLeft n s < s := by
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  rw [dyadicLeft, div_lt_iff₀ hpow]
  have := Nat.ceil_lt_add_one (le_of_lt (by positivity : (0 : ℝ) < s * 2 ^ n))
  linarith
theorem sub_le_dyadicLeft {s : ℝ} (n : ℕ) : s - (1 / 2 : ℝ) ^ n ≤ dyadicLeft n s := by
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  rw [dyadicLeft, le_div_iff₀ hpow]
  have hle := Nat.le_ceil (s * 2 ^ n)
  have hone : ((1 / 2 : ℝ) ^ n) * 2 ^ n = 1 := by
    rw [div_pow, one_pow]
    field_simp
  nlinarith [hle, hone]
theorem dyadicLeft_le_succ {s : ℝ} (hs : 0 < s) (n : ℕ) :
    dyadicLeft n s ≤ dyadicLeft (n + 1) s := by
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  set y : ℝ := s * 2 ^ n with hy
  have hy0 : 0 < y := by positivity
  have hyy : s * 2 ^ (n + 1) = 2 * y := by rw [hy, pow_succ]; ring
  have hkey : 2 * ⌈y⌉₊ ≤ ⌈2 * y⌉₊ + 1 := by
    have h1 : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0.le
    have h2 : (2 : ℝ) * y ≤ (⌈2 * y⌉₊ : ℝ) := Nat.le_ceil _
    have : (2 * ⌈y⌉₊ : ℝ) < (⌈2 * y⌉₊ : ℝ) + 2 := by linarith
    have hn : (2 * ⌈y⌉₊ : ℕ) < ⌈2 * y⌉₊ + 2 := by exact_mod_cast this
    omega
  rw [dyadicLeft, dyadicLeft, hyy, div_le_div_iff₀ hpow (by positivity)]
  have hcast : (2 * ⌈y⌉₊ : ℝ) ≤ (⌈2 * y⌉₊ : ℝ) + 1 := by exact_mod_cast hkey
  have hp : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  rw [hp]
  nlinarith [hpow, hcast]
theorem dyadicLeft_mono {s : ℝ} (hs : 0 < s) : Monotone fun n : ℕ => dyadicLeft n s :=
  monotone_nat_of_le_succ (dyadicLeft_le_succ hs)
theorem iUnion_Ioc_dyadicLeft {s : ℝ} (hs : 0 < s) :
    (⋃ n : ℕ, Set.Ioc (0 : ℝ) (dyadicLeft n s)) = Set.Ioo (0 : ℝ) s := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Ioo]
  constructor
  · rintro ⟨n, hx0, hxn⟩
    exact ⟨hx0, lt_of_le_of_lt hxn (dyadicLeft_lt hs n)⟩
  · rintro ⟨hx0, hxs⟩
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by linarith : (0 : ℝ) < s - x)
      (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨n, hx0, le_trans (by linarith) (sub_le_dyadicLeft n)⟩
theorem mem_timeSlab_dyadic {s : ℝ} (hs : 0 < s) (n : ℕ) :
    s ∈ timeSlab n (⌈s * 2 ^ n⌉₊ - 1) := by
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  rw [timeSlab, Set.mem_Ioc, cast_ceil_pred hs n]
  constructor
  · exact dyadicLeft_lt hs n
  · rw [sub_add_cancel, le_div_iff₀ hpow]
    exact Nat.le_ceil _
theorem cast_ceil_pred_div {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ((⌈s * 2 ^ n⌉₊ - 1 : ℕ) : ℝ) / 2 ^ n = dyadicLeft n s := by
  rw [cast_ceil_pred hs n, dyadicLeft]
end Dyadic

section Count

variable (N : PoissonRandomMeasure P ν)

/-- The count of a set up to the left endpoint of the level-`n` dyadic slab containing the time,
cut to a mark set. -/
noncomputable def stepCount (C : Set (ℝ × E)) (A : Set E) (T : ℝ) (n : ℕ)
    (ω : Ω) (s : ℝ) (e : E) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range ⌈T * 2 ^ n⌉₊,
    (Set.Ioc ((i : ℝ) / 2 ^ n) (((i : ℝ) + 1) / 2 ^ n) ×ˢ A).indicator
      (fun _ : ℝ × E => N.N ω (C ∩ Set.Ioc (0 : ℝ) ((i : ℝ) / 2 ^ n) ×ˢ Set.univ)) (s, e)
/-- The count of a set strictly before the time, cut to a mark set. -/
noncomputable def strictCount (C : Set (ℝ × E)) (A : Set E) (T : ℝ)
    (ω : Ω) (s : ℝ) (e : E) : ℝ≥0∞ :=
  ⨆ n : ℕ, stepCount N C A T n ω s e
theorem markedPredictable_stepCount {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) {C : Set (ℝ × E)} (hC : MeasurableSet C)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) (n : ℕ) :
    Probability.MarkedPredictable ℱ ν (stepCount N C A T n) := by
  have hcoef : ∀ i : ℕ, Measurable[ℱ ((i : ℝ) / 2 ^ n)]
      fun ω => N.N ω (C ∩ Set.Ioc (0 : ℝ) ((i : ℝ) / 2 ^ n) ×ˢ Set.univ) := by
    intro i
    refine hℱ.measurable ?_ (hC.inter (measurableSet_Ioc.prod MeasurableSet.univ))
    intro p hp
    exact ⟨hp.2.1.2, Set.mem_univ _⟩
  change Measurable[Probability.markedPredictableSigma ℱ ν] fun p : Ω × ℝ × E =>
    ∑ i ∈ Finset.range ⌈T * 2 ^ n⌉₊,
      (Set.Ioc ((i : ℝ) / 2 ^ n) (((i : ℝ) + 1) / 2 ^ n) ×ˢ A).indicator
        (fun _ : ℝ × E => N.N p.1 (C ∩ Set.Ioc (0 : ℝ) ((i : ℝ) / 2 ^ n) ×ˢ Set.univ))
        (p.2.1, p.2.2)
  exact Finset.measurable_sum _ fun i _ =>
    _root_.Prove2MeSourceProof.h_fdeeab164202d120da06e07d (by positivity) hA hAν (hcoef i)
theorem markedPredictable_strictCount {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) {C : Set (ℝ × E)} (hC : MeasurableSet C)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    Probability.MarkedPredictable ℱ ν (strictCount N C A T) := by
  change Measurable[Probability.markedPredictableSigma ℱ ν] fun p : Ω × ℝ × E =>
    ⨆ n : ℕ, stepCount N C A T n p.1 p.2.1 p.2.2
  exact Measurable.iSup fun n => markedPredictable_stepCount N hℱ hC hA hAν T n
theorem stepCount_eq {C : Set (ℝ × E)} {A : Set E} {T s : ℝ} (hs : 0 < s) (hsT : s ≤ T)
    {e : E} (he : e ∈ A) (ω : Ω) (n : ℕ) :
    stepCount N C A T n ω s e
      = N.N ω (C ∩ Set.Ioc (0 : ℝ) (dyadicLeft n s) ×ˢ Set.univ) := by
  classical
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hmem : ⌈s * 2 ^ n⌉₊ - 1 ∈ Finset.range ⌈T * 2 ^ n⌉₊ := by
    rw [Finset.mem_range]
    have h1 : 1 ≤ ⌈s * 2 ^ n⌉₊ := one_le_ceil_mul_pow hs n
    have h2 : ⌈s * 2 ^ n⌉₊ ≤ ⌈T * 2 ^ n⌉₊ := Nat.ceil_le_ceil (by nlinarith)
    omega
  have hzero : ∀ b ∈ Finset.range ⌈T * 2 ^ n⌉₊, b ≠ ⌈s * 2 ^ n⌉₊ - 1 →
      (Set.Ioc ((b : ℝ) / 2 ^ n) (((b : ℝ) + 1) / 2 ^ n) ×ˢ A).indicator
        (fun _ : ℝ × E => N.N ω (C ∩ Set.Ioc (0 : ℝ) ((b : ℝ) / 2 ^ n) ×ˢ Set.univ))
        (s, e) = 0 := by
    intro b _ hne
    refine Set.indicator_of_notMem (fun hmem2 => ?_) _
    exact Set.disjoint_left.mp (_root_.Prove2MeSourceProof.h_521bf039082cd15fcfae08ee n hne) hmem2.1
      (mem_timeSlab_dyadic hs n)
  rw [stepCount, Finset.sum_eq_single_of_mem _ hmem hzero,
    Set.indicator_of_mem
      (show ((s, e) : ℝ × E) ∈ Set.Ioc (((⌈s * 2 ^ n⌉₊ - 1 : ℕ) : ℝ) / 2 ^ n)
        ((((⌈s * 2 ^ n⌉₊ - 1 : ℕ) : ℝ) + 1) / 2 ^ n) ×ˢ A from
        ⟨mem_timeSlab_dyadic hs n, he⟩),
    cast_ceil_pred_div hs n]
end Count

end LevyStochCalc.Poisson


