-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Probability_StoppedProgressive
-- name    : KLS408915f_LevyStochCalc_Probability_StoppedProgressive
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T11:25:24.520551+00:00
-- url     : https://prove2.me/theorems/7bacfe49-704f-4134-9c92-f2ac69177d8c
-- title:
--   Stopping a progressively measurable process
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `stopped τ H ω s` equals $H(\omega,s)$ when $s\le\tau(\omega)$, with $\tau:\Omega\to\mathbb R\cup\{\infty\}$, and equals $0$ otherwise; `stoppedRegion τ t` and `stoppedSet τ` describe the corresponding regions in $\Omega\times\mathbb R$. Under `IsStoppingTime`, the source proves measurability of these regions, joint measurability of the stopped process, and preservation of progressive measurability.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/StoppedProgressive.lean#L23-L159 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.StoppedProgressive`, definition bundle `KLS408915f_LevyStochCalc_Probability_StoppedProgressive`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Progressive
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Stopping

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/StoppedProgressive.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
namespace LevyStochCalc
namespace Probability
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
/-- A process cut off at a stopping time. -/
noncomputable def stopped (τ : Ω → WithTop ℝ) (H : Ω → ℝ → ℝ) (ω : Ω) (s : ℝ) : ℝ :=
  if (s : WithTop ℝ) ≤ τ ω then H ω s else 0
theorem abs_stopped_le (τ : Ω → WithTop ℝ) (H : Ω → ℝ → ℝ) (ω : Ω) (s : ℝ) :
    |stopped τ H ω s| ≤ |H ω s| := by
  rw [stopped]
  split_ifs
  · exact le_rfl
  · simp
/-- The region cut out by a stopping time before a time `t`. -/
def stoppedRegion (τ : Ω → WithTop ℝ) (t : ℝ) : Set (Ω × ℝ) :=
  {p : Ω × ℝ | p.2 ≤ t ∧ ((p.2 : ℝ) : WithTop ℝ) ≤ τ p.1}
/-- The cut region before `t` is measurable for the σ-algebra at `t`. -/
theorem measurableSet_stoppedRegion {ℱ : Filtration ℝ mΩ} {τ : Ω → WithTop ℝ}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (t : ℝ) :
    MeasurableSet[@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance] (stoppedRegion τ t) := by
  letI : MeasurableSpace Ω := ℱ t
  set U : Set (Ω × ℝ) := ⋃ q : ℚ, {ω : Ω | τ ω ≤ ((min (q : ℝ) t : ℝ) : WithTop ℝ)}
    ×ˢ (Set.Ioi (q : ℝ) ∩ Set.Iic t) with hUdef
  have hU : MeasurableSet[@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance] U := by
    refine MeasurableSet.iUnion fun q => MeasurableSet.prod ?_ ?_
    · exact (ℱ.mono (min_le_right (q : ℝ) t)) _ (hτ (min (q : ℝ) t))
    · exact measurableSet_Ioi.inter measurableSet_Iic
  have heq : stoppedRegion τ t = (Set.univ ×ˢ Set.Iic t) \ U := by
    ext p
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨Set.mem_univ _, h1⟩, ?_⟩
      rw [hUdef]
      rintro hmem
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hmem
      obtain ⟨hq1, hq2⟩ := hq
      have hle : ((p.2 : ℝ) : WithTop ℝ) ≤ ((min (q : ℝ) t : ℝ) : WithTop ℝ) := h2.trans hq1
      have hle' : p.2 ≤ min (q : ℝ) t := by exact_mod_cast hle
      exact absurd (hle'.trans (min_le_left _ _)) (not_le.mpr hq2.1)
    · rintro ⟨⟨-, h1⟩, h2⟩
      refine ⟨h1, ?_⟩
      by_contra hcon
      rw [not_le] at hcon
      have hne : τ p.1 ≠ ⊤ := by
        intro h
        rw [h] at hcon
        exact absurd hcon (by simp)
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
      rw [← hr] at hcon
      have hrlt : r < p.2 := by exact_mod_cast hcon
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hrlt
      refine h2 ?_
      rw [hUdef]
      refine Set.mem_iUnion.mpr ⟨q, ?_, ⟨hq2, h1⟩⟩
      change τ p.1 ≤ ((min (q : ℝ) t : ℝ) : WithTop ℝ)
      rw [← hr]
      have : r ≤ min (q : ℝ) t := le_min hq1.le (hq1.le.trans (hq2.le.trans h1))
      exact_mod_cast this
  rw [heq]
  exact (MeasurableSet.univ.prod measurableSet_Iic).diff hU
/-- **Cutting off at a stopping time preserves progressive measurability.** -/
theorem ProgressivelyMeasurable.stopped {ℱ : Filtration ℝ mΩ} {τ : Ω → WithTop ℝ}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) {H : Ω → ℝ → ℝ}
    (hH : ProgressivelyMeasurable ℱ H) :
    ProgressivelyMeasurable ℱ (LevyStochCalc.Probability.stopped τ H) := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have key : (fun p : Ω × ℝ =>
        (Set.Iic t).indicator (LevyStochCalc.Probability.stopped τ H p.1) p.2)
      = Set.indicator (stoppedRegion τ t)
        (fun p : Ω × ℝ => (Set.Iic t).indicator (H p.1) p.2) := by
    funext p
    by_cases h1 : p ∈ stoppedRegion τ t
    · obtain ⟨h1a, h1b⟩ := h1
      rw [Set.indicator_of_mem (show p ∈ stoppedRegion τ t from ⟨h1a, h1b⟩),
        Set.indicator_of_mem (show p.2 ∈ Set.Iic t from h1a),
        Set.indicator_of_mem (show p.2 ∈ Set.Iic t from h1a),
        LevyStochCalc.Probability.stopped, if_pos h1b]
    · rw [Set.indicator_of_notMem h1]
      by_cases h2 : p.2 ∈ Set.Iic t
      · have h3 : ¬ ((p.2 : ℝ) : WithTop ℝ) ≤ τ p.1 := fun hc => h1 ⟨h2, hc⟩
        rw [Set.indicator_of_mem h2, LevyStochCalc.Probability.stopped, if_neg h3]
      · rw [Set.indicator_of_notMem h2]
  rw [key]
  exact (hH t).indicator (measurableSet_stoppedRegion hτ t)
/-- The whole region cut out by a stopping time. -/
def stoppedSet (τ : Ω → WithTop ℝ) : Set (Ω × ℝ) :=
  {p : Ω × ℝ | ((p.2 : ℝ) : WithTop ℝ) ≤ τ p.1}
theorem measurableSet_stoppedSet {ℱ : Filtration ℝ mΩ} {τ : Ω → WithTop ℝ}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) : MeasurableSet (stoppedSet τ) := by
  have hcompl : (stoppedSet τ)ᶜ
      = ⋃ q : ℚ, {ω : Ω | τ ω ≤ ((q : ℝ) : WithTop ℝ)} ×ˢ Set.Ioi (q : ℝ) := by
    ext p
    simp only [stoppedSet, Set.mem_compl_iff, Set.mem_setOf_eq, not_le, Set.mem_iUnion,
      Set.mem_prod, Set.mem_Ioi]
    constructor
    · intro hlt
      have hne : τ p.1 ≠ ⊤ := by
        intro h
        rw [h] at hlt
        exact absurd hlt (by simp)
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
      rw [← hr] at hlt
      have hrlt : r < p.2 := by exact_mod_cast hlt
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hrlt
      refine ⟨q, ?_, hq2⟩
      rw [← hr]
      exact_mod_cast hq1.le
    · rintro ⟨q, hq1, hq2⟩
      calc τ p.1 ≤ ((q : ℝ) : WithTop ℝ) := hq1
        _ < ((p.2 : ℝ) : WithTop ℝ) := by exact_mod_cast hq2
  have hmc : MeasurableSet (stoppedSet τ)ᶜ := by
    rw [hcompl]
    exact MeasurableSet.iUnion fun q =>
      ((ℱ.le (q : ℝ)) _ (hτ (q : ℝ))).prod measurableSet_Ioi
  simpa using hmc.compl
/-- **Cutting off at a stopping time preserves joint measurability.** -/
theorem measurable_uncurry_stopped {ℱ : Filtration ℝ mΩ} {τ : Ω → WithTop ℝ}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) {H : Ω → ℝ → ℝ}
    (hH : Measurable (Function.uncurry H)) :
    Measurable (Function.uncurry (LevyStochCalc.Probability.stopped τ H)) := by
  have hfun : Function.uncurry (LevyStochCalc.Probability.stopped τ H)
      = Set.indicator (stoppedSet τ) (Function.uncurry H) := by
    funext p
    by_cases hp : p ∈ stoppedSet τ
    · rw [Set.indicator_of_mem hp]
      exact if_pos hp
    · rw [Set.indicator_of_notMem hp]
      exact if_neg hp
  rw [hfun]
  exact hH.indicator (measurableSet_stoppedSet hτ)
end Probability
end LevyStochCalc


