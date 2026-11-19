-- Prove2me | Definitions.Def_LevyStochCalc_Probability_OpenExitTime_F000
-- name    : LevyStochCalc_Probability_OpenExitTime_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:34:49.776537+00:00
-- url     : https://prove2.me/theorems/98ad0be1-456e-4321-a881-ab3a8b9db2e2
-- title:
--   Source declarations: LevyStochCalc.Probability.OpenExitTime
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.OpenExitTime. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_ExitTime_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Exit times from an open ball, for right-continuous paths

`openExitTime X R ω` is the first nonnegative time at which the path `X ω` has norm strictly
greater than `R`, and `⊤` when the path never leaves the closed ball. Strict exceedance is the
right notion for a path that is only right-continuous: the set of states of norm greater than `R`
is open, so a single exceedance propagates to a right neighbourhood and is therefore witnessed at
a rational time. That makes `{openExitTime < t}` measurable for the time-`t` σ-algebra, and hence
`openExitTime` a stopping time for the right-continuation of the filtration.

Below the exit time the path stays in the closed ball, and a path bounded by `R` on `[0, T]` has
not exited by `T`; neither fact needs any path regularity.

## Main statements

* `openExitTime_lt_coe_iff` — for a right-continuous path, the exit time is below `t` exactly
  when some rational time of `[0, t)` sees the norm exceed `R`.
* `isStoppingTime_openExitTime` — the exit time is a stopping time for the right-continuation
  `ℱ₊` of `ℱ`.
* `norm_le_of_lt_openExitTime` — strictly below the exit time the path has norm at most `R`.
* `le_openExitTime_of_forall_norm_le` — a path bounded by `R` on `[0, T]` has not exited by `T`.
-/

open MeasureTheory Filter Topology

namespace LevyStochCalc.Probability

universe u v

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [NormedAddCommGroup E]

/-- The nonnegative times at which the path `X ω` has norm strictly greater than `R`. -/
def openExitSet (X : Ω → ℝ → E) (R : ℝ) (ω : Ω) : Set ℝ := {t : ℝ | 0 ≤ t ∧ R < ‖X ω t‖}
open scoped Classical in
/-- The first nonnegative time at which the path `X ω` has norm strictly greater than `R`, and
`⊤` when the path never leaves the closed ball of radius `R`. -/
noncomputable def openExitTime (X : Ω → ℝ → E) (R : ℝ) (ω : Ω) : WithTop ℝ :=
  if (openExitSet X R ω).Nonempty then ((sInf (openExitSet X R ω) : ℝ) : WithTop ℝ) else ⊤
theorem bddBelow_openExitSet (X : Ω → ℝ → E) (R : ℝ) (ω : Ω) :
    BddBelow (openExitSet X R ω) := ⟨0, fun _ ht => ht.1⟩
/-- **Strictly below the exit time the path stays in the closed ball.** -/
theorem norm_le_of_lt_openExitTime {X : Ω → ℝ → E} {R : ℝ} {ω : Ω} {s : ℝ} (hs : 0 ≤ s)
    (hlt : (s : WithTop ℝ) < openExitTime X R ω) : ‖X ω s‖ ≤ R := by
  classical
  by_contra hcon
  have hmem : s ∈ openExitSet X R ω := ⟨hs, not_le.mp hcon⟩
  have hne : (openExitSet X R ω).Nonempty := ⟨s, hmem⟩
  rw [openExitTime, if_pos hne] at hlt
  have hle : sInf (openExitSet X R ω) ≤ s := csInf_le (bddBelow_openExitSet X R ω) hmem
  exact absurd (by exact_mod_cast hlt : s < sInf (openExitSet X R ω)) (not_lt.mpr hle)
/-- **A path bounded by `R` on `[0, T]` has not exited by `T`.** -/
theorem le_openExitTime_of_forall_norm_le {X : Ω → ℝ → E} {R : ℝ} {ω : Ω} {T : ℝ}
    (h : ∀ s : ℝ, 0 ≤ s → s ≤ T → ‖X ω s‖ ≤ R) : (T : WithTop ℝ) ≤ openExitTime X R ω := by
  classical
  rw [openExitTime]
  split_ifs with hne
  · rw [WithTop.coe_le_coe]
    refine le_csInf hne fun s hs => ?_
    by_contra hcon
    exact absurd (h s hs.1 (not_le.mp hcon).le) (not_le.mpr hs.2)
  · exact le_top
/-- **For a right-continuous path the exit time from an open ball is decided by the rationals.**
The states of norm greater than `R` form an open set, so a single exceedance at a time of
`[0, t)` propagates to a right neighbourhood, where a rational time can be chosen. -/
theorem openExitTime_lt_coe_iff {X : Ω → ℝ → E} {R : ℝ} {ω : Ω}
    (hright : ∀ s : ℝ, Tendsto (X ω) (𝓝[>] s) (𝓝 (X ω s))) (t : ℝ) :
    openExitTime X R ω < (t : WithTop ℝ) ↔
      ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) < t ∧ R < ‖X ω (q : ℝ)‖ := by
  classical
  constructor
  · intro hlt
    have hne : (openExitSet X R ω).Nonempty := by
      by_contra hcon
      rw [openExitTime, if_neg hcon] at hlt
      exact absurd hlt (not_lt.mpr le_top)
    rw [openExitTime, if_pos hne] at hlt
    have hlt' : sInf (openExitSet X R ω) < t := by exact_mod_cast hlt
    obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt hne hlt'
    -- the states of norm greater than `R` form an open set containing `X ω s`
    have hopen : IsOpen {y : E | R < ‖y‖} := isOpen_lt continuous_const continuous_norm
    have hmem : X ω s ∈ {y : E | R < ‖y‖} := hs.2
    have hev : ∀ᶠ r in 𝓝[>] s, X ω r ∈ {y : E | R < ‖y‖} :=
      hright s (hopen.mem_nhds hmem)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min hu hst)
    have hqmem : (q : ℝ) ∈ Set.Ioo s u := ⟨hq1, hq2.trans_le (min_le_left _ _)⟩
    exact ⟨q, le_of_lt (lt_of_le_of_lt hs.1 hq1), hq2.trans_le (min_le_right _ _), hsub hqmem⟩
  · rintro ⟨q, hq0, hqt, hqR⟩
    have hmem : (q : ℝ) ∈ openExitSet X R ω := ⟨hq0, hqR⟩
    have hne : (openExitSet X R ω).Nonempty := ⟨(q : ℝ), hmem⟩
    rw [openExitTime, if_pos hne, WithTop.coe_lt_coe]
    exact lt_of_le_of_lt (csInf_le (bddBelow_openExitSet X R ω) hmem) hqt
/-- The event that the exit time is below `t` is measurable for the time-`t` σ-algebra. -/
theorem measurableSet_openExitTime_lt {ℱ : Filtration ℝ mΩ} [MeasurableSpace E]
    [OpensMeasurableSpace E] {X : Ω → ℝ → E} (hadapt : Adapted ℱ fun r ω => X ω r)
    (hright : ∀ (ω : Ω) (s : ℝ), Tendsto (X ω) (𝓝[>] s) (𝓝 (X ω s))) (R t : ℝ) :
    MeasurableSet[ℱ t] {ω | openExitTime X R ω < (t : WithTop ℝ)} := by
  classical
  have hset : {ω | openExitTime X R ω < (t : WithTop ℝ)}
      = ⋃ q : ℚ, (if 0 ≤ (q : ℝ) ∧ (q : ℝ) < t then {ω | R < ‖X ω (q : ℝ)‖} else ∅) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    rw [openExitTime_lt_coe_iff (hright ω) t]
    constructor
    · rintro ⟨q, h1, h2, h3⟩
      exact ⟨q, by rw [if_pos ⟨h1, h2⟩]; exact h3⟩
    · rintro ⟨q, hq⟩
      by_cases h : 0 ≤ (q : ℝ) ∧ (q : ℝ) < t
      · rw [if_pos h] at hq
        exact ⟨q, h.1, h.2, hq⟩
      · rw [if_neg h] at hq
        exact absurd hq (Set.notMem_empty ω)
  rw [hset]
  letI : MeasurableSpace Ω := ℱ t
  refine MeasurableSet.iUnion fun q => ?_
  by_cases h : 0 ≤ (q : ℝ) ∧ (q : ℝ) < t
  · rw [if_pos h]
    exact measurableSet_lt measurable_const
      ((measurable_norm_of_adapted hadapt ((q : ℚ) : ℝ)).mono (ℱ.mono h.2.le) le_rfl)
  · rw [if_neg h]
    exact @MeasurableSet.empty Ω (ℱ t)
/-- **The exit time from an open ball of a right-continuous adapted path is a stopping time**
for the right-continuation of the filtration. -/
theorem isStoppingTime_openExitTime {ℱ : Filtration ℝ mΩ} [MeasurableSpace E]
    [OpensMeasurableSpace E] {X : Ω → ℝ → E} (hadapt : Adapted ℱ fun r ω => X ω r)
    (hright : ∀ (ω : Ω) (s : ℝ), Tendsto (X ω) (𝓝[>] s) (𝓝 (X ω s))) (R : ℝ) :
    IsStoppingTime ℱ.rightCont (openExitTime X R) :=
  MeasureTheory.isStoppingTime_of_measurableSet_lt_of_isRightContinuous
    fun t => ℱ.le_rightCont t _ (measurableSet_openExitTime_lt hadapt hright R t)
/-- **A path that has not exited by `T` stays in the closed ball strictly before `T`.** This is
the form the localisation uses: the window `[0, T)` of a path stopped at the exit time meets the
state function only inside a ball, where its derivatives are bounded. -/
theorem norm_le_of_le_openExitTime {X : Ω → ℝ → E} {R : ℝ} {ω : Ω} {T s : ℝ} (hs : 0 ≤ s)
    (hsT : s < T) (hT : (T : WithTop ℝ) ≤ openExitTime X R ω) : ‖X ω s‖ ≤ R :=
  norm_le_of_lt_openExitTime hs
    (lt_of_lt_of_le (by exact_mod_cast hsT : (s : WithTop ℝ) < (T : WithTop ℝ)) hT)
/-- The exit time grows with the radius. -/
theorem openExitTime_mono (X : Ω → ℝ → E) (ω : Ω) {R R' : ℝ} (h : R ≤ R') :
    openExitTime X R ω ≤ openExitTime X R' ω := by
  classical
  have hsub : openExitSet X R' ω ⊆ openExitSet X R ω := fun r hr => ⟨hr.1, lt_of_le_of_lt h hr.2⟩
  rw [openExitTime, openExitTime]
  split_ifs with h1 h2 h2
  · exact_mod_cast csInf_le_csInf (bddBelow_openExitSet X R ω) h2 hsub
  · exact le_top
  · exact absurd (Set.Nonempty.mono hsub h2) h1
  · exact le_rfl
end LevyStochCalc.Probability


