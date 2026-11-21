-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoLocality_F000
-- name    : LevyStochCalc_Brownian_ItoLocality_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:04:24.512195+00:00
-- url     : https://prove2.me/theorems/f0499cef-4422-4f97-9351-5702eca6ab7e
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoLocality
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoLocality. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoOptionalStopping_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The local property of the Itô integral

Cutting the integrand off at a stopping time `τ` does not change the integral at a time the
stopping time has not yet reached. The stopping time is approximated from above by the
finite-range stopping times that stop at the first point of a uniform grid strictly beyond it,
for which the finite-range optional stopping identity applies directly; the approximation
converges in energy, and an `L²` squeeze removes the approximation.

## Main statements

* `LevyStochCalc.Brownian.Ito.stepStop`, `gridStop` — the two-valued and the grid stopping times.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_eq_of_le` — the local property.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_pos` — the integral to a
  positive time sees the integrand only at positive times.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_le` — two integrands agreeing
  up to a stopping time have the same integral where that time has not been reached.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (τ : Ω → WithTop ℝ)

section GridStop

/-- The two-valued stopping time that stops at `c`, unless `τ` has already reached `c`. -/
noncomputable def stepStop (c : ℝ) : Ω → WithTop ℝ :=
  fun ω => if (c : WithTop ℝ) ≤ τ ω then ⊤ else (c : WithTop ℝ)
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem le_stepStop (c : ℝ) (ω : Ω) : τ ω ≤ stepStop τ c ω := by
  rw [stepStop]
  split_ifs with h
  · exact le_top
  · exact (not_le.mp h).le
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem stepStop_eq_or (c : ℝ) (ω : Ω) :
    stepStop τ c ω = ((c : ℝ) : WithTop ℝ) ∨ stepStop τ c ω = ⊤ := by
  rw [stepStop]
  split_ifs with h
  · exact Or.inr rfl
  · exact Or.inl rfl
theorem isStoppingTime_stepStop {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (c : ℝ) :
    MeasureTheory.IsStoppingTime ℱ (stepStop τ c) := by
  intro i
  by_cases hci : c ≤ i
  · have hset : {ω | stepStop τ c ω ≤ ((i : ℝ) : WithTop ℝ)}
        = {ω | τ ω < ((c : ℝ) : WithTop ℝ)} := by
      ext ω
      simp only [stepStop, Set.mem_setOf_eq]
      by_cases h : ((c : ℝ) : WithTop ℝ) ≤ τ ω
      · simp only [if_pos h, top_le_iff]
        constructor
        · intro hcon
          exact absurd hcon (by simp)
        · intro hcon
          exact absurd h (not_le.mpr hcon)
      · simp only [if_neg h]
        exact ⟨fun _ => not_le.mp h, fun _ => by exact_mod_cast hci⟩
    rw [hset]
    exact ℱ.mono hci _ (hτ.measurableSet_lt c)
  · have hset : {ω | stepStop τ c ω ≤ ((i : ℝ) : WithTop ℝ)} = ∅ := by
      ext ω
      simp only [stepStop, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      by_cases h : ((c : ℝ) : WithTop ℝ) ≤ τ ω
      · simp only [if_pos h, top_le_iff]
        simp
      · simp only [if_neg h]
        exact fun hcon => hci (by exact_mod_cast hcon)
    rw [hset]
    exact @MeasurableSet.empty Ω (ℱ i)
/-- A point of the uniform grid on `[0, t]` with `n` steps. -/
noncomputable def gridPt (t : ℝ) (n k : ℕ) : ℝ := (k : ℝ) * t / (n : ℝ)
/-- The stopping time that stops at the first grid point strictly beyond `τ`, among the first
`k + 1` points. -/
noncomputable def gridStopAux (t : ℝ) (n : ℕ) : ℕ → Ω → WithTop ℝ
  | 0 => stepStop τ (gridPt t n 0)
  | (k + 1) => fun ω => min (stepStop τ (gridPt t n (k + 1)) ω) (gridStopAux t n k ω)
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem gridStopAux_le_iff (t : ℝ) (n k : ℕ) (ω : Ω) (a : WithTop ℝ) :
    gridStopAux τ t n k ω ≤ a ↔ ∃ j ≤ k, stepStop τ (gridPt t n j) ω ≤ a := by
  induction k with
  | zero =>
    constructor
    · intro h
      exact ⟨0, le_rfl, h⟩
    · rintro ⟨j, hj, hjle⟩
      rw [Nat.le_zero] at hj
      subst hj
      exact hjle
  | succ k ih =>
    rw [gridStopAux, min_le_iff, ih]
    constructor
    · rintro (h | ⟨j, hj, hjle⟩)
      · exact ⟨k + 1, le_rfl, h⟩
      · exact ⟨j, hj.trans (Nat.le_succ k), hjle⟩
    · rintro ⟨j, hj, hjle⟩
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · exact Or.inr ⟨j, Nat.lt_succ_iff.mp hlt, hjle⟩
      · have : j = k + 1 := le_antisymm hj hge
        subst this
        exact Or.inl hjle
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem le_gridStopAux (t : ℝ) (n k : ℕ) (ω : Ω) : τ ω ≤ gridStopAux τ t n k ω := by
  induction k with
  | zero => exact le_stepStop τ _ ω
  | succ k ih => exact le_min (le_stepStop τ _ ω) ih
end GridStop

section Local

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end Local

end LevyStochCalc.Brownian.Ito


