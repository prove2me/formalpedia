-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoLocality_F001
-- name    : LevyStochCalc_Brownian_ItoLocality_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:08:01.036244+00:00
-- url     : https://prove2.me/theorems/59152c48-43a2-4f48-9e06-042b0bf0c591
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoLocality
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoLocality. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoLocality_F000
import Definitions.Def_SourceProof_8c755078af7ae88c406a7a36

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

theorem isStoppingTime_gridStopAux {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (t : ℝ) (n k : ℕ) :
    MeasureTheory.IsStoppingTime ℱ (gridStopAux τ t n k) := by
  intro i
  have hset : {ω | gridStopAux τ t n k ω ≤ ((i : ℝ) : WithTop ℝ)}
      = ⋃ j : Fin (k + 1), {ω | stepStop τ (gridPt t n j) ω ≤ ((i : ℝ) : WithTop ℝ)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, gridStopAux_le_iff]
    constructor
    · rintro ⟨j, hj, hjle⟩
      exact ⟨⟨j, Nat.lt_succ_of_le hj⟩, hjle⟩
    · rintro ⟨j, hjle⟩
      exact ⟨j.1, Nat.lt_succ_iff.mp j.2, hjle⟩
  rw [hset]
  exact MeasurableSet.iUnion fun j => isStoppingTime_stepStop τ hτ (gridPt t n j) i
/-- The stopping time that stops at the first point of the uniform grid on `[0, t]` with `n`
steps that lies strictly beyond `τ`. -/
noncomputable def gridStop (t : ℝ) (n : ℕ) : Ω → WithTop ℝ := gridStopAux τ t n n
theorem isStoppingTime_gridStop {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (t : ℝ) (n : ℕ) :
    MeasureTheory.IsStoppingTime ℱ (gridStop τ t n) :=
  isStoppingTime_gridStopAux τ hτ t n n
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem le_gridStop (t : ℝ) (n : ℕ) (ω : Ω) : τ ω ≤ gridStop τ t n ω :=
  le_gridStopAux τ t n n ω
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem gridPt_nonneg {t : ℝ} (ht : 0 ≤ t) (n k : ℕ) : 0 ≤ gridPt t n k := by
  unfold gridPt
  positivity
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem gridPt_lt_of_lt {t : ℝ} (ht : 0 < t) {n k : ℕ} (hk : k < n) : gridPt t n k < t := by
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le k) hk
  rw [gridPt, div_lt_iff₀ hn]
  have hkn : (k : ℝ) < (n : ℝ) := by exact_mod_cast hk
  nlinarith
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem gridPt_self {t : ℝ} {n : ℕ} (hn : n ≠ 0) : gridPt t n n = t := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [gridPt]
  field_simp
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- The grid stopping time takes one of the grid values strictly below `t`, or a value at
least `t`. -/
theorem gridStop_finiteRange {t : ℝ} {n : ℕ} (hn : n ≠ 0) (ω : Ω) :
    (∃ c ∈ (Finset.range n).image (gridPt t n),
        gridStop τ t n ω = ((c : ℝ) : WithTop ℝ))
      ∨ ((t : ℝ) : WithTop ℝ) ≤ gridStop τ t n ω := by
  rcases _root_.Prove2MeSourceProof.h_8c755078af7ae88c406a7a36 τ t n n ω with ⟨j, hj, hje⟩ | hje
  · rcases lt_or_eq_of_le hj with hlt | rfl
    · exact Or.inl ⟨gridPt t n j, Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hlt, rfl⟩, hje⟩
    · refine Or.inr ?_
      rw [gridStop, hje, gridPt_self hn]
  · exact Or.inr (by rw [gridStop, hje]; exact le_top)
end GridStop

section Local

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end Local

end LevyStochCalc.Brownian.Ito


