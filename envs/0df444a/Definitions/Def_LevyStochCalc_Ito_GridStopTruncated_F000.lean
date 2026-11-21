-- Prove2me | Definitions.Def_LevyStochCalc_Ito_GridStopTruncated_F000
-- name    : LevyStochCalc_Ito_GridStopTruncated_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:27:58.564522+00:00
-- url     : https://prove2.me/theorems/d6dc5767-fba6-4f2a-b89e-63dee7b04db1
-- title:
--   Source declarations: LevyStochCalc.Ito.GridStopTruncated
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.GridStopTruncated. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaShift_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The upward grid discretisation truncated at the horizon

The stopping time that stops at the first point of a uniform grid strictly beyond a stopping time
attains the horizon, so its values are not all grid points strictly below the horizon. Sending it
to `⊤` where it attains the horizon leaves a stopping time whose values are grid points strictly
below the horizon or `⊤`, and changes neither the horizon clipped at it nor an integrand cut off
at it on the closed window, hence neither the Itô integral at the horizon.

## Main statements

* `LevyStochCalc.Brownian.Ito.gridStopTrunc` — the upward grid discretisation of a stopping time,
  sent to `⊤` where it attains the horizon.
* `LevyStochCalc.Brownian.Ito.isStoppingTime_gridStopTrunc` — it is a stopping time.
* `LevyStochCalc.Brownian.Ito.gridStopTrunc_mono` — it is monotone in the stopping time.
* `LevyStochCalc.Brownian.Ito.measurableSpace_le_gridStopTrunc` — the σ-algebra of a stopping
  time is contained in that of its truncated grid discretisation.
* `LevyStochCalc.Brownian.Ito.gridStopTrunc_finiteRange` — its values are grid points strictly
  below the horizon, or `⊤`.
* `LevyStochCalc.Brownian.Ito.clipTime_gridStopTrunc` — the horizon clipped at it is the horizon
  clipped at the grid discretisation.
* `LevyStochCalc.Brownian.Ito.stopped_gridStopTrunc` — an integrand cut off at it agrees on the
  closed window with the integrand cut off at the grid discretisation.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_le_horizon` — the Itô integral
  at a horizon depends on the integrand only on the window up to that horizon.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_gridStop_of_gridStopTrunc` — Itô's formula
  between the grid discretisations of two stopping times, from the identity between their
  truncations.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Truncate

variable {Ω : Type u}

/-- The stopping time that stops at the first point of the uniform grid on `[0, T]` with `m`
steps strictly beyond `σ`, sent to `⊤` where that point attains the horizon. -/
noncomputable def gridStopTrunc (σ : Ω → WithTop ℝ) (T : ℝ) (m : ℕ) : Ω → WithTop ℝ :=
  fun ω => if ((T : ℝ) : WithTop ℝ) ≤ gridStop σ T m ω then ⊤ else gridStop σ T m ω
theorem gridStopTrunc_of_le (σ : Ω → WithTop ℝ) (T : ℝ) (m : ℕ) {ω : Ω}
    (h : ((T : ℝ) : WithTop ℝ) ≤ gridStop σ T m ω) : gridStopTrunc σ T m ω = ⊤ := by
  simp only [gridStopTrunc]
  rw [if_pos h]
theorem gridStopTrunc_of_lt (σ : Ω → WithTop ℝ) (T : ℝ) (m : ℕ) {ω : Ω}
    (h : gridStop σ T m ω < ((T : ℝ) : WithTop ℝ)) :
    gridStopTrunc σ T m ω = gridStop σ T m ω := by
  simp only [gridStopTrunc]
  rw [if_neg (not_le.mpr h)]
theorem gridStop_le_gridStopTrunc (σ : Ω → WithTop ℝ) (T : ℝ) (m : ℕ) (ω : Ω) :
    gridStop σ T m ω ≤ gridStopTrunc σ T m ω := by
  by_cases h : ((T : ℝ) : WithTop ℝ) ≤ gridStop σ T m ω
  · rw [gridStopTrunc_of_le σ T m h]
    exact le_top
  · rw [gridStopTrunc_of_lt σ T m (not_le.mp h)]
theorem le_gridStopTrunc (σ : Ω → WithTop ℝ) (T : ℝ) (m : ℕ) (ω : Ω) :
    σ ω ≤ gridStopTrunc σ T m ω :=
  le_trans (le_gridStop σ T m ω) (gridStop_le_gridStopTrunc σ T m ω)
theorem zero_le_gridStopTrunc {σ : Ω → WithTop ℝ} (hσ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ σ ω)
    (T : ℝ) (m : ℕ) (ω : Ω) : ((0 : ℝ) : WithTop ℝ) ≤ gridStopTrunc σ T m ω :=
  le_trans (hσ0 ω) (le_gridStopTrunc σ T m ω)
theorem stepStop_mono {σ τ : Ω → WithTop ℝ} (hστ : ∀ ω, σ ω ≤ τ ω) (c : ℝ) (ω : Ω) :
    stepStop σ c ω ≤ stepStop τ c ω := by
  simp only [stepStop]
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (le_trans h1 (hστ ω)) h2
  · exact le_top
  · exact le_rfl
theorem gridStopAux_mono {σ τ : Ω → WithTop ℝ} (hστ : ∀ ω, σ ω ≤ τ ω) (t : ℝ) (n k : ℕ)
    (ω : Ω) : gridStopAux σ t n k ω ≤ gridStopAux τ t n k ω := by
  induction k with
  | zero => exact stepStop_mono hστ (gridPt t n 0) ω
  | succ k ih =>
    have h1 : gridStopAux σ t n (k + 1) ω
        = min (stepStop σ (gridPt t n (k + 1)) ω) (gridStopAux σ t n k ω) := rfl
    have h2 : gridStopAux τ t n (k + 1) ω
        = min (stepStop τ (gridPt t n (k + 1)) ω) (gridStopAux τ t n k ω) := rfl
    rw [h1, h2]
    exact min_le_min (stepStop_mono hστ (gridPt t n (k + 1)) ω) ih
theorem gridStop_mono {σ τ : Ω → WithTop ℝ} (hστ : ∀ ω, σ ω ≤ τ ω) (t : ℝ) (n : ℕ) (ω : Ω) :
    gridStop σ t n ω ≤ gridStop τ t n ω :=
  gridStopAux_mono hστ t n n ω
/-- The truncated grid discretisation is monotone in the stopping time. -/
theorem gridStopTrunc_mono {σ τ : Ω → WithTop ℝ} (hστ : ∀ ω, σ ω ≤ τ ω) (T : ℝ) (m : ℕ)
    (ω : Ω) : gridStopTrunc σ T m ω ≤ gridStopTrunc τ T m ω := by
  have hle := gridStop_mono hστ T m ω
  by_cases h : ((T : ℝ) : WithTop ℝ) ≤ gridStop σ T m ω
  · rw [gridStopTrunc_of_le σ T m h, gridStopTrunc_of_le τ T m (le_trans h hle)]
  · rw [gridStopTrunc_of_lt σ T m (not_le.mp h)]
    by_cases h2 : ((T : ℝ) : WithTop ℝ) ≤ gridStop τ T m ω
    · rw [gridStopTrunc_of_le τ T m h2]
      exact le_top
    · rw [gridStopTrunc_of_lt τ T m (not_le.mp h2)]
      exact hle
end Truncate

section FiniteRange

variable {Ω : Type u}

theorem gridPt_image_nonneg {T : ℝ} (hT : 0 < T) (m : ℕ) :
    ∀ a ∈ (Finset.range m).image (gridPt T m), 0 ≤ a := by
  intro a ha
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ha
  exact gridPt_nonneg hT.le m k
theorem gridPt_image_lt {T : ℝ} (hT : 0 < T) (m : ℕ) :
    ∀ a ∈ (Finset.range m).image (gridPt T m), a < T := by
  intro a ha
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
  exact gridPt_lt_of_lt hT (Finset.mem_range.mp hk)
/-- The truncated grid discretisation takes one of the grid values strictly below the horizon, or
the value `⊤`. -/
theorem gridStopTrunc_finiteRange (σ : Ω → WithTop ℝ) {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0)
    (ω : Ω) :
    (∃ a ∈ (Finset.range m).image (gridPt T m),
        gridStopTrunc σ T m ω = ((a : ℝ) : WithTop ℝ))
      ∨ gridStopTrunc σ T m ω = ⊤ := by
  rcases gridStop_finiteRange σ hm ω with ⟨a, ha, hae⟩ | hge
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
    have hlt : gridStop σ T m ω < ((T : ℝ) : WithTop ℝ) := by
      rw [hae]
      exact_mod_cast gridPt_lt_of_lt hT (Finset.mem_range.mp hk)
    exact Or.inl ⟨gridPt T m k, ha, by rw [gridStopTrunc_of_lt σ T m hlt, hae]⟩
  · exact Or.inr (gridStopTrunc_of_le σ T m hge)
end FiniteRange

section StoppingTime

variable {Ω : Type u} [MeasurableSpace Ω]

end StoppingTime

section Window

variable {Ω : Type u}

end Window

section Horizon

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end Horizon

section GridShiftTransfer

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

end GridShiftTransfer

end LevyStochCalc.Brownian.Ito


