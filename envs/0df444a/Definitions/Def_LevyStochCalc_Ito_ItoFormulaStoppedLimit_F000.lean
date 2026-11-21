-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoFormulaStoppedLimit_F000
-- name    : LevyStochCalc_Ito_ItoFormulaStoppedLimit_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:11:22.011522+00:00
-- url     : https://prove2.me/theorems/2011561f-a0cd-440b-ab16-274b683be95b
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoFormulaStoppedLimit
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoFormulaStoppedLimit. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoLocality_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaStopped_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula along a path stopped at an arbitrary stopping time

A stopping time is approximated from above by the stopping times that stop at the first point of
a uniform grid strictly beyond it, which take finitely many values. The horizons clipped at the
approximations converge to the horizon clipped at the stopping time, the integrands cut off at the
approximations converge in the energy of a window to the integrand cut off at the stopping time,
and Itô's formula along the finite-range stopped paths passes to the limit.

## Main statements

* `LevyStochCalc.Brownian.Ito.tendsto_clipTime_gridStop` — the clipped horizons converge.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_stopped_gridStop` — the cut-off integrands converge
  in the energy of the window.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.stopped_general` — the process stopped at a
  stopping time is the vector Itô process of the stopped coefficients.
* `LevyStochCalc.Brownian.Ito.itoFormula_stopped_general` — Itô's formula along the stopped path.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section ClipLimit

variable {Ω : Type u}

/-- A horizon clipped at a time that has already been passed lies below the passing time. -/
theorem clipTime_lt_of_lt {σ : Ω → WithTop ℝ} {t s : ℝ} {ω : Ω}
    (h : σ ω < ((s : ℝ) : WithTop ℝ)) : clipTime σ t ω < s := by
  have hne : σ ω ≠ ⊤ := by
    intro hcon
    rw [hcon] at h
    exact absurd h (by simp)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  have hrs : r < s := by
    rw [← hr] at h
    exact_mod_cast h
  rw [clipTime_eq_min hr.symm]
  exact lt_of_le_of_lt (min_le_right _ _) hrs
/-- The grid stopping time takes one of the grid values, or the value `⊤`. -/
theorem gridStop_eq_or_top (τ : Ω → WithTop ℝ) (t : ℝ) (m : ℕ) (ω : Ω) :
    (∃ c ∈ (Finset.range (m + 1)).image (gridPt t m),
        gridStop τ t m ω = ((c : ℝ) : WithTop ℝ)) ∨ gridStop τ t m ω = ⊤ := by
  rw [gridStop]
  rcases _root_.Prove2MeSourceProof.h_8c755078af7ae88c406a7a36 τ t m m ω with ⟨j, hj, hje⟩ | hje
  · exact Or.inl ⟨gridPt t m j,
      Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hj), rfl⟩, hje⟩
  · exact Or.inr hje
end ClipLimit

section Energy

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end Energy

section StoppedGeneral

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

end StoppedGeneral

end LevyStochCalc.Brownian.Ito


