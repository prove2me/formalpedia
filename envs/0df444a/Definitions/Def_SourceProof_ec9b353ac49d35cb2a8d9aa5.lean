-- Prove2me | Definitions.Def_SourceProof_ec9b353ac49d35cb2a8d9aa5
-- name    : SourceProof_ec9b353ac49d35cb2a8d9aa5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:16:41.643757+00:00
-- url     : https://prove2.me/theorems/3715dd0f-870d-4ea7-bed6-612a796b962e
-- title:
--   LevyStochCalc source module: SourceProof_ec9b353ac49d35cb2a8d9aa5
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.tendsto_clipTime_gridStop` comes from the `LevyStochCalc.Ito.ItoFormulaStoppedLimit` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaStoppedLimit_F000
import Definitions.Def_SourceProof_c420c5d06462fb990bdab16f

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


theorem _root_.Prove2MeSourceProof.h_ec9b353ac49d35cb2a8d9aa5 (τ : Ω → WithTop ℝ)
    (hτ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ τ ω) {t : ℝ} (ht : 0 < t) (ω : Ω) :
    Filter.Tendsto (fun m : ℕ => clipTime (gridStop τ t m) t ω) Filter.atTop
      (𝓝 (clipTime τ t ω)) := by
  by_cases hle : ((t : ℝ) : WithTop ℝ) ≤ τ ω
  · have hconst : ∀ m : ℕ, LevyStochCalc.Brownian.Ito.clipTime (LevyStochCalc.Brownian.Ito.gridStop τ t m) t ω = LevyStochCalc.Brownian.Ito.clipTime τ t ω := by
      intro m
      rw [LevyStochCalc.Brownian.Ito.clipTime_of_le (le_trans hle (LevyStochCalc.Brownian.Ito.le_gridStop τ t m ω)), LevyStochCalc.Brownian.Ito.clipTime_of_le hle]
    simp only [hconst]
    exact tendsto_const_nhds
  · rw [not_le] at hle
    have hne : τ ω ≠ ⊤ := by
      intro hcon
      rw [hcon] at hle
      exact absurd hle (by simp)
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
    have hrt : r < t := by
      rw [← hr] at hle
      exact_mod_cast hle
    have hr0 : 0 ≤ r := by
      have h0 := hτ0 ω
      rw [← hr] at h0
      exact_mod_cast h0
    have hclip : LevyStochCalc.Brownian.Ito.clipTime τ t ω = r := by
      rw [LevyStochCalc.Brownian.Ito.clipTime_eq_min hr.symm, min_eq_right hrt.le]
    rw [hclip]
    refine tendsto_order.2 ⟨fun a ha => Filter.Eventually.of_forall fun m => ?_, fun b hb => ?_⟩
    · refine lt_of_lt_of_le ha ?_
      refine (_root_.Prove2MeSourceProof.h_824bcd558fff0b7dee883334 hrt.le).mp ?_
      rw [hr]
      exact LevyStochCalc.Brownian.Ito.le_gridStop τ t m ω
    · have hrs : r < min b t := lt_min hb hrt
      have hs0 : 0 < min b t := lt_of_le_of_lt hr0 hrs
      have hst : min b t ≤ t := min_le_right _ _
      have hτs : τ ω < ((min b t : ℝ) : WithTop ℝ) := by
        rw [← hr]
        exact_mod_cast hrs
      filter_upwards [_root_.Prove2MeSourceProof.h_c420c5d06462fb990bdab16f τ ht ω hs0 hst hτs] with m hm
      exact lt_of_lt_of_le (LevyStochCalc.Brownian.Ito.clipTime_lt_of_lt hm) (min_le_left _ _)
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


