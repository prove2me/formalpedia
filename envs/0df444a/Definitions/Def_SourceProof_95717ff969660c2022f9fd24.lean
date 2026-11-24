-- Prove2me | Definitions.Def_SourceProof_95717ff969660c2022f9fd24
-- name    : SourceProof_95717ff969660c2022f9fd24
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:14:05.832533+00:00
-- url     : https://prove2.me/theorems/656686ba-cf6d-47a1-92e5-733388a5f595
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.min_const

import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F002
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F003
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F004
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F006
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Martingales are locally uniformly integrable

Protter I.6 Example 1 and Klenke 21.69(i). Stopping at deterministic time T
closes the martingale with the terminal variable X_T. Thus it is UI even when
the original martingale is not UI over the whole half-line. No continuous-time
optional sampling or integrability of an unbounded stopping value is used.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_95717ff969660c2022f9fd24 [SigmaFiniteFiltration P F]
    (hX : Martingale X F P) (T : ℝ≥0) :
    Martingale (fun t ↦ X (min t T)) F P := by
  refine ⟨fun t ↦ (hX.stronglyAdapted _).mono (F.mono (min_le_left t T)), ?_⟩
  intro s t hst
  change P[X (min t T) | F s] =ᵐ[P] X (min s T)
  by_cases hs : s ≤ T
  · simpa only [min_eq_left hs] using hX.condExp_ae_eq (le_min hst hs)
  · have hTs : T ≤ s := le_of_not_ge hs
    have hTt := hTs.trans hst
    rw [min_eq_right hTs, min_eq_right hTt,
      condExp_of_stronglyMeasurable (F.le s)
        ((hX.stronglyAdapted T).mono (F.mono hTs)) (hX.integrable T)]
end ProbabilityTheory


