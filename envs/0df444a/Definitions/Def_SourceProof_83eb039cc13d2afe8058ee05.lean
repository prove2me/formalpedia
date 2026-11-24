-- Prove2me | Definitions.Def_SourceProof_83eb039cc13d2afe8058ee05
-- name    : SourceProof_83eb039cc13d2afe8058ee05
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:54.200488+00:00
-- url     : https://prove2.me/theorems/658c18a9-8c8a-46c8-b58a-9c2c8f02cef2
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.condExp_terminal_ae_eq_min

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

theorem _root_.Prove2MeSourceProof.h_83eb039cc13d2afe8058ee05
    [SigmaFiniteFiltration P F] (hX : Martingale X F P) (T t : ℝ≥0) :
    P[X T | F t] =ᵐ[P] X (min t T) := by
  by_cases ht : t ≤ T
  · simpa only [min_eq_left ht] using hX.condExp_ae_eq ht
  · have hTt : T ≤ t := le_of_not_ge ht
    rw [min_eq_right hTt, condExp_of_stronglyMeasurable (F.le t)
      ((hX.stronglyAdapted T).mono (F.mono hTt)) (hX.integrable T)]
end ProbabilityTheory


