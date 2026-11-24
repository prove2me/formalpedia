-- Prove2me | Definitions.Def_SourceProof_94b26ceff87499d497c994b8
-- name    : SourceProof_94b26ceff87499d497c994b8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:46:38.205079+00:00
-- url     : https://prove2.me/theorems/015db482-2213-40ff-b18c-d5d8aea950ec
-- title:
--   StochLean source theorem: MeasureTheory.memLp_discreteStochasticIntegral

import Definitions.Def_StochLean_Probability_Martingale_QuadraticVariation_F001
import Definitions.Def_StochLean_Probability_Martingale_QuadraticVariation_F002
import Definitions.Def_SourceProof_12c6e978969ea0272068034a
import Definitions.Def_SourceProof_5cc80b9bfdcf1557ce8e5ae0
import Definitions.Def_SourceProof_eae059fb1d843e68f8ce3b08

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # L2 isometry and estimates for discrete predictable integrals

These estimates will be reused on sampled stopping-time partitions. The integral and discrete
bracket are the existing canonical owners; no continuous-time bracket is introduced here.
-/

@[expose] public section

open Filter Finset
open scoped NNReal ENNReal BigOperators

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℕ mΩ} {M H : ℕ → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_94b26ceff87499d497c994b8
    (hM : ∀ n, MemLp (M n) 2 P) (hH : IsStronglyPredictable F H)
    (hb : ∀ n, ∃ C : ℝ, ∀ᵐ ω ∂P, ‖H n ω‖ ≤ C) (n : ℕ) :
    MemLp (discreteStochasticIntegral H M n) 2 P := by
  rw [_root_.Prove2MeSourceProof.h_12c6e978969ea0272068034a]
  apply memLp_finsetSum'
  intro k _
  obtain ⟨C, hC⟩ := hb (k + 1)
  exact ((hM (k + 1)).sub (hM k)).smul
    (memLp_top_of_bound ((hH.measurable_add_one k).mono (F.le k)).aestronglyMeasurable C hC)
variable [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

end MeasureTheory


