-- Prove2me | Definitions.Def_SourceProof_15f823291c6a3c3a94b3df5f
-- name    : SourceProof_15f823291c6a3c3a94b3df5f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:48.222072+00:00
-- url     : https://prove2.me/theorems/d3405c73-6400-4d33-b3d3-08ce01f547aa
-- title:
--   StochLean source theorem: MeasureTheory.pathwiseQuadraticVariation_discreteStochasticIntegral

import Definitions.Def_StochLean_Probability_Martingale_QuadraticVariation_F001
import Definitions.Def_StochLean_Probability_Martingale_QuadraticVariation_F002
import Definitions.Def_SourceProof_5cc80b9bfdcf1557ce8e5ae0
import Definitions.Def_SourceProof_72e355a9b50999c17ffa8bc4
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


theorem _root_.Prove2MeSourceProof.h_15f823291c6a3c3a94b3df5f (H M : ℕ → Ω → ℝ) (n : ℕ) :
    pathwiseQuadraticVariation (discreteStochasticIntegral H M) n = fun ω ↦
      ∑ k ∈ range n, (H (k + 1) ω) ^ 2 * (M (k + 1) ω - M k ω) ^ 2 := by
  funext ω
  apply sum_congr rfl
  intro k _
  have heq := congrFun (_root_.Prove2MeSourceProof.h_72e355a9b50999c17ffa8bc4 H M k) ω
  simp only [Pi.add_apply, smul_eq_mul, Pi.mul_apply, Pi.sub_apply] at heq
  rw [heq]
  ring
variable [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

end MeasureTheory


