-- Prove2me | Definitions.Def_SourceProof_9338c20a7c823520a42b860f
-- name    : SourceProof_9338c20a7c823520a42b860f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T08:00:00.70287+00:00
-- url     : https://prove2.me/theorems/6c0b5b02-ee41-4fca-ab7b-b6753bb22bd7
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.integral_pathwiseQuadraticVariation_eq_integral_sub_initial_sq

import Definitions.Def_StochLean_Probability_Martingale_DiscreteIntegral_F000
import Definitions.Def_StochLean_Probability_Martingale_QuadraticVariation_F001
import Definitions.Def_StochLean_Probability_Martingale_QuadraticVariation_F002
import Definitions.Def_SourceProof_19faa263b6d16ab54e81ed55
import Definitions.Def_SourceProof_9fc8747e59136e7ba38fddc9

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

variable [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

namespace Martingale
theorem _root_.Prove2MeSourceProof.h_9338c20a7c823520a42b860f
    (hM : Martingale M F P) (hlp : ∀ n, MemLp (M n) 2 P) (n : ℕ) :
    ∫ ω, pathwiseQuadraticVariation M n ω ∂P = ∫ ω, (M n ω - M 0 ω) ^ 2 ∂P :=
  (_root_.Prove2MeSourceProof.h_19faa263b6d16ab54e81ed55 hM.stronglyAdapted
    (fun k ↦ ((hlp (k + 1)).sub (hlp k)).integrable_sq) n).trans
      ((_root_.Prove2MeSourceProof.h_9fc8747e59136e7ba38fddc9 hM) hlp n).symm
end Martingale

end MeasureTheory


