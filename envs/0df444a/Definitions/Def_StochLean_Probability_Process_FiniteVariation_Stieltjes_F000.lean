-- Prove2me | Definitions.Def_StochLean_Probability_Process_FiniteVariation_Stieltjes_F000
-- name    : StochLean_Probability_Process_FiniteVariation_Stieltjes_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:22:28.838469+00:00
-- url     : https://prove2.me/theorems/436b44d5-e99b-5f20-b34e-bcf5b67af08f
-- title:
--   StochLean: Probability.Process.FiniteVariation.Stieltjes F000

import Definitions.Def_StochLean_Probability_Process_FiniteVariation_Jordan_F000
import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Definitions.Def_SourceProof_4b71e23915dfe21f28d938f1
import Definitions.Def_SourceProof_6a931e0ab912939f33d99ec6
import Definitions.Def_SourceProof_cf9a7ad7f5832ad81464ff9b
import Definitions.Def_SourceProof_e6425243a41057923256952a
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Random Stieltjes measures of finite-variation processes

The three kernels are the deterministic canonical measures on each path. Their
restrictions through time `T` are measurable for the original `F T`, not merely
the ambient sigma-algebra. A common null-event reset supplies everywhere-good
versions from the almost-sure source assumptions under usual conditions.
-/

@[expose] public section

open MeasureTheory StochLean Set Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  (X : ℝ≥0 → Ω → ℝ) (ha : Adapted F X)
  (hv : ∀ ω, LocallyBoundedVariationOn (fun t ↦ X t ω) univ)
  (hr : ∀ ω, IsRightContinuousPath (fun t ↦ X t ω))

noncomputable def totalVariationKernel : Kernel Ω ℝ≥0 where
  toFun ω := (totalVariationStieltjes (fun t ↦ X t ω) (hv ω) (hr ω)).measure
  measurable' := _root_.Prove2MeSourceProof.h_cf9a7ad7f5832ad81464ff9b (fun t ↦
    ((_root_.Prove2MeSourceProof.h_e6425243a41057923256952a ha) hr t).mono (F.le t) le_rfl)
noncomputable def positiveVariationKernel : Kernel Ω ℝ≥0 where
  toFun ω := (positiveVariationStieltjes (fun t ↦ X t ω) (hv ω) (hr ω)).measure
  measurable' := _root_.Prove2MeSourceProof.h_cf9a7ad7f5832ad81464ff9b (fun t ↦
    ((_root_.Prove2MeSourceProof.h_6a931e0ab912939f33d99ec6 ha) hr t).mono (F.le t) le_rfl)
noncomputable def negativeVariationKernel : Kernel Ω ℝ≥0 where
  toFun ω := (negativeVariationStieltjes (fun t ↦ X t ω) (hv ω) (hr ω)).measure
  measurable' := _root_.Prove2MeSourceProof.h_cf9a7ad7f5832ad81464ff9b (fun t ↦
    ((_root_.Prove2MeSourceProof.h_4b71e23915dfe21f28d938f1 ha) hr t).mono (F.le t) le_rfl)
end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

end MeasureTheory


