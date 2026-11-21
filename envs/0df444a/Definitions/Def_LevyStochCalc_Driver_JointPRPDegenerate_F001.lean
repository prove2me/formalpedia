-- Prove2me | Definitions.Def_LevyStochCalc_Driver_JointPRPDegenerate_F001
-- name    : LevyStochCalc_Driver_JointPRPDegenerate_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:53:17.343859+00:00
-- url     : https://prove2.me/theorems/0d651bf9-5a4d-489b-a2ab-82a8c7546a22
-- title:
--   Source declarations: LevyStochCalc.Driver.JointPRPDegenerate
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.JointPRPDegenerate. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointPRPDegenerate_F000
import Definitions.Def_SourceProof_64792598230fcb5174f05c52
import Definitions.Def_SourceProof_da4e00f216757ccb78db0216

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The degenerate cases of the joint representation

Without Brownian coordinates the joint filtration is the Poisson one and the representation is
the compensated integral alone; without marks the Poisson random measure carries no information
and the representation is the Brownian one alone. Splitting on the two cases removes the
implementation hypotheses `0 < d` and `Nonempty E` from the representation theorem.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} {ν : Measure E} [SigmaFinite ν]

namespace LevyDriver

open Brownian.Ito Brownian.Multidim.MultidimBrownianMotion Poisson.Compensated

section Trivial

end Trivial

section Degenerate

/-- **The predictable representation property of a Lévy driver, in every case.** -/
theorem exists_jointIntegral_augFiltration_of_mean_zero (D : LevyDriver.{u, v, w} P d ν)
    {T : ℝ} (hT : 0 < T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[Brownian.augFiltration D.filtration P T] Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ (G : ∀ _ : Fin d, HorizonIntegrand P (Brownian.augFiltration D.filtration P) T)
      (K : MarkedHorizonIntegrand P ν (Brownian.augFiltration D.filtration P) T),
      Z =ᵐ[P] jointIntegral (fun k => D.isBrownianFiltration_aug k)
        D.isPoissonFiltration_aug G K := by
  rcases isEmpty_or_nonempty E with hE | hE
  · exact _root_.Prove2MeSourceProof.h_da4e00f216757ccb78db0216 D hT hZ2 hZm hZ0
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · exact exists_jointIntegral_augFiltration_of_dim_zero D hT hZ2 hZm hZ0
    · exact _root_.Prove2MeSourceProof.h_64792598230fcb5174f05c52 D hd hT hZ2 hZm hZ0
end Degenerate

end LevyDriver

end LevyStochCalc.Driver


