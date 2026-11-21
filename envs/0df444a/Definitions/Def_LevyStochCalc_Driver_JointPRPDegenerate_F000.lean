-- Prove2me | Definitions.Def_LevyStochCalc_Driver_JointPRPDegenerate_F000
-- name    : LevyStochCalc_Driver_JointPRPDegenerate_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:38:50.902636+00:00
-- url     : https://prove2.me/theorems/c4ddc4db-6aa5-4d93-93a7-4c661d37899e
-- title:
--   Source declarations: LevyStochCalc.Driver.JointPRPDegenerate
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.JointPRPDegenerate. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPBrownian_F000
import Definitions.Def_LevyStochCalc_Driver_JointRange_F000
import Definitions.Def_SourceProof_8f9f280f81d8e75768b9aa58
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Order.Fin.Basic

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

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- With no marks the Poisson random measure generates nothing. -/
theorem naturalFiltration_poisson_eq_bot [IsEmpty E] (N : Poisson.PoissonRandomMeasure P ν)
    (t : ℝ) : Poisson.naturalFiltration N t = ⊥ := by
  refine le_bot_iff.mp (iSup₂_le fun B _ => ?_)
  have hconst : (fun ω => N.N ω B) = fun _ => (0 : ℝ≥0∞) := by
    funext ω
    rw [Set.eq_empty_of_isEmpty B]
    simp
  rw [hconst]
  have hm : Measurable[(⊥ : MeasurableSpace Ω)] fun _ : Ω => (0 : ℝ≥0∞) := measurable_const
  exact hm.comap_le
/-- With no coordinates the Brownian motion generates nothing. -/
theorem naturalFiltration_brownian_eq_bot
    (W : Brownian.Multidim.MultidimBrownianMotion P 0) (t : ℝ) :
    W.naturalFiltration t = ⊥ := by
  rw [naturalFiltration_apply]
  exact iSup_of_empty _
end Trivial

section Degenerate

/-- **The representation with no Brownian coordinates.** -/
theorem exists_jointIntegral_augFiltration_of_dim_zero (D : LevyDriver.{u, v, w} P 0 ν)
    {T : ℝ} (hT : 0 < T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[Brownian.augFiltration D.filtration P T] Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ (G : ∀ _ : Fin 0, HorizonIntegrand P (Brownian.augFiltration D.filtration P) T)
      (K : MarkedHorizonIntegrand P ν (Brownian.augFiltration D.filtration P) T),
      Z =ᵐ[P] jointIntegral (fun k => D.isBrownianFiltration_aug k)
        D.isPoissonFiltration_aug G K := by
  have hfe : Brownian.augFiltration D.filtration P T
      = Probability.aug (Poisson.naturalFiltration D.N T) ‹MeasurableSpace Ω› P := by
    change Probability.aug (D.filtration (max T 0)) ‹MeasurableSpace Ω› P = _
    rw [max_eq_left hT.le, filtration_apply, naturalFiltration_brownian_eq_bot, bot_sup_eq]
  refine _root_.Prove2MeSourceProof.h_8f9f280f81d8e75768b9aa58 (fun k => D.isBrownianFiltration_aug k)
    D.isPoissonFiltration_aug (LevyDriver.crossWitness D).aug hT ?_ hZ2 hZm hZ0
  intro r hr2 hrm hr0 _ hrN
  exact _root_.Prove2MeSourceProof.h_1c3ddaa3b8787f0fb2a5acd3 D.N D.isPoissonFiltration_aug hT
    (le_of_eq hfe) hr2 hrm hr0 hrN
end Degenerate

end LevyDriver

end LevyStochCalc.Driver


