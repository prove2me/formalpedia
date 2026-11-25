-- Prove2me | Definitions.Def_SourceProof_6451e0733c598e97f97c76a7
-- name    : SourceProof_6451e0733c598e97f97c76a7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:33:18.177013+00:00
-- url     : https://prove2.me/theorems/78d1cc5d-2a3a-47b6-9343-e707b3e2f64f
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.finiteStoppingTime_value_ae_eq_condExp_of_progressive

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_Probability_Martingale_OptionalSampling_ContinuousTime_F000
import Definitions.Def_SourceProof_051fc0b5e27a30fe29cf5be5
import Definitions.Def_SourceProof_4a90e1998d81dac996f193f9
import Definitions.Def_SourceProof_988ec49bcccd24848c73e05d
import Definitions.Def_SourceProof_d5e0692f6e3d9a9902fd804f
import Definitions.Def_SourceProof_e8f06b9dd9a18f2eede837c2

open private upperApprox_value_ae_eq_condExp from Definitions.Def_StochLean_Probability_Martingale_OptionalSampling_ContinuousTime_F000
/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Bounded optional sampling in continuous time

Upper countable-range stopping times are capped at the deterministic bound.
Their values are conditional expectations of one integrable terminal value,
so they are uniformly integrable. Right continuity yields the almost-sure
limit, and Vitali gives L1 convergence. No bounded-path assumption is used.

The core statement assumes progressive measurability and common-event right
continuity. An everywhere-right-continuous adapted martingale has the former
property by the existing ProcessCore theorem. Transport from an AE regular
version under a usual filtration is kept separate.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]


theorem _root_.Prove2MeSourceProof.h_6451e0733c598e97f97c76a7
    (hX : Martingale X F P) (hprog : IsStronglyProgressive F X)
    (hr : HasRightContinuousPaths X P) (τ : FiniteStoppingTime F)
    {T : ℝ≥0} (hτ : ∀ ω, τ ω ≤ T) :
    (fun ω ↦ X (τ ω) ω) =ᵐ[P] P[X T | τ.measurableSpace] := by
  have hint := (_root_.Prove2MeSourceProof.h_051fc0b5e27a30fe29cf5be5 hX) τ hτ hr
  have hmeas : StronglyMeasurable[τ.measurableSpace] (fun ω ↦ X (τ ω) ω) :=
    (measurable_stoppedValue hprog τ.isStoppingTime).stronglyMeasurable
  apply ae_eq_condExp_of_forall_setIntegral_eq (_root_.Prove2MeSourceProof.h_4a90e1998d81dac996f193f9 τ) (hX.integrable T)
    (fun _ _ _ ↦ hint.integrableOn) ?_ hmeas.aestronglyMeasurable
  intro A hA _
  have hlim := tendsto_setIntegral_of_L1' (fun ω ↦ X (τ ω) ω) hint.aestronglyMeasurable
    (Eventually.of_forall fun n ↦ memLp_one_iff_integrable.mp
      (((_root_.Prove2MeSourceProof.h_d5e0692f6e3d9a9902fd804f hX) τ T).memLp n))
    ((_root_.Prove2MeSourceProof.h_988ec49bcccd24848c73e05d hX) τ hτ hr) A
  have heq (n : ℕ) :
      (∫ ω in A, X (τ.upperApprox T n ω) ω ∂P) = ∫ ω in A, X T ω ∂P := by
    have hle : τ.measurableSpace ≤ (τ.upperApprox T n).measurableSpace :=
      τ.isStoppingTime.measurableSpace_mono (τ.upperApprox T n).isStoppingTime
        (fun ω ↦ WithTop.coe_le_coe.mpr ((_root_.Prove2MeSourceProof.h_e8f06b9dd9a18f2eede837c2 τ) hτ n ω))
    calc
      _ = ∫ ω in A, P[X T | (τ.upperApprox T n).measurableSpace] ω ∂P :=
        integral_congr_ae (ae_restrict_of_ae (upperApprox_value_ae_eq_condExp hX τ T n))
      _ = _ := setIntegral_condExp (_root_.Prove2MeSourceProof.h_4a90e1998d81dac996f193f9 (τ.upperApprox T n))
        (hX.integrable T) (hle A hA)
  exact tendsto_nhds_unique hlim (by simpa only [heq] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ ∫ ω in A, X T ω ∂P) atTop (𝓝 _)))
end MeasureTheory.Martingale


