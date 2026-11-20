-- Prove2me | Definitions.Def_LevyStochCalc_Probability_CondExpModification_F000
-- name    : LevyStochCalc_Probability_CondExpModification_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:35:36.489186+00:00
-- url     : https://prove2.me/theorems/23cd8f88-6fbf-4186-908d-ad83028d326c
-- title:
--   Source declarations: LevyStochCalc.Probability.CondExpModification
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.CondExpModification. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F001
import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F003
import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F004
import Definitions.Def_LevyStochCalc_Probability_CondExpRightContinuous_F000
import Definitions.Def_LevyStochCalc_Probability_FiltrationNNReal_F000
import Definitions.Def_LevyStochCalc_Probability_Quasimartingale_F000
import Definitions.Def_SourceProof_5a8f87bfb50175f242169433

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A right-continuous modification of the conditional-expectation martingale

For a right-continuous filtration on `ℝ` and `ξ ∈ L²`, the process `t ↦ 𝔼[ξ | ℱ t]` converges in
measure from the right at every time, because it converges in `L²`
(`LevyStochCalc.Probability.CondExpRightContinuous`). Reindexing by `ℝ≥0`
(`LevyStochCalc.Probability.FiltrationNNReal`) puts it in range of
`ProbabilityTheory.rightContModif`, whose hypotheses are supplied by
`LevyStochCalc.Probability.Quasimartingale`. The resulting process is a martingale for the same
filtration, agrees with `𝔼[ξ | ℱ t]` at every fixed time, is right-continuous along every path
and has left limits almost surely.

## Main statements

* `tendstoInMeasure_condExp_nhdsGT` — convergence in measure from the right.
* `condExpModif` — the modification, and `martingale_condExpModif`, `condExpModif_ae_eq`,
  `continuousWithinAt_condExpModif`, `ae_exists_tendsto_condExpModif_nhdsLT`.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The conditional expectations of a fixed `L²` variable converge in measure from the right**
along a right-continuous filtration. -/
theorem tendstoInMeasure_condExp_nhdsGT (ℱ : Filtration ℝ m₀) [ℱ.IsRightContinuous]
    {ξ : Ω → ℝ} (hξ : MemLp ξ 2 μ) (t : ℝ) :
    TendstoInMeasure μ (fun r => μ[ξ | ℱ r]) (𝓝[>] t) (μ[ξ | ℱ t]) :=
  (tendstoInMeasure_of_tendsto_Lp (_root_.Prove2MeSourceProof.h_5a8f87bfb50175f242169433 ℱ t (hξ.toLp ξ))).congr
    (fun r => hξ.condExpL2_ae_eq_condExp (ℱ.le r)) (hξ.condExpL2_ae_eq_condExp (ℱ.le t))
section Process

variable (μ) (ℱ : Filtration ℝ m₀) (ξ : Ω → ℝ)

/-- The conditional-expectation process of `ξ` for a filtration on `ℝ`, reindexed by `ℝ≥0`. -/
noncomputable def condExpProcess : ℝ≥0 → Ω → ℝ := fun t => μ[ξ | ℱ (t : ℝ)]
/-- A right-continuous modification of `condExpProcess`. -/
noncomputable def condExpModif : ℝ≥0 → Ω → ℝ := rightContModif (condExpProcess μ ℱ ξ)
variable {μ ℱ ξ}

theorem martingale_condExpProcess : Martingale (condExpProcess μ ℱ ξ) (restrictNNReal ℱ) μ :=
  martingale_condExp ξ (restrictNNReal ℱ) μ
theorem isRealQuasimartingale_condExpProcess :
    IsRealQuasimartingale (restrictNNReal ℱ) (condExpProcess μ ℱ ξ) μ :=
  isRealQuasimartingale_of_martingale martingale_condExpProcess
theorem tendstoInMeasure_condExpProcess_nhdsGT [ℱ.IsRightContinuous] (hξ : MemLp ξ 2 μ)
    (t : ℝ≥0) :
    TendstoInMeasure μ (condExpProcess μ ℱ ξ) (𝓝[>] t) (condExpProcess μ ℱ ξ t) := by
  have hφ : Tendsto (fun s : ℝ≥0 => (s : ℝ)) (𝓝[>] t) (𝓝[>] (t : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((NNReal.continuous_coe.tendsto t).mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact_mod_cast hs
  exact fun ε hε => (tendstoInMeasure_condExp_nhdsGT ℱ hξ (t : ℝ) ε hε).comp hφ
theorem condExpModif_ae_eq [ℱ.IsRightContinuous] (hξ : MemLp ξ 2 μ) (t : ℝ≥0) :
    condExpModif μ ℱ ξ t =ᵐ[μ] μ[ξ | ℱ (t : ℝ)] :=
  _root_.Prove2MeSourceProof.h_ce2182052ee14161adc2c6b8 isRealQuasimartingale_condExpProcess t
    (tendstoInMeasure_condExpProcess_nhdsGT hξ t)
theorem adapted_condExpModif [ℱ.IsRightContinuous] :
    Adapted (restrictNNReal ℱ) (condExpModif μ ℱ ξ) :=
  adapted_rightContModif isRealQuasimartingale_condExpProcess
/-- **The modification is a martingale for the same filtration.** -/
theorem martingale_condExpModif [ℱ.IsRightContinuous] (hξ : MemLp ξ 2 μ) :
    Martingale (condExpModif μ ℱ ξ) (restrictNNReal ℱ) μ := by
  refine ⟨adapted_condExpModif.stronglyAdapted, fun i j hij => ?_⟩
  have h := martingale_condExpProcess (μ := μ) (ℱ := ℱ) (ξ := ξ) |>.2 i j hij
  calc μ[condExpModif μ ℱ ξ j | restrictNNReal ℱ i]
      =ᵐ[μ] μ[condExpProcess μ ℱ ξ j | restrictNNReal ℱ i] :=
        condExp_congr_ae (condExpModif_ae_eq hξ j)
    _ =ᵐ[μ] condExpProcess μ ℱ ξ i := h
    _ =ᵐ[μ] condExpModif μ ℱ ξ i := (condExpModif_ae_eq hξ i).symm
omit [IsProbabilityMeasure μ] in
/-- Every path of the modification is right-continuous. -/
theorem continuousWithinAt_condExpModif (t : ℝ≥0) (ω : Ω) :
    ContinuousWithinAt (fun s => condExpModif μ ℱ ξ s ω) (Set.Ioi t) t :=
  continuousWithinAt_rightContModif t ω
/-- Almost every path of the modification has left limits everywhere. -/
theorem ae_exists_tendsto_condExpModif_nhdsLT :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, ∃ L : ℝ,
      Tendsto (fun s => condExpModif μ ℱ ξ s ω) (𝓝[<] t) (𝓝 L) := by
  filter_upwards [ae_mem_regularitySetRight (isRealQuasimartingale_condExpProcess (μ := μ)
    (ℱ := ℱ) (ξ := ξ)) countable_denseCountable dense_denseCountable.exists_gt] with ω hω t
  exact ⟨_, tendsto_rightContModif_leftLimWithin (hω t)⟩
end Process

end LevyStochCalc.Probability


