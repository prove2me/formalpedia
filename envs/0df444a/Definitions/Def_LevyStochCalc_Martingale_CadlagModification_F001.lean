-- Prove2me | Definitions.Def_LevyStochCalc_Martingale_CadlagModification_F001
-- name    : LevyStochCalc_Martingale_CadlagModification_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:23:23.914088+00:00
-- url     : https://prove2.me/theorems/de5c7e22-8eb5-4a99-9876-57f69cdb3810
-- title:
--   Source declarations: LevyStochCalc.Martingale.CadlagModification
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Martingale.CadlagModification. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_Martingale_F000
import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F001
import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F003
import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F004
import Definitions.Def_SourceProof_74cdf30061d2e4e561a44513

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Càdlàg modifications of real martingales

A real martingale on a right-continuous filtration whose time slices are right-continuous
in measure admits an adapted modification whose paths are almost surely càdlàg. The
modification is the right-limit regularisation along a countable dense set of times
(`ProbabilityTheory.rightContModif`), available for real quasimartingales; a martingale is
a quasimartingale because the elementary integral of a predictable indicator against it has
zero mean.

Two index sets are treated: `ℝ≥0`, where the quasimartingale theory lives (it needs a least
time), and `ℝ`, by restricting to nonnegative times and extending by zero to negative times.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace LevyStochCalc.Martingale

section Modification

variable {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} {ℱ : Filtration ι mΩ}
  {μ : Measure Ω} {X Y : ι → Ω → ℝ}

end Modification

section Quasimartingale

variable {ι Ω : Type*} [LinearOrder ι] {mΩ : MeasurableSpace Ω}
  {𝓕 : Filtration ι mΩ} {μ : Measure Ω} {X : ι → Ω → ℝ}

variable [OrderBot ι]

end Quasimartingale

section NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

end NNReal

section Real

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℝ mΩ} {X : ℝ → Ω → ℝ}

/-- A real martingale on a right-continuous filtration indexed by `ℝ`, right-continuous in
`L²` at every time and vanishing at negative times, has an adapted modification whose paths
are almost surely càdlàg. -/
theorem exists_adapted_ae_cadlag_of_eLpNorm [ℱ.IsRightContinuous] (hX : Martingale X ℱ μ)
    (hrc : ∀ t, Tendsto (fun r => eLpNorm (X r - X t) 2 μ) (𝓝[>] t) (𝓝 0))
    (hneg : ∀ t, t < 0 → X t =ᵐ[μ] 0) :
    ∃ Y : ℝ → Ω → ℝ, Adapted ℱ Y ∧ (∀ t, Y t =ᵐ[μ] X t) ∧
      ∀ᵐ ω ∂μ, ∀ t : ℝ, Tendsto (fun s => Y s ω) (𝓝[>] t) (𝓝 (Y t ω)) ∧
        ∃ L : ℝ, Tendsto (fun s => Y s ω) (𝓝[<] t) (𝓝 L) :=
  _root_.Prove2MeSourceProof.h_74cdf30061d2e4e561a44513 hX (fun t => tendstoInMeasure_of_tendsto_eLpNorm
    (by norm_num) (fun r => (hX.integrable r).aestronglyMeasurable)
    (hX.integrable t).aestronglyMeasurable (hrc t)) hneg
end Real

end LevyStochCalc.Martingale


