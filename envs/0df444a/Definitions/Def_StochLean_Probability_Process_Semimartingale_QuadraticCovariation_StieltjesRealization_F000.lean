-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticCovariation_StieltjesRealization_F000
-- name    : StochLean_Probability_Process_Semimartingale_QuadraticCovariation_StieltjesRealization_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:14:02.200884+00:00
-- url     : https://prove2.me/theorems/065e73df-88fb-51a7-aeab-7cfc62fdf9af
-- title:
--   StochLean: Probability.Process.Semimartingale.QuadraticCovariation.StieltjesRealization F000

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticCovariation_F000
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.Instances.Real.Lemmas

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurable Stieltjes realizations of the canonical raw brackets

These are null-event versions of the already constructed brackets, not another
definition of stochastic quadratic variation. All three path identifications
are indistinguishability statements. Their canonical variation/energy integrals
will therefore have measurable random versions without assumptions on moments.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

structure SemimartingaleBracketRealization
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) where
  mixed : ℝ≥0 → Ω → ℝ
  mixed_adapted : Adapted F mixed
  mixed_bv : ∀ ω, LocallyBoundedVariationOn (fun t ↦ mixed t ω) univ
  mixed_rc : ∀ ω, IsRightContinuousPath (fun t ↦ mixed t ω)
  mixed_eq : Indistinguishable (hX.quadraticCovariation hY hF) mixed P
  left : Ω → StieltjesFunction ℝ≥0
  right : Ω → StieltjesFunction ℝ≥0
  left_adapted : Adapted F (fun t ω ↦ left ω t)
  right_adapted : Adapted F (fun t ω ↦ right ω t)
  left_eq : Indistinguishable (hX.quadraticVariation hF) (fun t ω ↦ left ω t) P
  right_eq : Indistinguishable (hY.quadraticVariation hF) (fun t ω ↦ right ω t) P
namespace SemimartingaleBracketRealization

variable {hX : IsSemimartingale X F P} {hY : IsSemimartingale Y F P} {hF : F.IsUsual P}
  (D : SemimartingaleBracketRealization hX hY hF)

end SemimartingaleBracketRealization

end ProbabilityTheory


