-- Prove2me | Definitions.Def_SourceProof_6725b8c29516b8368f82b455
-- name    : SourceProof_6725b8c29516b8368f82b455
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:26:15.349437+00:00
-- url     : https://prove2.me/theorems/2cb68420-047e-5a2f-bd56-39f6b9e0cf0c
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.pathStieltjesIntegral_eq_integralProcess

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegral_F000
import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000
import Definitions.Def_SourceProof_5caa95db89fdd596c2cde105
import Definitions.Def_SourceProof_c1fa16da946ef4c39a6738ca
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite-variation integration on an individual sample path

The integrator need only have finite variation on the particular path being
compared. Caglad pathwise integrability is obtained by the deterministic,
one-point-space specialization of the existing progressive integration theorem.
-/

@[expose] public section

open MeasureTheory StochLean Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X H : ℝ≥0 → Ω → ℝ} {ω : Ω}

namespace SimplePredictableRep
theorem _root_.Prove2MeSourceProof.h_6725b8c29516b8368f82b455
    (R : SimplePredictableRep F) (hv : LocallyBoundedVariationOn (X · ω) univ)
    (hr : IsRightContinuousPath (X · ω)) (T : ℝ≥0) :
    pathStieltjesIntegral (X · ω) hv hr (R.toProcess · ω) T = R.integralProcess X T ω := by
  have h := _root_.Prove2MeSourceProof.h_c1fa16da946ef4c39a6738ca (x := (X · ω)) (hx := hv) (hr := hr)
    (fun i : Fin R.partition.size ↦ R.partition.point i.castSucc ω)
    (fun i : Fin R.partition.size ↦ R.partition.point i.succ ω)
    (fun i ↦ R.coefficient i ω) (fun i ↦ (_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 (R.partition.path ω)) i)
    (R.initial ω) T
  simpa only [ProbabilityTheory.SimplePredictableRep.toProcess, _root_.Prove2MeSourceProof.h_5caa95db89fdd596c2cde105,
    Set.indicator, mem_Ioc] using h
end SimplePredictableRep

end ProbabilityTheory


