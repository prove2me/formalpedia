-- Prove2me | Definitions.Def_SourceProof_ee4e1738437f392088834bc8
-- name    : SourceProof_ee4e1738437f392088834bc8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:41:47.682819+00:00
-- url     : https://prove2.me/theorems/1c3d2ebe-3bca-5c9d-a9e6-18e72f90023d
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.tendstoUniformlyOn_integralProcess

import Definitions.Def_SourceProof_5caa95db89fdd596c2cde105
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.LocalProperty
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Ring.Real

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Continuity in the integrator for a fixed elementary integrand

Only finitely many stopped increments are involved. No semimartingale premise
on the integrators, coefficient bound, or coefficient integrability is used.
This does not assert continuity in a varying integrator for general integrands.
-/

@[expose] public section

open MeasureTheory Filter Set Finset
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℕ → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}

namespace SimplePredictableRep
theorem _root_.Prove2MeSourceProof.h_ee4e1738437f392088834bc8
    (H : SimplePredictableRep F) {T : ℝ≥0} {ω : Ω}
    (hu : TendstoUniformlyOn (fun n t ↦ X n t ω) (fun t ↦ Y t ω) atTop (Icc 0 T)) :
    TendstoUniformlyOn (fun n t ↦ H.integralProcess (X n) t ω)
      (fun t ↦ H.integralProcess Y t ω) atTop (Icc 0 T) := by
  classical
  have hstop (a : ℝ≥0) : TendstoUniformlyOn (fun n t ↦ X n (min a t) ω)
      (fun t ↦ Y (min a t) ω) atTop (Icc 0 T) :=
    (hu.comp (fun t ↦ min a t)).mono (fun t ht ↦ ⟨bot_le, (min_le_right a t).trans ht.2⟩)
  have hcell (i : Fin H.partition.size) : TendstoUniformlyOn
      (fun n t ↦ H.coefficient i ω *
        (X n (min (H.partition.point i.succ ω) t) ω -
          X n (min (H.partition.point i.castSucc ω) t) ω))
      (fun t ↦ H.coefficient i ω *
        (Y (min (H.partition.point i.succ ω) t) ω -
          Y (min (H.partition.point i.castSucc ω) t) ω)) atTop (Icc 0 T) :=
    Real.uniformContinuous_const_mul.comp_tendstoUniformlyOn
      ((hstop (H.partition.point i.succ ω)).sub (hstop (H.partition.point i.castSucc ω)))
  have hsum (s : Finset (Fin H.partition.size)) : TendstoUniformlyOn
      (fun n t ↦ ∑ i ∈ s, H.coefficient i ω *
        (X n (min (H.partition.point i.succ ω) t) ω -
          X n (min (H.partition.point i.castSucc ω) t) ω))
      (fun t ↦ ∑ i ∈ s, H.coefficient i ω *
        (Y (min (H.partition.point i.succ ω) t) ω -
          Y (min (H.partition.point i.castSucc ω) t) ω)) atTop (Icc 0 T) := by
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)).tendstoUniformlyOn_const
          (Icc 0 T)
    | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using (hcell i).fun_add ih
  have hinit := ((hu.tendsto_at (show (0 : ℝ≥0) ∈ Icc 0 T from ⟨le_rfl, bot_le⟩)).const_mul
    (H.initial ω)).tendstoUniformlyOn_const (s := Icc 0 T)
  simpa only [(_root_.Prove2MeSourceProof.h_5caa95db89fdd596c2cde105 H)] using hinit.fun_add (hsum Finset.univ)
end SimplePredictableRep

end ProbabilityTheory


