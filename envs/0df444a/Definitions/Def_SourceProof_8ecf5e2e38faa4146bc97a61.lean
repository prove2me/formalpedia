-- Prove2me | Definitions.Def_SourceProof_8ecf5e2e38faa4146bc97a61
-- name    : SourceProof_8ecf5e2e38faa4146bc97a61
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:48:30.846787+00:00
-- url     : https://prove2.me/theorems/1f7837c5-17b9-40e6-8d64-c4b4605989fa
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.tendstoUniformlyOn_leftRiemannSum_rightLimitProcess

import Definitions.Def_SourceProof_33b4740ce8fec4b85a3add51
import Definitions.Def_SourceProof_34709e9a71549d163a00e849
import Definitions.Def_SourceProof_5caa95db89fdd596c2cde105
import Definitions.Def_SourceProof_bf9c1f28ce44b7204ce64183
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.UniformSpace.UniformConvergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The fixed-source-step jump-displacement argument in Protter II.21

Sample the right-limit process of a fixed full source simple integrand. Exact
ceiling-endpoint formulas and right continuity of the integrator give actual
compact-uniform path convergence. Its increment-only limit retains the source
initial correction; it does not assume convergence of the sampled integrands.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} {π : ℕ → StoppingTimePartition F}

theorem _root_.Prove2MeSourceProof.h_8ecf5e2e38faa4146bc97a61 (H : SimplePredictableRep F)
    {ω : Ω} (hπT : Tendsto (fun n ↦ (π n).terminal ω) atTop atTop)
    (hπmesh : Tendsto (fun n ↦ (π n).mesh ω) atTop (𝓝 0))
    (hrX : IsRightContinuousPath (X · ω)) (T : ℝ≥0) :
    TendstoUniformlyOn (fun n t ↦ (π n).leftRiemannSumProcess (rightLimitProcess H.toProcess) X t ω)
      (fun t ↦ H.integralProcess X t ω - H.initial ω * X 0 ω) atTop (Icc 0 T) := by
  classical
  have hm : Tendsto (fun n ↦ ((π n).mesh ω : ℝ)) atTop (𝓝 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp hπmesh
  have hstop (a : ℝ≥0) : TendstoUniformlyOn
      (fun n t ↦ X (min ((π n).path ω |>.ceilingPoint a) t) ω)
      (fun t ↦ X (min a t) ω) atTop (Icc 0 T) :=
    (_root_.Prove2MeSourceProof.h_bf9c1f28ce44b7204ce64183 (hrX a)
      (_root_.Prove2MeSourceProof.h_34709e9a71549d163a00e849
        (fun n ↦ (π n).path ω) a (hπT.eventually (eventually_ge_atTop a)) hm)).tendstoUniformlyOn
  have hcell (i : Fin H.partition.size) : TendstoUniformlyOn
      (fun n t ↦ H.coefficient i ω *
        (X (min ((π n).path ω |>.ceilingPoint (H.partition.point i.succ ω)) t) ω -
          X (min ((π n).path ω |>.ceilingPoint (H.partition.point i.castSucc ω)) t) ω))
      (fun t ↦ H.coefficient i ω *
        (X (min (H.partition.point i.succ ω) t) ω -
          X (min (H.partition.point i.castSucc ω) t) ω)) atTop (Icc 0 T) :=
    Real.uniformContinuous_const_mul.comp_tendstoUniformlyOn
      ((hstop (H.partition.point i.succ ω)).sub (hstop (H.partition.point i.castSucc ω)))
  have hsum (s : Finset (Fin H.partition.size)) : TendstoUniformlyOn
      (fun n t ↦ ∑ i ∈ s, H.coefficient i ω *
        (X (min ((π n).path ω |>.ceilingPoint (H.partition.point i.succ ω)) t) ω -
          X (min ((π n).path ω |>.ceilingPoint (H.partition.point i.castSucc ω)) t) ω))
      (fun t ↦ ∑ i ∈ s, H.coefficient i ω *
        (X (min (H.partition.point i.succ ω) t) ω -
          X (min (H.partition.point i.castSucc ω) t) ω)) atTop (Icc 0 T) := by
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)).tendstoUniformlyOn_const
          (Icc 0 T)
    | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using (hcell i).fun_add ih
  have heq (t : ℝ≥0) : H.integralProcess X t ω - H.initial ω * X 0 ω =
      ∑ i : Fin H.partition.size, H.coefficient i ω *
        (X (min (H.partition.point i.succ ω) t) ω -
          X (min (H.partition.point i.castSucc ω) t) ω) := by
    rw [(_root_.Prove2MeSourceProof.h_5caa95db89fdd596c2cde105 H)]
    ring
  simpa only [(_root_.Prove2MeSourceProof.h_33b4740ce8fec4b85a3add51 H), heq] using hsum Finset.univ
end ProbabilityTheory.SimplePredictableRep


