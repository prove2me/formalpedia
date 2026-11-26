-- Prove2me | Definitions.Def_SourceProof_5fba6145a988c3f8a6970ab9
-- name    : SourceProof_5fba6145a988c3f8a6970ab9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T23:57:00.507384+00:00
-- url     : https://prove2.me/theorems/9a7dd1b9-8355-454b-829f-354b1b05bad0
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.contDiff_comp

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_F000
import Definitions.Def_SourceProof_00a8a291a5ec377d57feab0f
import Definitions.Def_SourceProof_0f1f1b63b3e52165c8596e25
import Definitions.Def_SourceProof_13d74fe230d87debed607218
import Definitions.Def_SourceProof_264b430747bbe6ee020dbafc
import Definitions.Def_SourceProof_2805187910815ebae4f90f84
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_2d0886ee2025f07cabb3dec2
import Definitions.Def_SourceProof_31d0de13ef1656df97c05a7d
import Definitions.Def_SourceProof_44c235d61a2cdcb446e715a4
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_7d09eb6a4e03c1fa37d5b869
import Definitions.Def_SourceProof_8c18053bf585bd3a019ad5a3
import Definitions.Def_SourceProof_91e98637506f1c2c3dd4a09b
import Definitions.Def_SourceProof_9e1a38876e8989b923316eb2
import Definitions.Def_SourceProof_a648f5e42a2456dbcb33c4d9
import Definitions.Def_SourceProof_dff15d58aea8e47b608598ba
import Definitions.Def_SourceProof_f0fd1d672681382caf130496
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Order.Filter.Finite
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.UniformSpace.UniformApproximation

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # C2 transformations preserve general cadlag semimartingales

The residual is adapted and cadlag before semimartingale preservation is
claimed. The proved raw Ito identity identifies that residual with the
actual finite-variation jump series. This supplies its good-integrator
property without assuming nonlinear closure or a classical decomposition.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {f : ℝ → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_5fba6145a988c3f8a6970ab9
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hf : ContDiff ℝ 2 f) :
    IsSemimartingale (fun t ω ↦ f (X t ω)) F P := by
  let hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  let ha₁ : Adapted F (fun t ω ↦ deriv f (X t ω)) :=
    fun t ↦ hd.continuous.measurable.comp ((_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX) t)
  let hr₁ := (_root_.Prove2MeSourceProof.h_264b430747bbe6ee020dbafc (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)) hd.continuous
  let ha₂ : Adapted F (fun t ω ↦ deriv (deriv f) (X t ω)) :=
    fun t ↦ hd.continuous_deriv_one.measurable.comp ((_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX) t)
  let hr₂ := (_root_.Prove2MeSourceProof.h_264b430747bbe6ee020dbafc (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)) hd.continuous_deriv_one
  let J₁ := hX.stochasticIntegral hF
    ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 ha₁) hF hr₁) (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba hr₁)
  let J₂ := (1 / 2 : ℝ) • ((_root_.Prove2MeSourceProof.h_a648f5e42a2456dbcb33c4d9 hX) hF).stochasticIntegral hF
    ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 ha₂) hF hr₂) (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba hr₂)
  have hJ₁ : ProbabilityTheory.IsSemimartingale J₁ F P := (_root_.Prove2MeSourceProof.h_7d09eb6a4e03c1fa37d5b869 hX) hF
    ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 ha₁) hF hr₁) (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba hr₁)
  have hJ₂ : ProbabilityTheory.IsSemimartingale J₂ F P :=
    (_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 ((_root_.Prove2MeSourceProof.h_7d09eb6a4e03c1fa37d5b869 ((_root_.Prove2MeSourceProof.h_a648f5e42a2456dbcb33c4d9 hX) hF)) hF
      ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 ha₂) hF hr₂) (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba hr₂))) (1 / 2)
  let C₀ : ℝ≥0 → Ω → ℝ := fun _ ω ↦ f (X 0 ω)
  have hC : ProbabilityTheory.IsSemimartingale C₀ F P := _root_.Prove2MeSourceProof.h_0f1f1b63b3e52165c8596e25
    (hf.continuous.measurable.comp ((_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX) 0))
  let V : ℝ≥0 → Ω → ℝ := (fun t ω ↦ f (X t ω)) - C₀ - J₁ - J₂
  let R : ℝ≥0 → Ω → ℝ := fun t ω ↦ ∑' s : Ioc 0 t,
    (f (X s ω) - f (ProbabilityTheory.leftLimitProcess X s ω) -
      deriv f (ProbabilityTheory.leftLimitProcess X s ω) * ProbabilityTheory.jumpProcess X s ω -
      deriv (deriv f) (ProbabilityTheory.leftLimitProcess X s ω) / 2 * (ProbabilityTheory.jumpProcess X s ω) ^ 2)
  have hvR : ProbabilityTheory.HasFiniteVariationPaths R P :=
    (_root_.Prove2MeSourceProof.h_91e98637506f1c2c3dd4a09b hX) hF hf
  have he : ProbabilityTheory.Indistinguishable V R P := by
    filter_upwards [(_root_.Prove2MeSourceProof.h_f0fd1d672681382caf130496 hX) hF hf] with ω hω t
    have h := hω t
    change f (X t ω) - f (X 0 ω) = J₁ t ω + J₂ t ω + R t ω at h
    change f (X t ω) - f (X 0 ω) - J₁ t ω - J₂ t ω = R t ω
    linarith only [h]
  have hv : ProbabilityTheory.HasFiniteVariationPaths V P := _root_.Prove2MeSourceProof.h_9e1a38876e8989b923316eb2 (_root_.Prove2MeSourceProof.h_13d74fe230d87debed607218 he) hvR
  have haV : Adapted F V := fun t ↦
    (((hf.continuous.measurable.comp ((_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX) t)).sub ((_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hC) t)).sub
      ((_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hJ₁) t)).sub ((_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hJ₂) t)
  have hrV : ProbabilityTheory.HasCadlagPaths V P :=
    (_root_.Prove2MeSourceProof.h_44c235d61a2cdcb446e715a4 ((_root_.Prove2MeSourceProof.h_44c235d61a2cdcb446e715a4 ((_root_.Prove2MeSourceProof.h_44c235d61a2cdcb446e715a4 ((_root_.Prove2MeSourceProof.h_264b430747bbe6ee020dbafc (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)) hf.continuous)) (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hC)))
      (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hJ₁))) (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hJ₂)
  have hV := (_root_.Prove2MeSourceProof.h_00a8a291a5ec377d57feab0f hv) haV hF hrV
  apply (_root_.Prove2MeSourceProof.h_2805187910815ebae4f90f84 ((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hC) ((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hJ₁) ((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hJ₂) hV)))) _
    (fun t ↦ hf.continuous.measurable.comp ((_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX) t))
  exact ae_of_all _ (fun ω t ↦ by
    change f (X 0 ω) + (J₁ t ω + (J₂ t ω +
      (f (X t ω) - f (X 0 ω) - J₁ t ω - J₂ t ω))) = f (X t ω)
    ring)
end IsSemimartingale

end ProbabilityTheory


