-- Prove2me | Definitions.Def_SourceProof_f0fd1d672681382caf130496
-- name    : SourceProof_f0fd1d672681382caf130496
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T23:40:29.741052+00:00
-- url     : https://prove2.me/theorems/e3f9e103-7a64-51a1-9295-cfd08cc827b0
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.ito_raw_bracket

import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F002
import Definitions.Def_StochLean_Probability_Process_Partition_TaylorSums_F000
import Definitions.Def_SourceProof_1656998222a6439ea1baa6b7
import Definitions.Def_SourceProof_1cce7685e72bf317570bfd3c
import Definitions.Def_SourceProof_215f6d5e6b10999a8c8f10ba
import Definitions.Def_SourceProof_24278e78a60501166c68bfc8
import Definitions.Def_SourceProof_264b430747bbe6ee020dbafc
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_2d0886ee2025f07cabb3dec2
import Definitions.Def_SourceProof_36da4c661fc115cbdc2bfff4
import Definitions.Def_SourceProof_5922ecc268414b6fc6aec126
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_60fbb0806e5cb393cb74e054
import Definitions.Def_SourceProof_6ec6ed103d98506e37900b2a
import Definitions.Def_SourceProof_87f0a7a067d30089e512c6db
import Definitions.Def_SourceProof_a648f5e42a2456dbcb33c4d9
import Definitions.Def_SourceProof_dff15d58aea8e47b608598ba
import Definitions.Def_SourceProof_f9b9945a35d8fec22e63e77b
import Definitions.Def_SourceProof_ff07642989734d14cb2ac8eb
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Order.Filter.Finite
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # General cadlag Ito identity with the original raw quadratic variation

This is the equivalent raw-bracket form in Protter II.32's proof. Its
absolutely summable jump correction subtracts both first- and second-order
terms. The identity is on one event for all finite times and retains the
source initial convention through zero-starting left-limit integrands.
-/

@[expose] public section

open MeasureTheory Filter Set StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {f : ℝ → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_f0fd1d672681382caf130496
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hf : ContDiff ℝ 2 f) :
    let hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
    let ha₁ : Adapted F (fun t ω ↦ deriv f (X t ω)) :=
      fun t ↦ hd.continuous.measurable.comp ((_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX) t)
    let hr₁ := (_root_.Prove2MeSourceProof.h_264b430747bbe6ee020dbafc (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)) hd.continuous
    let ha₂ : Adapted F (fun t ω ↦ deriv (deriv f) (X t ω)) :=
      fun t ↦ hd.continuous_deriv_one.measurable.comp ((_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX) t)
    let hr₂ := (_root_.Prove2MeSourceProof.h_264b430747bbe6ee020dbafc (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)) hd.continuous_deriv_one
    Indistinguishable (fun t ω ↦ f (X t ω) - f (X 0 ω))
      (fun t ω ↦ hX.stochasticIntegral hF ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 ha₁) hF hr₁)
          (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba hr₁) t ω +
        (1 / 2 : ℝ) * ((_root_.Prove2MeSourceProof.h_a648f5e42a2456dbcb33c4d9 hX) hF).stochasticIntegral hF
          ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 ha₂) hF hr₂) (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba hr₂) t ω +
        ∑' s : Ioc 0 t, (f (X s ω) - f (leftLimitProcess X s ω) -
          deriv f (leftLimitProcess X s ω) * jumpProcess X s ω -
          deriv (deriv f) (leftLimitProcess X s ω) / 2 * (jumpProcess X s ω) ^ 2)) P := by
  dsimp only
  let hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  let ha₁ : Adapted F (fun t ω ↦ deriv f (X t ω)) :=
    fun t ↦ hd.continuous.measurable.comp ((_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX) t)
  let hr₁ := (_root_.Prove2MeSourceProof.h_264b430747bbe6ee020dbafc (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)) hd.continuous
  let ha₂ : Adapted F (fun t ω ↦ deriv (deriv f) (X t ω)) :=
    fun t ↦ hd.continuous_deriv_one.measurable.comp ((_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX) t)
  let hr₂ := (_root_.Prove2MeSourceProof.h_264b430747bbe6ee020dbafc (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)) hd.continuous_deriv_one
  let π : ℕ → ProbabilityTheory.StoppingTimePartition F := fun n ↦ ProbabilityTheory.StoppingTimePartition.deterministic F
    ((StochLean.LocallyFinitePartition.dyadic n).restrict (n : ℝ≥0))
  have hπ : ProbabilityTheory.StoppingTimePartition.IsTendingToIdentity π P :=
    _root_.Prove2MeSourceProof.h_6ec6ed103d98506e37900b2a
      _root_.Prove2MeSourceProof.h_36da4c661fc115cbdc2bfff4 tendsto_natCast_atTop_atTop
  have h₁ := (_root_.Prove2MeSourceProof.h_5922ecc268414b6fc6aec126 hX) hF ha₁ hr₁ hπ
  have h₂ := (_root_.Prove2MeSourceProof.h_f9b9945a35d8fec22e63e77b hX) hF ha₂ hr₂ hπ
  have hu := (_root_.Prove2MeSourceProof.h_ff07642989734d14cb2ac8eb ((_root_.Prove2MeSourceProof.h_ff07642989734d14cb2ac8eb ((_root_.Prove2MeSourceProof.h_ff07642989734d14cb2ac8eb ((_root_.Prove2MeSourceProof.h_215f6d5e6b10999a8c8f10ba hπ) (fun t ω ↦ f (X t ω))))
    (_root_.Prove2MeSourceProof.h_60fbb0806e5cb393cb74e054 atTop (fun _ ω ↦ f (X 0 ω))))) h₁)) ((_root_.Prove2MeSourceProof.h_24278e78a60501166c68bfc8 h₂) (1 / 2 : ℝ))
  have he := (_root_.Prove2MeSourceProof.h_1cce7685e72bf317570bfd3c hX) hF hf hπ
    ((_root_.Prove2MeSourceProof.h_87f0a7a067d30089e512c6db hu) (fun n ↦ ae_of_all _ (fun ω t ↦ by
      rw [(_root_.Prove2MeSourceProof.h_1656998222a6439ea1baa6b7 (π n))]
      rfl)))
  filter_upwards [he] with ω hω t
  have h := hω t
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
  linarith only [h]
end IsSemimartingale

end ProbabilityTheory


