-- Prove2me | Definitions.Def_MarkovProcess_V3H_Kernel_OnePointKilled_a181fa20
-- name    : MarkovProcess_V3H_Kernel_OnePointKilled_a181fa20
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T08:22:29.625627+00:00
-- url     : https://prove2.me/theorems/c25d9cfe-69d2-4ad0-9153-5952879369b9
-- title:
--   MarkovProcess: MarkovProcess_V3H_Kernel_OnePointKilled_a181fa20
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Feller_Resolvent_4f8c89b8
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointExtension_e4fabfdf
import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointKolmogorov_a805d493
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorKernel_13678038
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0Resolvent_c009f25c
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0SemigroupKernel_c6b9bee0
import Definitions.Def_MarkovProcess_V3H_Killed_Resolvent_b61459c1
import Definitions.Def_MarkovProcess_V3H_Killed_Semigroup_8f8ac7bc
import Definitions.Def_MarkovProcess_V3H_Semigroup_Basic_fec91841
import Definitions.Def_MarkovProcess_V3H_Semigroup_Generation_6c19e644
import Definitions.Def_MarkovProcess_V3H_Semigroup_Resolvent_323559dd
import Definitions.Def_MarkovProcess_V3H_Trajectory_ExitLaw_2add356d
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Killing the one-point process at infinity

This file identifies the continuous process of the one-point extension of a positive
`C₀`-contractive resolvent with the process killed on leaving its live part.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]





variable [LocallyCompactSpace alpha]







end MarkovProcess.SubMarkovKernelSemigroup

namespace MarkovProcess.PositiveC0ContractiveResolvent

open MarkovProcess.SubMarkovKernelSemigroup

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

omit [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
/-- The one-point compactification is compact under the exhaustion metric's topology, since that
topology coincides with the canonical one-point topology (which is always compact). This is a
typeclass-search cache in the same spirit as `OnePoint.instCompleteSpaceOnePointExhaustion`: it
lets the `isCompact_univ` calls that build `CompleteSpace (OnePoint X)` (via
`completeSpace_of_isComplete_univ`) inside this file's `letI` chains resolve automatically. -/
private instance instCompactSpaceOnePointExhaustion
    (rho : X → ℝ) (hrho_cont : Continuous rho) (hrho_pos : ∀ x, 0 < rho x)
    (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x}) :
    @CompactSpace (OnePoint X)
      (OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz
        hrho_compact).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
  rw [OnePoint.exhaustionMetricSpace_toTopologicalSpace]
  infer_instance

/-- The original space is homeomorphic to the live part of its one-point compactification. -/
noncomputable def onePointLiveHomeomorph :
    X ≃ₜ Set.range ((↑) : X → OnePoint X) :=
  OnePoint.isOpenEmbedding_coe.isEmbedding.toHomeomorph

omit [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [BorelSpace X] in
/-- The homeomorphism onto the live part is the coercion into the compactification. -/
@[simp] theorem p2m_embedded_6eea5fb8e11e688a (x : X) :
    (onePointLiveHomeomorph x : OnePoint X) = (x : OnePoint X) := rfl

/-- At a live starting point, the compactified transition law is the original transition law,
pushed into the live part, plus the missing mass at infinity. -/
theorem p2m_embedded_396ad0af3d01b90b
    (R : PositiveC0ContractiveResolvent X) (t : NNReal) (x : X) :
    R.onePointKernelSemigroup t (x : OnePoint X) =
      (R.kernelSemigroup t x).map ((↑) : X → OnePoint X) +
        (1 - R.kernelSemigroup t x Set.univ) • Measure.dirac OnePoint.infty := by
  let : (R.kernelSemigroup t x).Regular := by
    rw [PositiveC0ContractiveResolvent.kernelSemigroup,
      PositiveC0SemigroupKernel.kernelSemigroup_apply,
      PositiveC0OperatorKernel.kernel_apply]
    infer_instance
  let : IsFiniteMeasure (R.kernelSemigroup t x) :=
    ⟨lt_of_le_of_lt (R.kernelSemigroup.measure_univ_le_one t x) ENNReal.one_lt_top⟩
  let : Measure.InnerRegularCompactLTTop
      ((R.kernelSemigroup t x).map ((↑) : X → OnePoint X)) :=
    Measure.InnerRegularCompactLTTop.map_of_continuous OnePoint.continuous_coe
  let : IsFiniteMeasure
      ((R.kernelSemigroup t x).map ((↑) : X → OnePoint X)) := inferInstance
  have hmissing_ne_top : 1 - R.kernelSemigroup t x Set.univ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  let : IsFiniteMeasure
      ((1 - R.kernelSemigroup t x Set.univ) •
        Measure.dirac (OnePoint.infty : OnePoint X)) :=
    Measure.smul_finite _ hmissing_ne_top
  let : IsFiniteMeasure
      ((R.kernelSemigroup t x).map ((↑) : X → OnePoint X) +
        (1 - R.kernelSemigroup t x Set.univ) • Measure.dirac OnePoint.infty) :=
    ⟨(ENNReal.add_lt_top).2 ⟨measure_lt_top _ _, measure_lt_top _ _⟩⟩
  let : (R.onePointKernelSemigroup t (x : OnePoint X)).Regular := by
    rw [onePointKernelSemigroup, PositiveC0ContractiveResolvent.kernelSemigroup,
      PositiveC0SemigroupKernel.kernelSemigroup_apply,
      PositiveC0OperatorKernel.kernel_apply]
    infer_instance
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let g : C₀(OnePoint X, ℝ) :=
    PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f
  have hmain := R.integral_onePointKernelSemigroup t g (x : OnePoint X)
  rw [onePointSemigroup_apply, R.p2m_embedded_58791ce44297e271] at hmain
  have hmap :
      ∫ z, f z ∂(R.kernelSemigroup t x).map ((↑) : X → OnePoint X) =
        ∫ y, f (y : OnePoint X) ∂R.kernelSemigroup t x := by
    simpa only using! integral_map OnePoint.continuous_coe.aemeasurable
      f.continuous.aestronglyMeasurable
  have hmass : R.kernelSemigroup t x Set.univ ≠ ⊤ :=
    (lt_of_le_of_lt (R.kernelSemigroup.measure_univ_le_one t x) ENNReal.one_lt_top).ne
  have hmissing :
      (1 - R.kernelSemigroup t x Set.univ).toReal =
        1 - (R.kernelSemigroup t x).real Set.univ := by
    rw [ENNReal.toReal_sub_of_le (R.kernelSemigroup.measure_univ_le_one t x)
        ENNReal.one_ne_top,
      ENNReal.toReal_one, measureReal_def]
  have hleft : ∫ z, f z ∂R.onePointKernelSemigroup t (x : OnePoint X) =
      ∫ z, g z ∂R.onePointKernelSemigroup t (x : OnePoint X) := by
    apply integral_congr_ae
    filter_upwards with z
    exact (PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply f z).symm
  rw [integral_add_measure]
  · rw [hleft, hmain, hmap, integral_smul_measure, integral_dirac, hmissing, smul_eq_mul]
    congr 2
  · exact f.integrable
  · exact f.integrable











/-- Extend a nonnegative observable on the live space by zero at infinity. -/
def onePointLiveExtension (f : X → ℝ≥0∞) : OnePoint X → ℝ≥0∞ :=
  OnePoint.rec 0 f

omit [MetricSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
/-- The zero extension of a function on the live space agrees with it at live points. -/
@[simp] theorem p2m_embedded_699ca8132c74f39f (f : X → ℝ≥0∞) (x : X) :
    onePointLiveExtension f (x : OnePoint X) = f x := rfl

omit [MetricSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
/-- The zero extension vanishes at the added point. -/
@[simp] theorem p2m_embedded_29f98d148df77df2 (f : X → ℝ≥0∞) :
    onePointLiveExtension f OnePoint.infty = 0 := rfl









end MarkovProcess.PositiveC0ContractiveResolvent


