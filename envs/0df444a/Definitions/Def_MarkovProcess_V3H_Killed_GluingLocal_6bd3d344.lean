-- Prove2me | Definitions.Def_MarkovProcess_V3H_Killed_GluingLocal_6bd3d344
-- name    : MarkovProcess_V3H_Killed_GluingLocal_6bd3d344
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T08:23:35.487179+00:00
-- url     : https://prove2.me/theorems/2f168bca-6e08-4b04-ab04-9afc265ac17c
-- title:
--   MarkovProcess: MarkovProcess_V3H_Killed_GluingLocal_6bd3d344
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointExtension_e4fabfdf
import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointKilled_a181fa20
import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointKolmogorov_a805d493
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0Resolvent_c009f25c
import Definitions.Def_MarkovProcess_V3H_Killed_GluingTransfer_c0e8ad8d
import Definitions.Def_MarkovProcess_V3H_Killed_Resolvent_b61459c1
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Semigroup_ContractiveResolvent_4e63c9ca
import Definitions.Def_MarkovProcess_V3H_Semigroup_PositiveShift_fb2cca50
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
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
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
# Comparing two local resolvents through the part-process identity

Two positive `C₀`-contractive resolvents on nested locally compact state spaces are compared here
through the process of the larger one.  The data are an open embedding `iota : X₀ → X₁`, the
regularity data (`PositiveC0ContractiveResolvent.OnePointRegular`) which the continuous-path
process of the compactification of `X₁` is formed from, and the part-process identity: the
resolvent of the process of `X₁` killed at the exit from the image of `X₀` is the resolvent
supplied on `X₀`.

The conclusion (`PositiveC0ContractiveResolvent.kernelResolvent_le_of_partProcess`) is that the
kernel resolvent of the smaller space is dominated by the kernel resolvent of the larger one: a
path leaves the smaller domain no later, so it accumulates less.  The identity is supplied for
nonnegative continuous observables vanishing at infinity, which is the form an analytic
construction produces, and is upgraded to all nonnegative measurable observables through the
potential measures.

The regularity data are an explicit hypothesis: positivity, contractivity and the resolvent
identity do not by themselves give the compactified semigroup a continuous-path process.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace MarkovProcess.PositiveC0ContractiveResolvent

open MarkovProcess.SubMarkovKernelSemigroup

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-- Regularity data for the compactified process of a positive `C₀`-contractive resolvent: a
positive `1`-Lipschitz exhaustion function with compact positive superlevel sets, together with
the Kolmogorov regularity of the compactified kernel semigroup in the metric which that function
determines.  The continuous-path process of the compactified semigroup is formed from exactly
these data. -/
structure OnePointRegular (R : PositiveC0ContractiveResolvent X) where
  /-- The exhaustion function on the live space. -/
  rho : X → ℝ
  /-- The exhaustion function is continuous. -/
  continuous_rho : Continuous rho
  /-- The exhaustion function is positive. -/
  rho_pos : ∀ x, 0 < rho x
  /-- The exhaustion function is `1`-Lipschitz. -/
  lipschitz_rho : LipschitzWith 1 rho
  /-- The positive superlevel sets of the exhaustion function are compact. -/
  isCompact_superlevel : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x}
  /-- The compactified kernel semigroup is Kolmogorov regular in the exhaustion metric. -/
  kolmogorovRegular :
    letI := OnePoint.exhaustionMetricSpace rho continuous_rho rho_pos lipschitz_rho
      isCompact_superlevel
    letI : CompleteSpace (OnePoint X) :=
      completeSpace_of_isComplete_univ isCompact_univ.isComplete
    R.onePointKernelSemigroup.KolmogorovRegular R.isConservative_onePointKernelSemigroup

namespace OnePointRegular

variable {R : PositiveC0ContractiveResolvent X}

set_option warn.classDefReducibility false in
/-- The metric on the compactification determined by the exhaustion function. -/
noncomputable def metricSpace (h : R.OnePointRegular) : MetricSpace (OnePoint X) :=
  OnePoint.exhaustionMetricSpace h.rho h.continuous_rho h.rho_pos h.lipschitz_rho
    h.isCompact_superlevel

/-- Typeclass-search cache: lets `letI := h.metricSpace` discharge an ambient
`CompactSpace (OnePoint X)` obligation without re-deriving compactness at each call site (the
exhaustion metric's topology coincides with the canonical one-point topology, which is always
compact). -/
private instance instCompactSpaceMetricSpace (h : R.OnePointRegular) :
    @CompactSpace (OnePoint X) h.metricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
  unfold OnePointRegular.metricSpace
  rw [OnePoint.exhaustionMetricSpace_toTopologicalSpace]
  infer_instance

/-- Typeclass-search cache, in the same spirit as `instCompactSpaceMetricSpace`: lets
`letI := h.metricSpace` discharge an ambient `BorelSpace (OnePoint X)` obligation. -/
private instance instBorelSpaceMetricSpace (h : R.OnePointRegular) :
    @BorelSpace (OnePoint X) h.metricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      OnePoint.instMeasurableSpace := by
  unfold OnePointRegular.metricSpace
  rw [OnePoint.exhaustionMetricSpace_toTopologicalSpace]
  exact OnePoint.instBorelSpace

/-- Typeclass-search cache, in the same spirit as `instCompactSpaceMetricSpace`: lets
`letI := h.metricSpace` discharge an ambient `SecondCountableTopology (OnePoint X)`
obligation. -/
private instance instSecondCountableTopologyMetricSpace (h : R.OnePointRegular) :
    @SecondCountableTopology (OnePoint X)
      h.metricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
  unfold OnePointRegular.metricSpace
  rw [OnePoint.exhaustionMetricSpace_toTopologicalSpace]
  exact OnePoint.instSecondCountableTopology

/-- The compactification is complete in the exhaustion metric. -/
theorem completeSpace (h : R.OnePointRegular) :
    letI := h.metricSpace
    CompleteSpace (OnePoint X) :=
  letI := h.metricSpace
  completeSpace_of_isComplete_univ isCompact_univ.isComplete



end OnePointRegular



section Embedding

variable {X₀ X₁ : Type*}

/-- The embedding of a smaller live space into the compactification of a larger one. -/
def compactifiedEmbedding (iota : X₀ → X₁) (y : X₀) : OnePoint X₁ := ((iota y : X₁) : OnePoint X₁)

/-- The embedding of a smaller live space into the compactification, unfolded. -/
@[simp] theorem p2m_embedded_8f126fc975442187 (iota : X₀ → X₁) (y : X₀) :
    compactifiedEmbedding iota y = ((iota y : X₁) : OnePoint X₁) := rfl







end Embedding

section EmbeddingTopology

variable {X₀ X₁ : Type*} [TopologicalSpace X₀] [TopologicalSpace X₁]

/-- The embedding of a smaller live space into the compactification of a larger one is an open
embedding. -/
theorem isOpenEmbedding_compactifiedEmbedding {iota : X₀ → X₁} (hiota : IsOpenEmbedding iota) :
    IsOpenEmbedding (compactifiedEmbedding iota) :=
  OnePoint.isOpenEmbedding_coe.comp hiota

/-- The image of a smaller live space in the compactification of a larger one is open. -/
theorem isOpen_range_compactifiedEmbedding {iota : X₀ → X₁} (hiota : IsOpenEmbedding iota) :
    IsOpen (Set.range (compactifiedEmbedding iota)) :=
  (isOpenEmbedding_compactifiedEmbedding hiota).isOpen_range

end EmbeddingTopology

section Comparison

variable {X₀ X₁ : Type*}
  [MetricSpace X₀] [LocallyCompactSpace X₀] [SecondCountableTopology X₀]
  [MeasurableSpace X₀] [BorelSpace X₀]
  [MetricSpace X₁] [LocallyCompactSpace X₁] [SecondCountableTopology X₁]
  [MeasurableSpace X₁] [BorelSpace X₁]

/-- **The part-process identity.**  The resolvent of the compactified process of `R₁`, killed at
the exit from the image of the smaller live space, is the analytic resolvent supplied on that
space, tested on nonnegative observables vanishing at infinity and extended by zero off the
image. -/
def IsPartProcess (R₀ : PositiveC0ContractiveResolvent X₀)
    (R₁ : PositiveC0ContractiveResolvent X₁) (h₁ : R₁.OnePointRegular)
    {iota : X₀ → X₁} (hiota : IsOpenEmbedding iota) : Prop :=
  ∀ (mu : Semigroup.PositiveShift) (f : C₀(X₀, ℝ)), (∀ z, 0 ≤ f z) → ∀ y : X₀,
    letI := h₁.metricSpace
    letI := h₁.completeSpace
    IsConservative.killedResolvent R₁.onePointKernelSemigroup
        R₁.isConservative_onePointKernelSemigroup
        (Set.range (compactifiedEmbedding iota))
        (isOpen_range_compactifiedEmbedding hiota) (mu : ℝ)
        (Function.extend (compactifiedEmbedding iota) (fun z ↦ ENNReal.ofReal (f z)) 0)
        (compactifiedEmbedding iota y) =
      ENNReal.ofReal (R₀.toContractiveResolvent.operator mu f y)



end Comparison

end MarkovProcess.PositiveC0ContractiveResolvent


