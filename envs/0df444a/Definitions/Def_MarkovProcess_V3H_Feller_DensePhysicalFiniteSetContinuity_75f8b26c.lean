-- Prove2me | Definitions.Def_MarkovProcess_V3H_Feller_DensePhysicalFiniteSetContinuity_75f8b26c
-- name    : MarkovProcess_V3H_Feller_DensePhysicalFiniteSetContinuity_75f8b26c
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T08:01:52.652398+00:00
-- url     : https://prove2.me/theorems/024bd1a2-981a-491d-ab00-9b2f74a05378
-- title:
--   MarkovProcess: MarkovProcess_V3H_Feller_DensePhysicalFiniteSetContinuity_75f8b26c
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_PhysicalCompactTestTransport_e18ed42b
import Definitions.Def_MarkovProcess_V3H_DenseTime_PhysicalReindex_4ed652de
import Definitions.Def_MarkovProcess_V3H_Feller_FiniteSetCompactTestContinuity_012434c8
import Definitions.Def_MarkovProcess_V3H_Feller_Semigroup_2cfe612a
import Definitions.Def_MarkovProcess_V3H_FiniteTime_ProjectiveFamily_1eff0efa
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMeasure_354455bb
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Definitions.Def_MarkovProcess_V3H_Trajectory_FiniteMarginals_a8fbfae5
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Compact-test bounds for finite dense-time laws

Compact-test integrals against a physically indexed finite-set kernel, reindexed by dense-time
labels, are continuous in the starting point. Conservativity also gives a uniform norm bound by
the `C₀` norm of the test. Both statements include the empty coordinate set.

This is finite-dimensional analytic infrastructure; no statement about path space is proved
here.  The continuous-path process is built in `Trajectory/`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal CompactlySupported ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

section Continuity

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

/-- A compact-test integral against a finite dense-time law is continuous in the starting
point. -/
theorem IsFellerKernelSemigroup.continuous_integral_map_finiteSetKernel_pullbackPhysicalSet
    {P : SubMarkovKernelSemigroup alpha} (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (J : Finset DenseTime) (f : C_c(J → alpha, ℝ)) :
    Continuous fun y ↦ ∫ z, f z ∂
      (finiteSetKernel P (denseTimePhysicalSet J)).map
        (DenseTimePath.pullbackPhysicalSet J) y := by
  have h := hFeller.continuous_integral_compactlySupported_finiteSetKernel hP
    (denseTimePhysicalSet J) (DenseTimePath.pullbackPhysicalSetCompactTest J f)
  simpa only [DenseTimePath.integral_map_finiteSetKernel_pullbackPhysicalSet P J f] using h

end Continuity

section Bound

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]

/-- A compact-test integral against a conservative finite dense-time law is bounded by the
test's canonical `C₀` norm. -/
theorem IsConservative.p2m_embedded_e32d42236a59802b
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsConservative)
    (J : Finset DenseTime) (f : C_c(J → alpha, ℝ)) (y : alpha) :
    ‖∫ z, f z ∂(finiteSetKernel P (denseTimePhysicalSet J)).map
        (DenseTimePath.pullbackPhysicalSet J) y‖ ≤
      ‖PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f‖ := by
  let K := (finiteSetKernel P (denseTimePhysicalSet J)).map
    (DenseTimePath.pullbackPhysicalSet J)
  let : IsMarkovKernel K := by
    let : IsMarkovKernel (finiteSetKernel P (denseTimePhysicalSet J)) :=
      hP.isMarkovKernel_finiteSetKernel P (denseTimePhysicalSet J)
    exact Kernel.IsMarkovKernel.map _ (DenseTimePath.measurable_pullbackPhysicalSet J)
  let : IsProbabilityMeasure (K y) := IsMarkovKernel.isProbabilityMeasure y
  let f₀ : C₀(J → alpha, ℝ) :=
    PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f
  change ‖∫ z, f z ∂K y‖ ≤ ‖f₀‖
  calc
    ‖∫ z, f z ∂K y‖ ≤ ‖f₀‖ * (K y).real Set.univ :=
      MeasureTheory.norm_integral_le_of_norm_le_const
        (ae_of_all _ fun z ↦ by
          simpa only [f₀,
            PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply] using!
            f₀.toBCF.norm_coe_le_norm z)
    _ = ‖f₀‖ := by
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one]

end Bound

end MarkovProcess.SubMarkovKernelSemigroup


