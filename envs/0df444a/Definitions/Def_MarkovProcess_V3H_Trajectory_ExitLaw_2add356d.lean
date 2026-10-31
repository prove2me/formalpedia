-- Prove2me | Definitions.Def_MarkovProcess_V3H_Trajectory_ExitLaw_2add356d
-- name    : MarkovProcess_V3H_Trajectory_ExitLaw_2add356d
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T08:20:52.780989+00:00
-- url     : https://prove2.me/theorems/915f802d-a3ee-4186-a79c-1bb57526ce02
-- title:
--   MarkovProcess: MarkovProcess_V3H_Trajectory_ExitLaw_2add356d
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Lifetime_ExitTime_a7b75085
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_ExitTimeShift_63f55a50
import Definitions.Def_MarkovProcess_V3H_Path_ExitTime_92962b9e
import Definitions.Def_MarkovProcess_V3H_Path_OptionalStopping_4dea182f
import Definitions.Def_MarkovProcess_V3H_Path_RandomShiftMeasurability_fbe17c52
import Definitions.Def_MarkovProcess_V3H_Trajectory_DiscountedDynkin_a0eb8ff0
import Definitions.Def_MarkovProcess_V3H_Trajectory_StoppingLtTop_f2bd051e
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
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
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
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
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Stopped laws and exit distributions

For the continuous-path process `Q` of a conservative semigroup, this file packages as kernels the
laws that the strong Markov property and the boundary value problems of a domain consume:

* `stoppedLaw T hT : Kernel alpha (NNReal × alpha)`, the joint law of a finite stopping time and
  the position at that time, with its two marginals;
* `exitLawTrunc U hU K : Kernel alpha alpha`, the law of the position at the exit time of an open
  set `U` truncated at the horizon `K`; from a starting point in `U` it lives on the closure of `U`
  (`exitLawTrunc_apply_compl_closure`);
* `exitLaw U hU : Kernel alpha alpha`, the exit distribution (harmonic measure): the law of the
  position at the exit time on the event that the path leaves `U`; its total mass is the exit
  probability, and from a starting point in `U` it lives on the frontier of `U`
  (`exitLaw_apply_compl_frontier`).

The harmonic representation of `Trajectory/HarmonicRepresentation.lean` reads, in these terms,
`∫ f d(exitLawTrunc U hU K x) = f x` whenever `L f = 0` on `U`
(`integral_exitLawTrunc_eq_of_generator_eq_zero`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]



variable [MeasurableSpace alpha] [BorelSpace alpha]

/-- The event that a path leaves the open set `U` is measurable. -/
theorem measurableSet_exitTime_lt_top (U : Set alpha) (hU : IsOpen U) :
    MeasurableSet {omega : ContinuousPath alpha | exitTime U omega < ⊤} :=
  measurableSet_lt (measurable_exitTime U hU) measurable_const

/-- The pair of a finite stopping time and the position at that time is measurable. -/
theorem measurable_prodMk_stoppingTime (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal))) :
    Measurable fun omega : ContinuousPath alpha ↦ (T omega, omega (T omega)) :=
  (measurable_of_isStoppingTime T hT).prodMk (measurable_eval_stoppingTime_borel T hT)



end ContinuousPath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable {P : SubMarkovKernelSemigroup alpha} (hP : P.IsConservative)

section StoppedLaw

variable (T : ContinuousPath alpha → NNReal)
  (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
    (fun omega ↦ (T omega : WithTop NNReal)))

/-- The stopped law: the joint law of a finite stopping time and the position at that time, as a
kernel from the starting point. -/
noncomputable def IsConservative.stoppedLaw : Kernel alpha (NNReal × alpha) :=
  Kernel.mapOfMeasurable (IsConservative.continuousProcess P hP)
    (fun omega ↦ (T omega, omega (T omega))) (ContinuousPath.measurable_prodMk_stoppingTime T hT)



/-- The stopped law is a Markov kernel. -/
instance isMarkovKernel_stoppedLaw : IsMarkovKernel (IsConservative.stoppedLaw hP T hT) := by
  rw [IsConservative.stoppedLaw, Kernel.mapOfMeasurable_eq_map]
  exact Kernel.IsMarkovKernel.map _ (ContinuousPath.measurable_prodMk_stoppingTime T hT)





end StoppedLaw

section ExitLaw

variable (U : Set alpha) (hU : IsOpen U)

/-- The law of the position at the exit time of `U` truncated at the horizon `K`. -/
noncomputable def IsConservative.exitLawTrunc (K : NNReal) : Kernel alpha alpha :=
  Kernel.mapOfMeasurable (IsConservative.continuousProcess P hP)
    (fun omega ↦ omega (ContinuousPath.exitTimeTrunc U K omega))
    (ContinuousPath.measurable_eval_stoppingTime_borel _
      (ContinuousPath.isStoppingTime_exitTimeTrunc U hU K))



/-- The truncated exit law is a Markov kernel. -/
instance isMarkovKernel_exitLawTrunc (K : NNReal) :
    IsMarkovKernel (IsConservative.exitLawTrunc hP U hU K) := by
  rw [IsConservative.exitLawTrunc, Kernel.mapOfMeasurable_eq_map]
  exact Kernel.IsMarkovKernel.map _
    (ContinuousPath.measurable_eval_stoppingTime_borel _
      (ContinuousPath.isStoppingTime_exitTimeTrunc U hU K))





/-- The exit distribution (harmonic measure) of `U`: the law of the position at the exit time, on
the event that the path leaves `U`. -/
noncomputable def IsConservative.exitLaw : Kernel alpha alpha :=
  ((IsConservative.continuousProcess P hP).restrict
      (ContinuousPath.measurableSet_exitTime_lt_top U hU)).map
    (fun omega ↦ omega ((ContinuousPath.exitTimeTop U omega).untopD 0))







variable [LocallyCompactSpace alpha]



end ExitLaw

end SubMarkovKernelSemigroup

end MarkovProcess


