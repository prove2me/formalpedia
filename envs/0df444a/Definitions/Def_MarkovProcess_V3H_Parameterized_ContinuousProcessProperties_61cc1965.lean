-- Prove2me | Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcessProperties_61cc1965
-- name    : MarkovProcess_V3H_Parameterized_ContinuousProcessProperties_61cc1965
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T08:20:40.164684+00:00
-- url     : https://prove2.me/theorems/bbdcb2fe-4619-4c17-9196-2bfa9d9d2039
-- title:
--   MarkovProcess: MarkovProcess_V3H_Parameterized_ContinuousProcessProperties_61cc1965
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcess_caf2584d
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_RandomShiftMeasurability_fbe17c52
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
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
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
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
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Properties of the parameterized continuous-path process

Every property of the continuous-path process of a single semigroup, as exposed in
`MarkovProcess/Main.lean`, restated for the measurably parameterized process
`ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess P hP` at a point
`(theta, x)` of the parameter-and-state space.  The hypotheses are the fibrewise ones: fibrewise
conservativity `hP`, fibrewise Feller property `hFeller` where the single-semigroup statement needs
it, and fibrewise Kolmogorov regularity `hK`.

Every proof is a transport through the exact fibre identity
`IsConservative.continuousProcess_apply`; consumers never need that identity themselves.  The
restarted kernels are written as the parameterized kernel composed with the map
`omega ↦ (theta, omega (T omega))`, so that the parameter is carried along the restart.

Main statements: `continuousProcess_map_eval`, `continuousProcess_map_eval_zero` (and its kernel
form `continuousProcess_map_eval_zero'`), `continuousProcess_map_finiteEvaluation`,
`continuousProcess_map_finiteEvaluation_denseTime`, `continuousProcess_map_shift`,
`continuousProcess_restrict_map_shift`, `continuousProcess_restrict_map_shift_stoppingTime`,
`continuousProcess_condExp_shift`, `continuousProcess_condExp_shift_stoppingTime`,
`continuousProcess_condExp_shift_countableStoppingTime`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]



end ContinuousPath

namespace ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)

section Fibre



omit [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha] in
/-- The map `omega ↦ (theta, omega s)` carrying the parameter along the state at time `s` is
measurable. -/
theorem measurable_prodMk_coordinateProcess (theta : Theta) (s : NNReal) :
    Measurable (fun omega : ContinuousPath alpha ↦ (theta, omega s)) :=
  measurable_const.prodMk (ContinuousPath.measurable_coordinateProcess (alpha := alpha) s)

omit [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha] in
/-- The map `omega ↦ (theta, omega (T omega))` carrying the parameter along the state at a finite
stopping time `T` is measurable. -/
theorem measurable_prodMk_eval_stoppingTime (theta : Theta) (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal))) :
    Measurable (fun omega : ContinuousPath alpha ↦ (theta, omega (T omega))) :=
  measurable_const.prodMk (ContinuousPath.measurable_eval_stoppingTime_borel T hT)

end Fibre

section Marginals









variable [LocallyCompactSpace alpha]
  (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)

include hFeller









variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]







end Marginals

end ParameterizedSubMarkovKernelSemigroup

end MarkovProcess


