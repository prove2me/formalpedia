-- Prove2me | Definitions.Def_MarkovProcess_V3H_Path_RelativeHitting_d5970fdd
-- name    : MarkovProcess_V3H_Path_RelativeHitting_d5970fdd
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T08:19:23.452685+00:00
-- url     : https://prove2.me/theorems/25be3bac-650b-41b8-bcbb-a76d40963303
-- title:
--   MarkovProcess: MarkovProcess_V3H_Path_RelativeHitting_d5970fdd
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_ClosedSetDetection_642089d8
import Definitions.Def_MarkovProcess_V3H_Trajectory_StoppingLtTop_f2bd051e
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
# Closed-set detection after a stopping time

This file relativizes closed-set detection to the random compact interval between a stopping
time and a fixed deterministic horizon.  The lower endpoint is truncated at the horizon, so it
is a bounded finite stopping time.  Continuity reduces detection on that interval to its two
endpoints and the fixed enumeration of nonnegative rational times strictly between them.

Public declarations:

* `ContinuousPath.hitsSetBetween`;
* `ContinuousPath.measurableSet_hitsSetBetween`.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess

noncomputable section

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]

/-- The event that a path meets `F` between the stopping time `T` and the fixed horizon `t`. -/
def hitsSetBetween (T : ContinuousPath alpha → ℝ≥0∞) (t : NNReal) (F : Set alpha) :
    Set (ContinuousPath alpha) :=
  {omega | ∃ s : NNReal, T omega ≤ s ∧ s ≤ t ∧ omega s ∈ F}

private def restrictIcc (u t : NNReal) (omega : ContinuousPath alpha) :
    C(Set.Icc u t, alpha) where
  toFun s := omega s
  continuous_toFun := omega.continuous.comp continuous_subtype_val

variable [SecondCountableTopology alpha] [MeasurableSpace alpha] [BorelSpace alpha]



end ContinuousPath

end

end MarkovProcess


