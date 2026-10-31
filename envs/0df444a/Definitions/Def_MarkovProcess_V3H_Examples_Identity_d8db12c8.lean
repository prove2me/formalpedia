-- Prove2me | Definitions.Def_MarkovProcess_V3H_Examples_Identity_d8db12c8
-- name    : MarkovProcess_V3H_Examples_Identity_d8db12c8
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T08:17:56.121988+00:00
-- url     : https://prove2.me/theorems/504ddbdf-ce7f-44fc-a5a3-02f37061bef9
-- title:
--   MarkovProcess: MarkovProcess_V3H_Examples_Identity_d8db12c8
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_Basic_264434f5
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
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
# The identity semigroup and its continuous-path process

The transition semigroup that never moves: `idSemigroup t = Kernel.id` at every time.  It is
conservative, Feller, and satisfies the Kolmogorov moment criterion with exponents `p = 1`,
`q = 2` and constant `M = 0`, so the existence-and-uniqueness theorem of `MarkovProcess.Main`
applies to it verbatim.  The resulting process is identified: from every starting point `x` its
law is the Dirac mass at the constant path at `x`.

This file witnesses that the hypotheses of the main theorem are jointly satisfiable; it proves
nothing about any other semigroup, and it makes no claim about a semigroup that actually moves
(see `MarkovProcess.Examples.Drift` for that).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

noncomputable section

section Definition

variable {alpha : Type*} [MeasurableSpace alpha]

/-- The identity kernel semigroup: the transition kernel at every time is the identity kernel,
so the associated process never moves. -/
def idSemigroup : SubMarkovKernelSemigroup alpha where
  kernel := fun _ ↦ Kernel.id
  measurable_kernel := (Kernel.id : Kernel alpha alpha).measurable.comp measurable_snd
  kernel_zero := rfl
  kernel_add := fun _ _ ↦ (Kernel.id_comp Kernel.id).symm
  isSubMarkovKernel := fun _ ↦ IsSubMarkovKernel.id

/-- Every transition measure of the identity semigroup is the Dirac mass at the starting
point. -/
theorem idSemigroup_apply (t : NNReal) (x : alpha) :
    (idSemigroup (alpha := alpha)) t x = Measure.dirac x := rfl

/-- The identity semigroup is conservative: every transition measure has total mass one. -/
theorem isConservative_idSemigroup :
    (idSemigroup (alpha := alpha)).IsConservative := by
  intro t x
  rw [idSemigroup_apply t x]
  exact measure_univ

end Definition

section Feller

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]





variable [LocallyCompactSpace alpha]



end Feller

section Moments

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]



end Moments

section Process

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [Nonempty alpha]









end Process

end

end MarkovProcess


