-- Prove2me | Definitions.Def_MarkovProcess_V3H_Trajectory_StoppingLtTop_f2bd051e
-- name    : MarkovProcess_V3H_Trajectory_StoppingLtTop_f2bd051e
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T08:18:34.780506+00:00
-- url     : https://prove2.me/theorems/7fb91aa7-56dc-47e8-9f52-43003989d715
-- title:
--   MarkovProcess: MarkovProcess_V3H_Trajectory_StoppingLtTop_f2bd051e
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
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
# The strong Markov property at a stopping time that may be infinite

Mathlib's stopping times take values in `WithTop ℝ≥0`, so a stopping time of the canonical
filtration on continuous-path space may be infinite, while the strong Markov property of
`MarkovProcess/Main.lean` is stated for finite, `ℝ≥0`-valued stopping times.  This file removes
that restriction on the event `{tau < ⊤}` where the time is finite, writing the finite value as
`(tau omega).untopD 0`:

* `IsFellerKernelSemigroup.continuousProcess_restrict_map_shift_stoppingTime_lt_top`: the
  restart identity, after restricting the law of the process to `A ∩ {tau < ⊤}` for an event `A`
  of the stopped sigma-algebra;
* `IsFellerKernelSemigroup.continuousProcess_condExp_shift_stoppingTime_lt_top`: the same fact
  in conditional-expectation form, for a bounded strongly measurable functional of the shifted
  path, with the indicator of `{tau < ⊤}` on both sides.
* `StoppingTime.lintegral_mul_indicator_of_restrict_map`: integration of a restricted restart
  identity against a nonnegative weight measurable at the conditioning sigma-algebra.

The route is truncation: `truncTime tau K` is the finite stopping time `min tau K`, and the
slices `stoppingTimeSlice A tau K` partition `A ∩ {tau < ⊤}` into countably many events on which
`tau` is finite and bounded by `K`.  On each slice the finite theorems of `Main.lean` apply, and
both sides of the restart identity are countably additive in the restricted measure; the
conditional-expectation form is then obtained from the slicewise restart identity through a
generic indicator bridge, `condExp_indicator_ae_eq_integral_kernel_of_restrict_map`.

Nothing is asserted about the event `{tau = ⊤}`: on it the shifted path is the path itself, and
neither statement constrains it.  No Hunt-process property is claimed.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Function

namespace MarkovProcess

/-! Generic stopping-time material: truncation at a deterministic horizon, the countable slicing
of the event where a `WithTop`-valued stopping time is finite, and the reassembly of restart
identities over the slices.  Nothing here is specific to path space. -/

namespace StoppingTime

section RestrictedRestartIntegral

variable {Omega beta : Type*} {m mOmega : MeasurableSpace Omega}
  {mBeta : MeasurableSpace beta}



end RestrictedRestartIntegral

section Trunc

variable {Omega : Type*} {mOmega : MeasurableSpace Omega}

/-- A `WithTop ℝ≥0`-valued time truncated at the deterministic horizon `K`: the finite,
`ℝ≥0`-valued time equal to `tau omega` when that is at most `K`, and to `K` otherwise. -/
def truncTime (tau : Omega → WithTop NNReal) (K : NNReal) (omega : Omega) : NNReal :=
  (min (tau omega) (K : WithTop NNReal)).untopD 0

/-- The truncated time, read back in `WithTop ℝ≥0`, is the minimum of the time and the
horizon. -/
theorem coe_truncTime (tau : Omega → WithTop NNReal) (K : NNReal) (omega : Omega) :
    ((truncTime tau K omega : NNReal) : WithTop NNReal) = min (tau omega) (K : WithTop NNReal) := by
  have hne : min (tau omega) (K : WithTop NNReal) ≠ ⊤ := by
    intro htop
    have hle := min_le_right (tau omega) (K : WithTop NNReal)
    rw [htop, top_le_iff] at hle
    exact WithTop.coe_ne_top hle
  rw [truncTime]
  lift min (tau omega) (K : WithTop NNReal) to NNReal using hne with a ha
  rw [WithTop.untopD_coe]



/-- The truncation of a stopping time at a deterministic horizon is a finite stopping time. -/
theorem isStoppingTime_truncTime {f : Filtration NNReal mOmega} {tau : Omega → WithTop NNReal}
    (htau : IsStoppingTime f tau) (K : NNReal) :
    IsStoppingTime f (fun omega ↦ ((truncTime tau K omega : NNReal) : WithTop NNReal)) := by
  simp only [coe_truncTime]
  exact htau.min_const K





end Trunc

section Slices

variable {Omega : Type*} {mOmega : MeasurableSpace Omega} {f : Filtration NNReal mOmega}
  {tau : Omega → WithTop NNReal}





/-- The `K`-th slice of an event `A` of the stopped sigma-algebra of `tau`: the part of `A` on
which `tau` is at most `K` but larger than every smaller natural number.  These slices are
pairwise disjoint and exhaust `A ∩ {tau < ⊤}`. -/
def stoppingTimeSlice (A : Set Omega) (tau : Omega → WithTop NNReal) (K : ℕ) : Set Omega :=
  (A ∩ ⋂ j ∈ Set.Iio K, {omega | ((j : NNReal) : WithTop NNReal) < tau omega}) ∩
    {omega | tau omega ≤ ((K : NNReal) : WithTop NNReal)}











end Slices

section Reassembly

variable {Omega beta : Type*} [MeasurableSpace Omega] [MeasurableSpace beta]



end Reassembly

end StoppingTime

open StoppingTime

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]
  [TopologicalSpace.PseudoMetrizableSpace alpha] [SecondCountableTopology alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

omit [TopologicalSpace.PseudoMetrizableSpace alpha] [SecondCountableTopology alpha] in
/-- The untopped value of a stopping time of the canonical filtration is Borel measurable. -/
theorem measurable_untopD_stoppingTime (tau : ContinuousPath alpha → WithTop NNReal)
    (htau : IsStoppingTime (canonicalFiltration (alpha := alpha)) tau) :
    Measurable (fun omega ↦ (tau omega).untopD 0) :=
  htau.measurable'.untopD 0



omit [TopologicalSpace.PseudoMetrizableSpace alpha] [SecondCountableTopology alpha] in
/-- Evaluating a path at the untopped value of a stopping time of the canonical filtration is
Borel measurable. -/
theorem measurable_eval_untopD_stoppingTime (tau : ContinuousPath alpha → WithTop NNReal)
    (htau : IsStoppingTime (canonicalFiltration (alpha := alpha)) tau) :
    Measurable (fun omega : ContinuousPath alpha ↦ omega ((tau omega).untopD 0)) :=
  measurable_eval_of_measurable _ (measurable_untopD_stoppingTime tau htau)



end ContinuousPath

namespace StoppingTime

section Bridge

variable {Omega beta E : Type*} {m : MeasurableSpace Omega}
  {mOmega : MeasurableSpace Omega} {mBeta : MeasurableSpace beta}
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]





end Bridge

end StoppingTime

namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]



end

end SubMarkovKernelSemigroup

end MarkovProcess


