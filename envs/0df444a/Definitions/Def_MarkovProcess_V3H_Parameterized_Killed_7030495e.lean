-- Prove2me | Definitions.Def_MarkovProcess_V3H_Parameterized_Killed_7030495e
-- name    : MarkovProcess_V3H_Parameterized_Killed_7030495e
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T08:21:56.588439+00:00
-- url     : https://prove2.me/theorems/12a5fbed-a12f-4a6c-b923-ba7832450800
-- title:
--   MarkovProcess: MarkovProcess_V3H_Parameterized_Killed_7030495e
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Feller_Semigroup_2cfe612a
import Definitions.Def_MarkovProcess_V3H_Kernel_Basic_264434f5
import Definitions.Def_MarkovProcess_V3H_Killed_Kernel_adff808d
import Definitions.Def_MarkovProcess_V3H_Killed_Semigroup_8f8ac7bc
import Definitions.Def_MarkovProcess_V3H_Lifetime_ExitTime_a7b75085
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcessProperties_61cc1965
import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcess_caf2584d
import Definitions.Def_MarkovProcess_V3H_Parameterized_Semigroup_5f8b28ce
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_ExitTimeShift_63f55a50
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
# The killed parameterized family

For a measurably parameterized family of conservative Feller semigroups and an open set `U`, the
processes of the fibres killed when they leave `U` again form a measurably parameterized family
of sub-Markov kernel semigroups on the carrier `U`: `killedFamily P hP U hU hFeller hK :
ParameterizedSubMarkovKernelSemigroup Theta U`, whose fibre at `theta` is the killed semigroup
`killedSemigroup` of `Killed/Semigroup.lean` for the semigroup at `theta`
(`killedFamily_toSubMarkovKernelSemigroup`, definitionally).  The only new content is the joint
measurability of the killed transition probabilities in the parameter, the time and the starting
point, `measurable_killedKernelOn_family`, which comes from the joint measurability of the
parameterized continuous-path process through the fibre identity.

The killed process on lifetime paths (with a cemetery state) is not constructed here.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovProcess.ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)

/-- The killed transition probabilities of the fibres are jointly measurable in the parameter, the
time and the starting point in `U`. -/
theorem IsConservative.measurable_killedKernelOn_family :
    Measurable fun q : Theta × (NNReal × U) ↦
      SubMarkovKernelSemigroup.IsConservative.killedKernelOn (P.toSubMarkovKernelSemigroup q.1)
        (hP q.1) U hU q.2.1 q.2.2 := by
  refine Measure.measurable_of_measurable_coe _ fun B hB ↦ ?_
  have hB' : MeasurableSet (Subtype.val '' B) :=
    (MeasurableEmbedding.subtype_coe hU.measurableSet).measurableSet_image.mpr hB
  have hfun : (fun q : Theta × (NNReal × U) ↦
      SubMarkovKernelSemigroup.IsConservative.killedKernelOn (P.toSubMarkovKernelSemigroup q.1)
        (hP q.1) U hU q.2.1 q.2.2 B) =
      fun q ↦ IsConservative.continuousProcess P hP (q.1, (q.2.2 : alpha))
        (ContinuousPath.killedEvent U q.2.1 (Subtype.val '' B)) := by
    funext q
    rw [SubMarkovKernelSemigroup.IsConservative.killedKernelOn_apply_eq_continuousProcess _ _ U hU
      _ _ hB, IsConservative.continuousProcess_apply]
  rw [hfun]
  have hg : Measurable fun q : Theta × (NNReal × U) ↦ (q.1, (q.2.2 : alpha)) :=
    measurable_fst.prodMk (measurable_subtype_coe.comp (measurable_snd.comp measurable_snd))
  have heval : Measurable fun p : NNReal × ContinuousPath alpha ↦ p.2 p.1 :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable
  have hS : MeasurableSet {p : (Theta × (NNReal × U)) × ContinuousPath alpha |
      (p.1.2.1 : ℝ≥0∞) < ContinuousPath.exitTime U p.2 ∧ p.2 p.1.2.1 ∈ Subtype.val '' B} := by
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_lt
        (measurable_coe_nnreal_ennreal.comp (measurable_fst.comp (measurable_snd.comp measurable_fst)))
        ((ContinuousPath.measurable_exitTime U hU).comp measurable_snd)
    · exact (heval.comp ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
        measurable_snd)) hB'
  exact Kernel.measurable_kernel_prodMk_left
    (κ := (IsConservative.continuousProcess P hP).comap _ hg) hS

variable [LocallyCompactSpace alpha]

/-- **The killed parameterized family**: the processes of the fibres killed when they leave the
open set `U`, as a measurably parameterized family of sub-Markov kernel semigroups on the carrier
`U`. -/
noncomputable def IsConservative.killedFamily
    (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) : ParameterizedSubMarkovKernelSemigroup Theta U where
  kernel theta t :=
    SubMarkovKernelSemigroup.IsConservative.killedKernelOn (P.toSubMarkovKernelSemigroup theta)
      (hP theta) U hU t
  measurable_kernel := IsConservative.measurable_killedKernelOn_family P hP U hU
  kernel_zero theta :=
    SubMarkovKernelSemigroup.IsConservative.killedKernelOn_zero _ _ U hU (hK theta)
  kernel_add theta :=
    SubMarkovKernelSemigroup.IsConservative.killedKernelOn_add _ _ U hU (hFeller theta) (hK theta)
  isSubMarkovKernel theta t :=
    SubMarkovKernelSemigroup.IsConservative.isSubMarkovKernel_killedKernelOn
      (P.toSubMarkovKernelSemigroup theta) (hP theta) U hU t





end MarkovProcess.ParameterizedSubMarkovKernelSemigroup


