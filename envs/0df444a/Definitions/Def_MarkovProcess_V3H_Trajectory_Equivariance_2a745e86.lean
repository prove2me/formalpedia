-- Prove2me | Definitions.Def_MarkovProcess_V3H_Trajectory_Equivariance_2a745e86
-- name    : MarkovProcess_V3H_Trajectory_Equivariance_2a745e86
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T08:18:59.404639+00:00
-- url     : https://prove2.me/theorems/5d6245e2-baca-476b-84d1-623738f91796
-- title:
--   MarkovProcess: MarkovProcess_V3H_Trajectory_Equivariance_2a745e86
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelEquivariance_10113825
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
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
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
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
# Equivariance of the continuous-path process

Let `P` be a conservative Feller sub-Markov kernel semigroup on `alpha` with a Kolmogorov-regular
continuous-path process, let `e : alpha ≃ₜ beta` be a homeomorphism onto a second state space and
`c > 0` a time factor, and let `P'` be the rescaled conjugate of `P` on `beta`, that is
`P' t x = ((P (c * t)) (e.symm x)).map e`.  Then the continuous-path process of `P'` is the
continuous-path process of `P` started at `e.symm x` and pushed forward by the path map
`omega ↦ fun t ↦ e (omega (c * t))`.

The proof goes through the uniqueness theorem of `MarkovProcess/Main.lean`: the pushed-forward
kernel is a Markov kernel whose finite-dimensional distributions are computed from the Feller
marginal theorem for `P` at the rescaled times together with the finite-dimensional transfer
`SubMarkovKernelSemigroup.IsRescaledConjugate.finiteSetKernel_eq`.

Main results: `ContinuousPath.rescale` and its continuity and measurability;
`SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_finiteEvaluation_ordered`,
the marginal of the continuous-path process at an arbitrary strictly increasing finite family of
times; `SubMarkovKernelSemigroup.IsConservative.continuousProcess_eq_map_rescale` and its
pointwise form `continuousProcess_apply_rescale`; the intrinsic form
`continuousProcess_eq_map_rescale_of_hasKolmogorovMoments`, whose only regularity hypothesis is a
Kolmogorov moment bound on `P` when `e` is an isometry; and the two degenerate corollaries, pure
time rescaling (`continuousProcess_eq_map_timeRescale`) and pure conjugation
(`continuousProcess_eq_map_conjugate`).

No scaling limit is asserted: `c` is a fixed positive factor and both semigroups are given in
advance.  The two state spaces may coincide; the degenerate corollaries are stated on one space.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess

namespace ContinuousPath

section Rescale

variable {alpha beta gamma : Type*} [TopologicalSpace alpha] [TopologicalSpace beta]
  [TopologicalSpace gamma]

/-- Multiplication of nonnegative time by a fixed factor, as a continuous self-map of `NNReal`. -/
def timeScaling (c : NNReal) : C(NNReal, NNReal) where
  toFun t := c * t
  continuous_toFun := continuous_const.mul continuous_id

/-- Time scaling, evaluated. -/
@[simp]
theorem p2m_embedded_560a0f3cd8307b61 (c t : NNReal) : timeScaling c t = c * t := rfl

/-- Speed a continuous path up by the factor `c` and conjugate its state by the homeomorphism
`e`. -/
def rescale (e : alpha ≃ₜ beta) (c : NNReal) (omega : ContinuousPath alpha) :
    ContinuousPath beta :=
  (e : C(alpha, beta)).comp (omega.comp (timeScaling c))

/-- The rescaled path, evaluated: `e` applied to the path at the sped-up time. -/
@[simp]
theorem p2m_embedded_f5285285254f4af5 (e : alpha ≃ₜ beta) (c : NNReal) (omega : ContinuousPath alpha)
    (t : NNReal) : rescale e c omega t = e (omega (c * t)) :=
  rfl

/-- Rescaling by the identity homeomorphism and the factor one is the identity. -/
@[simp]
theorem p2m_embedded_7fb650216415eb01 (omega : ContinuousPath alpha) :
    rescale (Homeomorph.refl alpha) 1 omega = omega := by
  ext t
  simp only [_root_.MarkovProcess.ContinuousPath.p2m_embedded_f5285285254f4af5, Homeomorph.refl_apply, id_eq, one_mul]

/-- Rescaling by the identity homeomorphism speeds the path up without touching the state. -/
@[simp]
theorem p2m_embedded_7d59e1b4f3f1cbd9 (c : NNReal) (omega : ContinuousPath alpha) (t : NNReal) :
    rescale (Homeomorph.refl alpha) c omega t = omega (c * t) :=
  rfl

/-- Rescaling by the time factor one conjugates the state without touching the time. -/
@[simp]
theorem p2m_embedded_4bfdf6085a55adfb (e : alpha ≃ₜ beta) (omega : ContinuousPath alpha) (t : NNReal) :
    rescale e 1 omega t = e (omega t) := by
  simp only [_root_.MarkovProcess.ContinuousPath.p2m_embedded_f5285285254f4af5, one_mul]









end Rescale

end ContinuousPath

namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)



section TwoSpaces

variable {beta : Type*} [MetricSpace beta] [CompleteSpace beta]
  [MeasurableSpace beta] [BorelSpace beta] [SecondCountableTopology beta] [Nonempty beta]

variable (P' : SubMarkovKernelSemigroup beta) (hP' : P'.IsConservative)







end TwoSpaces

section OneSpace

variable (P' : SubMarkovKernelSemigroup alpha) (hP' : P'.IsConservative)





end OneSpace

end

end SubMarkovKernelSemigroup

end MarkovProcess


