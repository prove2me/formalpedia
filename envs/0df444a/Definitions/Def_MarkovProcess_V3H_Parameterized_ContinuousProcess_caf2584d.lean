-- Prove2me | Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcess_caf2584d
-- name    : MarkovProcess_V3H_Parameterized_ContinuousProcess_caf2584d
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T08:18:32.602645+00:00
-- url     : https://prove2.me/theorems/cb43d0ec-ef42-4423-b184-9c79dc316e75
-- title:
--   MarkovProcess: MarkovProcess_V3H_Parameterized_ContinuousProcess_caf2584d
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousLaw_cc004751
import Definitions.Def_MarkovProcess_V3H_DenseTime_PrefixKernel_a192bbea
import Definitions.Def_MarkovProcess_V3H_DenseTime_Trajectory_b0f7f66f
import Definitions.Def_MarkovProcess_V3H_FiniteTime_MeasureFiniteRestrictionIdentification_470add42
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Kernel_KolmogorovMoments_9b991370
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Parameterized_DenseTimePrefixKernel_12387c59
import Definitions.Def_MarkovProcess_V3H_Parameterized_DenseTimeTrajectory_d8dd1c30
import Definitions.Def_MarkovProcess_V3H_Parameterized_Semigroup_5f8b28ce
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_Polish_87f91693
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Definitions.Def_MarkovProcess_V3H_Trajectory_Basic_34bd0835
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
# The continuous-path process of a measurably parameterized semigroup

For a jointly measurable family of sub-Markov kernel semigroups indexed by a measurable parameter
space `Theta`, this file constructs the quenched continuous-path process as a single kernel
`Kernel (Theta × alpha) (ContinuousPath alpha)`: joint measurability in the parameter and the
starting state is carried by the kernel structure, not proved parameter by parameter afterwards.

The construction transports the jointly measurable dense-time trajectory
`parameterizedDenseTimeTrajectory` through the same measurable continuous-extension map that the
unparameterized `continuousProcess` uses, with the same fallback path.  The central result is the
fibre identity: at every parameter and every starting point the parameterized process is
*literally* the unparameterized process of that parameter's semigroup, with no null set and no
regularity hypothesis.  It rests on the corresponding dense-time fibre identity, which is proved
here from the finite enumeration-prefix marginals of the two trajectory kernels.

Fibrewise conservativity, Kolmogorov regularity and Kolmogorov moment bounds are named as
predicates on the parameterized family, so that consumers state hypotheses once.

No Markov, strong Markov, Feller, equivariance, annealed or killed statement is proved here; each
of those is a separate transport through the fibre identity.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

noncomputable section

section Conservativity

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]

/-- Fibrewise conservativity of a measurably parameterized sub-Markov kernel semigroup: every
parameter slice is a conservative sub-Markov kernel semigroup, so that no mass is lost at any
time from any state for any parameter. -/
def IsConservative (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) : Prop :=
  ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative

end Conservativity

section Moments

variable {Theta alpha : Type*} [MeasurableSpace Theta] [PseudoEMetricSpace alpha]
  [MeasurableSpace alpha]

/-- Fibrewise Kolmogorov moment bounds with parameter-independent constants: every parameter slice
satisfies the intrinsic displacement estimate `∫ edist z y ^ p ∂(P theta h y) ≤ M * h ^ q`, with
the same exponents `p`, `q` and the same constant `M` for every parameter. -/
def HasKolmogorovMoments (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (p q : ℝ) (M : ℝ≥0) : Prop :=
  ∀ theta, (P.toSubMarkovKernelSemigroup theta).HasKolmogorovMoments p q M

end Moments

section DenseTimeFibre

variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

omit [StandardBorelSpace alpha] [Nonempty alpha] in
/-- Two finite measures on a countable product path space that agree on every finite
enumeration prefix agree.  Every finite coordinate set is contained in a long enough prefix,
so the prefix marginals already determine all finite-coordinate marginals. -/
private theorem measure_eq_of_map_denseTimeTrajectoryPrefix_eq (e : ℕ ≃ D)
    (mu nu : Measure (D → alpha)) [IsFiniteMeasure mu]
    (h : ∀ n : ℕ,
      mu.map (SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectoryPrefix e n) =
        nu.map (SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectoryPrefix e n)) :
    mu = nu := by
  refine _root_.MarkovProcess.Measure.p2m_embedded_b1456b20928f753b mu nu fun I ↦ ?_
  obtain ⟨n, hlt⟩ : ∃ n : ℕ, ∀ d ∈ I, e.symm d < n :=
    ⟨I.sup fun d ↦ e.symm d + 1,
      fun d hd ↦ Nat.lt_of_succ_le (Finset.le_sup (f := fun d ↦ e.symm d + 1) hd)⟩
  have hprefix : Measurable
      (SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectoryPrefix (α := alpha) e n) :=
    SubMarkovKernelSemigroup.IsConservative.measurable_denseTimeTrajectoryPrefix e n
  have hg : Measurable
      (fun z : Fin n → alpha ↦ fun d : I ↦ z ⟨e.symm (d : D), hlt (d : D) d.2⟩) := by
    rw [measurable_pi_iff]
    intro d
    exact measurable_pi_apply _
  have hfun :
      (fun z : Fin n → alpha ↦ fun d : I ↦ z ⟨e.symm (d : D), hlt (d : D) d.2⟩) ∘
          SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectoryPrefix (α := alpha) e n =
        I.restrict := by
    funext path d
    change path (e (e.symm (d : D))) = path (d : D)
    rw [e.apply_symm_apply]
  rw [← hfun, ← Measure.map_map hg hprefix, ← Measure.map_map hg hprefix, h n]

/-- **Dense-time fibre identity.**  At every parameter and every starting state, the jointly
measurable parameterized dense-time trajectory is the dense-time trajectory of that parameter's
semigroup.  Both kernels are Markov with the same finite enumeration-prefix marginals. -/
theorem p2m_embedded_6c61c679d0514bbd
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (theta : Theta) (x : alpha) :
    P.parameterizedDenseTimeTrajectory hP e iota (theta, x) =
      SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectory
        (P.toSubMarkovKernelSemigroup theta) (hP theta) e iota x := by
  let : IsMarkovKernel (P.parameterizedDenseTimeTrajectory hP e iota) :=
    P.isMarkovKernel_parameterizedDenseTimeTrajectory hP e iota
  refine measure_eq_of_map_denseTimeTrajectoryPrefix_eq e _ _ fun n ↦ ?_
  have hprefix : Measurable
      (SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectoryPrefix (α := alpha) e n) :=
    SubMarkovKernelSemigroup.IsConservative.measurable_denseTimeTrajectoryPrefix e n
  rw [← Kernel.map_apply _ hprefix, ← Kernel.map_apply _ hprefix,
    P.p2m_embedded_c425cb990d127140 hP e iota n,
    SubMarkovKernelSemigroup.IsConservative.denseTimeTrajectory_map_prefix
      (P.toSubMarkovKernelSemigroup theta) (hP theta) e iota n,
    P.parameterizedDenseTimePrefixKernel_apply e iota n theta x]

end DenseTimeFibre

section ContinuousProcess

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hP : P.IsConservative)

/-- Fibrewise Kolmogorov regularity: for every parameter, the dense-time coordinate process of
that parameter's semigroup satisfies a Kolmogorov--Chentsov moment bound with an admissible
Hölder exponent at every starting point.  The exponents and constants may depend on the parameter
and on the starting point. -/
def KolmogorovRegular : Prop :=
  ∀ theta, (P.toSubMarkovKernelSemigroup theta).KolmogorovRegular (hP theta)



/-- The parameterized continuous-path process: the jointly measurable dense-time trajectory of
`P`, transported to continuous paths by the canonical measurable extension, with the fallback path
of that extension fixed to the constant path at `Classical.arbitrary alpha` — exactly the fallback
used by the unparameterized `continuousProcess`.

Joint measurability in the parameter and the starting state is carried by the kernel structure.
Under `P.KolmogorovRegular hP` the choice of fallback is immaterial, by `continuousProcess_eq`. -/
def IsConservative.continuousProcess : Kernel (Theta × alpha) (ContinuousPath alpha) :=
  Kernel.toContinuousPathKernel
    (P.parameterizedDenseTimeTrajectory hP DenseTime.enumeration
      DenseTime.castOrderEmbedding.toEmbedding)
    (ContinuousMap.const NNReal (Classical.arbitrary alpha))

/-- The parameterized continuous-path process is a Markov kernel: from every parameter and every
starting state it assigns total mass one to continuous-path space. -/
instance isMarkovKernel_continuousProcess :
    IsMarkovKernel (IsConservative.continuousProcess P hP) := by
  let : IsMarkovKernel (P.parameterizedDenseTimeTrajectory hP DenseTime.enumeration
      DenseTime.castOrderEmbedding.toEmbedding) :=
    P.isMarkovKernel_parameterizedDenseTimeTrajectory hP _ _
  unfold IsConservative.continuousProcess
  exact Kernel.isMarkovKernel_toContinuousPathKernel _ _

/-- **Fibre identity.**  At every parameter `theta` and every starting state `x`, the parameterized
continuous-path process is the continuous-path process of the semigroup at `theta`, started at `x`.

The identity is exact and unconditional: it holds for every parameter and every starting point,
with no exceptional set and without any regularity hypothesis, because both sides transport the
same dense-time law through the same measurable extension.  It is the theorem that lets every
property of the unparameterized process be restated on the parameterized kernel. -/
theorem IsConservative.continuousProcess_apply (theta : Theta) (x : alpha) :
    IsConservative.continuousProcess P hP (theta, x) =
      SubMarkovKernelSemigroup.IsConservative.continuousProcess
        (P.toSubMarkovKernelSemigroup theta) (hP theta) x := by
  have hext := ContinuousPath.measurable_continuousExtension
    (ContinuousMap.const NNReal (Classical.arbitrary alpha))
  unfold IsConservative.continuousProcess
    SubMarkovKernelSemigroup.IsConservative.continuousProcess
    SubMarkovKernelSemigroup.IsConservative.continuousPathTrajectory
  rw [Kernel.toContinuousPathKernel_eq_map, Kernel.map_apply _ hext,
    Kernel.toContinuousPathKernel_eq_map, Kernel.map_apply _ hext,
    _root_.MarkovProcess.ParameterizedSubMarkovKernelSemigroup.p2m_embedded_6c61c679d0514bbd]







section QuenchedExpectations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



variable [MeasurableSpace E] [BorelSpace E]





end QuenchedExpectations

end ContinuousProcess

end
end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess


