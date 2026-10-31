-- Prove2me | Definitions.Def_MarkovProcess_V3H_Killed_GluingPotential_fe882cb0
-- name    : MarkovProcess_V3H_Killed_GluingPotential_fe882cb0
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T08:21:28.370819+00:00
-- url     : https://prove2.me/theorems/9e18e4a7-746c-400e-ab3c-a3b20dbef7ad
-- title:
--   MarkovProcess: MarkovProcess_V3H_Killed_GluingPotential_fe882cb0
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Kernel_Resolvent_f63a7282
import Definitions.Def_MarkovProcess_V3H_Killed_Kernel_adff808d
import Definitions.Def_MarkovProcess_V3H_Killed_Resolvent_b61459c1
import Definitions.Def_MarkovProcess_V3H_Path_Exhaustion_e03721f1
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
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
# Potential measures

The resolvent of a transition family at a shift `lam` integrates an observable against the
exponentially weighted time average of its transition kernels.  This file realises that average
as a genuine measure, the `lam`-potential measure

  `laplacePotential lam mu = ∫_0^∞ e^{-lam t} (mu t) dt`,

so that both the kernel resolvent of a sub-Markov kernel semigroup and the killed resolvent of an
open set are integrals against a measure on the state space:
`SubMarkovKernelSemigroup.lintegral_resolventPotential` and
`IsConservative.lintegral_killedPotential`.  Potential measures of sub-Markov families are finite
at every positive shift, with total mass at most `1 / lam`.

Two consequences of the measure form are proved here: the killed resolvent is monotone in the
open set and in the observable (`IsConservative.killedResolvent_mono`), and the kernel resolvent
is measurable in the starting point and continuous along monotone limits of observables
(`SubMarkovKernelSemigroup.measurable_kernelResolvent`,
`SubMarkovKernelSemigroup.kernelResolvent_iSup`).  The kernel resolvent is also additive and
homogeneous on measurable observables (`SubMarkovKernelSemigroup.kernelResolvent_add`,
`SubMarkovKernelSemigroup.kernelResolvent_const_mul`).

No resolvent identity and no topology on the state space are used here.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace MarkovProcess

/-- The exponentially weighted measure on positive times at the shift `lam`. -/
noncomputable def laplaceWeight (lam : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity fun t ↦ ENNReal.ofReal (Real.exp (-lam * t))

/-- The exponential weight is measurable in time. -/
theorem measurable_laplaceDensity (lam : ℝ) :
    Measurable fun t : ℝ ↦ ENNReal.ofReal (Real.exp (-lam * t)) :=
  ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable

/-- Integration against the exponentially weighted time measure. -/
theorem lintegral_laplaceWeight (lam : ℝ) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ t, g t ∂laplaceWeight lam =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) * g t := by
  rw [laplaceWeight,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_laplaceDensity lam) hg]
  rfl

/-- At a positive shift the exponentially weighted time measure has total mass `1 / lam`. -/
theorem laplaceWeight_univ {lam : ℝ} (hlam : 0 < lam) :
    laplaceWeight lam univ = ENNReal.ofReal lam⁻¹ := by
  have hmass : ∫⁻ _t : ℝ, (1 : ℝ≥0∞) ∂laplaceWeight lam = laplaceWeight lam univ :=
    lintegral_one
  rw [← hmass, lintegral_laplaceWeight lam measurable_const]
  simp only [mul_one]
  rw [← ofReal_integral_eq_lintegral_ofReal (exp_neg_integrableOn_Ioi 0 hlam)
    (Eventually.of_forall fun t ↦ (Real.exp_pos _).le)]
  congr 1
  rw [integral_exp_mul_Ioi (neg_neg_of_pos hlam) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp



variable {alpha : Type*} [MeasurableSpace alpha]

/-- The `lam`-potential measure of a measurable family of transition measures: the exponentially
weighted time average of the family. -/
noncomputable def laplacePotential (lam : ℝ) (mu : ℝ → Measure alpha) : Measure alpha :=
  (laplaceWeight lam).bind mu

/-- Integration against a potential measure is the Laplace transform in time of the integrals
against the family. -/
theorem lintegral_laplacePotential (lam : ℝ) {mu : ℝ → Measure alpha} (hmu : Measurable mu)
    {f : alpha → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂laplacePotential lam mu =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) * ∫⁻ y, f y ∂mu t := by
  have hinner : Measurable fun t : ℝ ↦ ∫⁻ y, f y ∂mu t :=
    (Measure.measurable_lintegral hf).comp hmu
  rw [laplacePotential, Measure.lintegral_bind hmu.aemeasurable hf.aemeasurable,
    lintegral_laplaceWeight lam hinner]

/-- A potential measure of a family of sub-probability measures has mass at most `1 / lam`. -/
theorem laplacePotential_univ_le {lam : ℝ} (hlam : 0 < lam) {mu : ℝ → Measure alpha}
    (hmu : Measurable mu) (hmass : ∀ t, mu t univ ≤ 1) :
    laplacePotential lam mu univ ≤ ENNReal.ofReal lam⁻¹ := by
  have hone : ∫⁻ _y : alpha, (1 : ℝ≥0∞) ∂laplacePotential lam mu =
      laplacePotential lam mu univ := lintegral_one
  have hweight : ∫⁻ _t : ℝ, (1 : ℝ≥0∞) ∂laplaceWeight lam = laplaceWeight lam univ :=
    lintegral_one
  rw [← hone, lintegral_laplacePotential lam hmu measurable_const, ← laplaceWeight_univ hlam,
    ← hweight, lintegral_laplaceWeight lam measurable_const]
  refine setLIntegral_mono' measurableSet_Ioi fun t _ht ↦ ?_
  rw [lintegral_one]
  gcongr
  exact hmass t



namespace SubMarkovKernelSemigroup

variable (P : SubMarkovKernelSemigroup alpha)

/-- The transition measures of a sub-Markov kernel semigroup are measurable in time. -/
theorem measurable_toMeasure_toNNReal (x : alpha) :
    Measurable fun t : ℝ ↦ P (Real.toNNReal t) x :=
  P.measurable_toMeasure.comp (measurable_real_toNNReal.prodMk measurable_const)

/-- The `lam`-potential measure of a sub-Markov kernel semigroup started at `x`. -/
noncomputable def resolventPotential (lam : ℝ) (x : alpha) : Measure alpha :=
  laplacePotential lam fun t ↦ P (Real.toNNReal t) x

/-- The kernel resolvent is integration against the potential measure. -/
theorem lintegral_resolventPotential (lam : ℝ) {f : alpha → ℝ≥0∞} (hf : Measurable f)
    (x : alpha) :
    ∫⁻ y, f y ∂P.resolventPotential lam x = P.kernelResolvent lam f x :=
  lintegral_laplacePotential lam (P.measurable_toMeasure_toNNReal x) hf



/-- At a positive shift the kernel resolvent of the constant observable one is at most
`1 / lam`. -/
theorem kernelResolvent_one_le {lam : ℝ} (hlam : 0 < lam) (x : alpha) :
    P.kernelResolvent lam (fun _ ↦ 1) x ≤ ENNReal.ofReal lam⁻¹ := by
  rw [← P.lintegral_resolventPotential lam measurable_const x, lintegral_one]
  exact laplacePotential_univ_le hlam (P.measurable_toMeasure_toNNReal x)
    fun _t ↦ P.measure_univ_le_one _ x



/-- The kernel resolvent is monotone in the observable. -/
theorem kernelResolvent_mono (lam : ℝ) {f g : alpha → ℝ≥0∞} (hfg : f ≤ g) (x : alpha) :
    P.kernelResolvent lam f x ≤ P.kernelResolvent lam g x := by
  refine setLIntegral_mono' measurableSet_Ioi fun _t _ht ↦ ?_
  exact mul_le_mul' le_rfl (lintegral_mono hfg)

/-- The kernel resolvent is additive on measurable observables. -/
theorem kernelResolvent_add (lam : ℝ) {f g : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    P.kernelResolvent lam (fun y ↦ f y + g y) x =
      P.kernelResolvent lam f x + P.kernelResolvent lam g x := by
  unfold kernelResolvent
  have hinner : ∀ t : ℝ, ENNReal.ofReal (Real.exp (-lam * t)) *
      ∫⁻ y, (f y + g y) ∂P (Real.toNNReal t) x =
      ENNReal.ofReal (Real.exp (-lam * t)) * ∫⁻ y, f y ∂P (Real.toNNReal t) x +
        ENNReal.ofReal (Real.exp (-lam * t)) * ∫⁻ y, g y ∂P (Real.toNNReal t) x := by
    intro t
    rw [lintegral_add_left hf, mul_add]
  simp_rw [hinner]
  exact lintegral_add_left ((measurable_laplaceDensity lam).mul
    ((Measure.measurable_lintegral hf).comp (P.measurable_toMeasure_toNNReal x))) _

/-- The kernel resolvent is homogeneous under multiplication by an extended-real constant. -/
theorem kernelResolvent_const_mul (lam : ℝ) (c : ℝ≥0∞) {f : alpha → ℝ≥0∞} (hf : Measurable f)
    (x : alpha) :
    P.kernelResolvent lam (fun y ↦ c * f y) x = c * P.kernelResolvent lam f x := by
  unfold kernelResolvent
  have hinner : ∀ t : ℝ, ENNReal.ofReal (Real.exp (-lam * t)) *
      ∫⁻ y, c * f y ∂P (Real.toNNReal t) x =
      c * (ENNReal.ofReal (Real.exp (-lam * t)) * ∫⁻ y, f y ∂P (Real.toNNReal t) x) := by
    intro t
    rw [lintegral_const_mul c hf]
    ring
  simp_rw [hinner]
  exact lintegral_const_mul c ((measurable_laplaceDensity lam).mul
    ((Measure.measurable_lintegral hf).comp (P.measurable_toMeasure_toNNReal x)))

/-- The kernel resolvent is measurable in the starting point. -/
theorem measurable_kernelResolvent (lam : ℝ) {f : alpha → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun x ↦ P.kernelResolvent lam f x := by
  have hjoint : Measurable fun q : alpha × ℝ ↦
      ENNReal.ofReal (Real.exp (-lam * q.2)) * ∫⁻ y, f y ∂P (Real.toNNReal q.2) q.1 := by
    refine Measurable.mul ((measurable_laplaceDensity lam).comp measurable_snd) ?_
    exact (Measure.measurable_lintegral hf).comp
      (P.measurable_toMeasure.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk
        measurable_fst))
  exact hjoint.lintegral_prod_right'

/-- The kernel resolvent is continuous along monotone limits of observables. -/
theorem p2m_embedded_5e165efdb81ebb50 (lam : ℝ) {f : ℕ → alpha → ℝ≥0∞} (hf : ∀ n, Measurable (f n))
    (hmono : Monotone f) (x : alpha) :
    P.kernelResolvent lam (fun y ↦ ⨆ n, f n y) x = ⨆ n, P.kernelResolvent lam (f n) x := by
  unfold kernelResolvent
  have hinner : ∀ t : ℝ, ENNReal.ofReal (Real.exp (-lam * t)) *
      ∫⁻ y, (⨆ n, f n y) ∂P (Real.toNNReal t) x =
      ⨆ n, ENNReal.ofReal (Real.exp (-lam * t)) * ∫⁻ y, f n y ∂P (Real.toNNReal t) x := by
    intro t
    rw [lintegral_iSup hf fun m n hmn ↦ hmono hmn, ENNReal.mul_iSup]
  simp_rw [hinner]
  refine lintegral_iSup (fun n ↦ ?_) fun m n hmn ↦ ?_
  · exact (measurable_laplaceDensity lam).mul
      ((Measure.measurable_lintegral (hf n)).comp (P.measurable_toMeasure_toNNReal x))
  · intro _t
    exact mul_le_mul' le_rfl (lintegral_mono (hmono hmn))

section Killed

variable [MetricSpace alpha] [CompleteSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)



/-- The `lam`-potential measure of the process killed at the exit of `U`, started at `x`. -/
noncomputable def IsConservative.killedPotential (lam : ℝ) (x : alpha) : Measure alpha :=
  laplacePotential lam fun t ↦ IsConservative.killedKernel P hP U hU (Real.toNNReal t) x







end Killed

end SubMarkovKernelSemigroup

end MarkovProcess


