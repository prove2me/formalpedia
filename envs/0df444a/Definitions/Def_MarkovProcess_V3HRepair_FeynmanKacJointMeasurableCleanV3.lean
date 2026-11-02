-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_FeynmanKacJointMeasurableCleanV3
-- name    : MarkovProcess_V3HRepair_FeynmanKacJointMeasurableCleanV3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T09:45:51.475539+00:00
-- url     : https://prove2.me/theorems/d8ef295f-e2c0-4c83-8c0c-fa8ffe6c0af4
-- title:
--   Verified MarkovProcess source repair: FeynmanKacJointMeasurableCleanV3
-- statement:
--   Joint measurability and evaluation identities for Feynman-Kac additive functionals and their semigroup kernels.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream commit 1f8060caa137731fa08029592019eeaf9d997fe5; source-faithful adapted axiom-clean proof module V3HRepaired.FeynmanKacJointMeasurableCleanV3, archived SHA-256 b8bb32f476105475ddcf9ae5eb4d7e6b7c2f5bb2311fc910ac0152978d4a9fa1.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Trajectory_FeynmanKacFunctional_cc8a1986

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]

omit [MeasurableSpace alpha] [BorelSpace alpha] in
/-- The accumulated potential is unfolded as its path integral. -/
theorem feynmanKacAdditiveFunctional_apply (q : alpha → ℝ) (t : NNReal)
    (omega : ContinuousPath alpha) :
    feynmanKacAdditiveFunctional q t omega =
      ∫ s in (0 : ℝ)..t, q (omega (Real.toNNReal s)) :=
  rfl

variable [SecondCountableTopology alpha]
/-- The accumulated potential is jointly strongly measurable in time and path. -/
theorem stronglyMeasurable_feynmanKacAdditiveFunctional_joint {q : alpha → ℝ}
    (hq : Measurable q) :
    StronglyMeasurable fun p : NNReal × ContinuousPath alpha ↦
      feynmanKacAdditiveFunctional q p.1 p.2 := by
  let phi : (NNReal × ContinuousPath alpha) × ℝ → ℝ := fun p ↦
    if 0 < p.2 ∧ p.2 ≤ (p.1.1 : ℝ)
    then q (p.1.2 (Real.toNNReal p.2)) else 0
  have hset : MeasurableSet {p : (NNReal × ContinuousPath alpha) × ℝ |
      0 < p.2 ∧ p.2 ≤ (p.1.1 : ℝ)} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd
        (NNReal.continuous_coe.measurable.comp (measurable_fst.comp measurable_fst)))
  have heval : Measurable fun p : (NNReal × ContinuousPath alpha) × ℝ ↦
      q (p.1.2 (Real.toNNReal p.2)) := by
    have hpath : Measurable fun p : (NNReal × ContinuousPath alpha) × ℝ ↦
        p.1.2 (Real.toNNReal p.2) :=
      (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
        ((measurable_real_toNNReal.comp measurable_snd).prodMk
          (measurable_snd.comp measurable_fst))
    exact hq.comp hpath
  have hphi : StronglyMeasurable phi := by
    exact (heval.ite hset measurable_const).stronglyMeasurable
  have hint : StronglyMeasurable fun p : NNReal × ContinuousPath alpha ↦
      ∫ s, phi (p, s) := hphi.integral_prod_right'
  have heq : (fun p : NNReal × ContinuousPath alpha ↦
      feynmanKacAdditiveFunctional q p.1 p.2) = fun p ↦ ∫ s, phi (p, s) := by
    funext p
    rw [feynmanKacAdditiveFunctional_apply,
      intervalIntegral.integral_of_le p.1.coe_nonneg]
    change (∫ s in Ioc (0 : ℝ) (p.1 : ℝ), q (p.2 (Real.toNNReal s))) =
      ∫ s, phi (p, s)
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    exact Eventually.of_forall fun s ↦ by
      by_cases hs : s ∈ Ioc (0 : ℝ) (p.1 : ℝ)
      · have hs' : 0 < s ∧ s ≤ (p.1 : ℝ) := hs
        simp only [indicator_of_mem hs, phi, if_pos hs']
      · have hs' : ¬(0 < s ∧ s ≤ (p.1 : ℝ)) := hs
        simp only [indicator_of_notMem hs, phi, if_neg hs']
  rw [heq]
  exact hint

variable [CompleteSpace alpha] [Nonempty alpha] [LocallyCompactSpace alpha]
variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

omit [LocallyCompactSpace alpha] in
/-- The Feynman--Kac operator is unfolded as a path expectation. -/
theorem IsConservative.feynmanKac_apply (q : alpha → ℝ) (t : NNReal)
    (f : alpha → ℝ) (x : alpha) :
    IsConservative.feynmanKac P hP q t f x =
      ∫ omega, Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t)
        ∂(IsConservative.continuousProcess P hP x) :=
  rfl

omit [LocallyCompactSpace alpha] in
/-- A Feynman--Kac operator applied to a bounded measurable observable is jointly measurable in
time and starting point. -/
theorem IsConservative.measurable_feynmanKac_joint {q : alpha → ℝ}
    (hq : Measurable q) : ∀ {f : alpha → ℝ}, Measurable f →
    Measurable fun p : NNReal × alpha ↦
      IsConservative.feynmanKac P hP q p.1 f p.2 := by
  intro f hf
  let Q : Kernel alpha (ContinuousPath alpha) := IsConservative.continuousProcess P hP
  let Q' : Kernel (NNReal × alpha) (ContinuousPath alpha) :=
    Kernel.comap Q Prod.snd measurable_snd
  have hA : Measurable fun p : (NNReal × alpha) × ContinuousPath alpha ↦
      feynmanKacAdditiveFunctional q p.1.1 p.2 :=
    (stronglyMeasurable_feynmanKacAdditiveFunctional_joint hq).measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have heval : Measurable fun p : (NNReal × alpha) × ContinuousPath alpha ↦
      p.2 p.1.1 :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hint : StronglyMeasurable fun p : (NNReal × alpha) × ContinuousPath alpha ↦
      Real.exp (-feynmanKacAdditiveFunctional q p.1.1 p.2) * f (p.2 p.1.1) :=
    ((hA.neg.exp).mul (hf.comp heval)).stronglyMeasurable
  have hInt := hint.integral_kernel_prod_right' (κ := Q')
  simpa only [Q', Kernel.comap_apply, IsConservative.feynmanKac_apply] using hInt.measurable

end
end MarkovProcess.SubMarkovKernelSemigroup

#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsConservative.measurable_feynmanKac_joint


