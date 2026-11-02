-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_FeynmanKacKilledDominationCleanV2
-- name    : MarkovProcess_V3HRepair_FeynmanKacKilledDominationCleanV2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T10:03:12.028884+00:00
-- url     : https://prove2.me/theorems/42abb071-7bec-42b4-8eea-88fbc7c6abdc
-- title:
--   Verified MarkovProcess source repair: FeynmanKacKilledDominationCleanV2
-- statement:
--   Kernel and resolvent domination estimates relate Feynman-Kac weighted path integrals to killed transition kernels.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.FeynmanKacKilledDominationCleanV2 source SHA-256 27f01afe245ab527697704a9cf2f7f660f85939931b469443f5f6efdbdab98a3. Only repaired-module import paths were converted to their new published Definitions.Def_MarkovProcess_V3HRepair_* names.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Trajectory_FeynmanKacResolvent_ed9736ae
import Definitions.Def_MarkovProcess_V3HRepair_FeynmanKacJointMeasurableCleanV3
import Definitions.Def_MarkovProcess_V3HRepair_KilledResolventPathCleanV1

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace MarkovProcess.SubMarkovKernelSemigroup
noncomputable section
variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [CompleteSpace alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]
variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

omit [LocallyCompactSpace alpha] in
/-- The Feynman--Kac resolvent is the expected discounted weighted path occupation. -/
theorem IsConservative.feynmanKacResolvent_eq_lintegral_path {q : alpha → ℝ}
    (hq : Measurable q) (lam : ℝ) {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    IsConservative.feynmanKacResolvent P hP q lam f x =
      ∫⁻ omega, (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
        (ENNReal.ofReal (Real.exp
          (-feynmanKacAdditiveFunctional q (Real.toNNReal t) omega)) *
          f (omega (Real.toNNReal t))))
        ∂(IsConservative.continuousProcess P hP x) := by
  have hA : Measurable fun p : ℝ × ContinuousPath alpha ↦
      feynmanKacAdditiveFunctional q (Real.toNNReal p.1) p.2 :=
    (stronglyMeasurable_feynmanKacAdditiveFunctional_joint hq).measurable.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have heval : Measurable fun p : ℝ × ContinuousPath alpha ↦
      p.2 (Real.toNNReal p.1) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hjoint : Measurable fun p : ℝ × ContinuousPath alpha ↦
      ENNReal.ofReal (Real.exp (-lam * p.1)) *
        (ENNReal.ofReal (Real.exp
          (-feynmanKacAdditiveFunctional q (Real.toNNReal p.1) p.2)) *
          f (p.2 (Real.toNNReal p.1))) :=
    (ENNReal.measurable_ofReal.comp
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
        measurable_fst)).mul
      ((hA.neg.exp.ennreal_ofReal).mul (hf.comp heval))
  unfold IsConservative.feynmanKacResolvent IsConservative.feynmanKacENNReal
  calc
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
        ∫⁻ omega, ENNReal.ofReal (Real.exp
          (-feynmanKacAdditiveFunctional q (Real.toNNReal t) omega)) *
          f (omega (Real.toNNReal t))
          ∂(IsConservative.continuousProcess P hP x)) =
        ∫⁻ t in Ioi (0 : ℝ), ∫⁻ omega,
          ENNReal.ofReal (Real.exp (-lam * t)) *
            (ENNReal.ofReal (Real.exp
              (-feynmanKacAdditiveFunctional q (Real.toNNReal t) omega)) *
              f (omega (Real.toNNReal t)))
            ∂(IsConservative.continuousProcess P hP x) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t _ht
      exact (lintegral_const_mul' _ _ (by finiteness)).symm
    _ = _ := lintegral_lintegral_swap hjoint.aemeasurable

omit [LocallyCompactSpace alpha] in
/-- The Feynman--Kac resolvent dominates the resolvent of the process killed on leaving an open
set when the potential vanishes there.  No sign condition on the potential is needed away from
the open set. -/
theorem IsConservative.killedResolvent_le_feynmanKacResolvent
    {q : alpha → ℝ} (hq : Measurable q)
    {U : Set alpha} (hU : IsOpen U) (hqU : ∀ y ∈ U, q y = 0)
    (lam : ℝ) {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    IsConservative.killedResolvent P hP U hU lam f x ≤
      IsConservative.feynmanKacResolvent P hP q lam f x := by
  rw [IsConservative.killedResolvent_eq_lintegral P hP U hU lam hf x,
    IsConservative.feynmanKacResolvent_eq_lintegral_path P hP hq lam hf x]
  apply lintegral_mono
  intro omega
  apply setLIntegral_mono' measurableSet_Ioi
  intro t ht
  have ht0 : 0 < t := ht
  let u : NNReal := Real.toNNReal t
  by_cases hsurv : (u : ℝ≥0∞) < ContinuousPath.exitTime U omega
  · have hA0 : feynmanKacAdditiveFunctional q u omega = 0 := by
      rw [feynmanKacAdditiveFunctional_apply]
      calc
        (∫ s in (0 : ℝ)..u, q (omega (Real.toNNReal s))) = ∫ _s in (0 : ℝ)..u, 0 := by
          apply intervalIntegral.integral_congr
          intro s hs
          have hsu : Real.toNNReal s ≤ u := by
            apply Real.toNNReal_le_iff_le_coe.mpr
            rw [uIcc_of_le u.coe_nonneg] at hs
            exact hs.2
          exact hqU _ (ContinuousPath.mem_of_lt_exitTime U omega (Real.toNNReal s)
            ((ENNReal.coe_le_coe.mpr hsu).trans_lt hsurv))
        _ = 0 := intervalIntegral.integral_zero
    have hsurv' : t ∈ {r : ℝ | ((Real.toNNReal r : NNReal) : ℝ≥0∞) <
        ContinuousPath.exitTime U omega} := by simpa only [u] using! hsurv
    rw [indicator_of_mem hsurv', show feynmanKacAdditiveFunctional q (Real.toNNReal t) omega = 0
      by simpa only [u] using hA0, neg_zero, Real.exp_zero, ENNReal.ofReal_one,
      one_mul]
  · have hsurv' : t ∉ {r : ℝ | ((Real.toNNReal r : NNReal) : ℝ≥0∞) <
        ContinuousPath.exitTime U omega} := by simpa only [u] using! hsurv
    simp only [indicator_of_notMem hsurv', mul_zero, zero_le]

end
end MarkovProcess.SubMarkovKernelSemigroup
#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsConservative.feynmanKacResolvent_eq_lintegral_path
#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedResolvent_le_feynmanKacResolvent


