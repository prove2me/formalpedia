-- Prove2me | Definitions.Def_MarkovProcess_V3H_Examples_HeatOnePoint_42235b58
-- name    : MarkovProcess_V3H_Examples_HeatOnePoint_42235b58
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T08:24:42.843238+00:00
-- url     : https://prove2.me/theorems/a9e2d1d9-9a30-4829-8429-9b6010d77e3a
-- title:
--   MarkovProcess: MarkovProcess_V3H_Examples_HeatOnePoint_42235b58
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Examples_HeatSemigroup_43feba3c
import Definitions.Def_MarkovProcess_V3H_Feller_Resolvent_4f8c89b8
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointExtension_e4fabfdf
import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointKilled_a181fa20
import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointKolmogorov_a805d493
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0Resolvent_c009f25c
import Definitions.Def_MarkovProcess_V3H_Killed_GluingLocal_6bd3d344
import Definitions.Def_MarkovProcess_V3H_Killed_GluingPotential_fe882cb0
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
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
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The compactified heat process

The heat resolvent represents the heat semigroup again
(`kernelSemigroup_heatResolvent`), so its one-point extension moves a live starting point by the
Gaussian law and never reaches the added point.  In the metric determined by the exhaustion
`x ↦ 1 / (1 + |x|)` the distance of two points is at most `2` and the distance of two live points
is at most their distance on the line, so the fourth-moment estimate of the Gaussian law gives
the local Kolmogorov criterion on the compactification
(`hasLocalKolmogorovMoments_onePointKernelSemigroup_heatResolvent`).

This assembles the regularity data from which the continuous-path process of the compactified
heat semigroup is formed (`onePointRegular_heatResolvent`), the witness that those data are
available for a genuine example.  Because the heat semigroup is conservative, the compactified
process started at a live point almost surely never reaches the added point
(`ae_exitTime_eq_top_heatResolvent`).
-/

open MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace MarkovProcess

/-- **The heat resolvent represents the heat semigroup.** -/
theorem kernelSemigroup_heatResolvent : heatResolvent.kernelSemigroup = heatSemigroup :=
  isFellerKernelSemigroup_heatSemigroup.p2m_embedded_7a36add020ed9fda

section Metric

/-- In the exhaustion metric of the line the compactification has diameter at most `2`. -/
theorem p2m_embedded_c3091aaf2596da94 (z w : OnePoint ℝ) :
    letI := OnePoint.exhaustionMetricSpace heatExhaustion continuous_heatExhaustion
      heatExhaustion_pos lipschitzWith_one_heatExhaustion isCompact_heatExhaustion_superlevel
    dist z w ≤ 2 := by
  let := OnePoint.exhaustionMetricSpace heatExhaustion continuous_heatExhaustion
    heatExhaustion_pos lipschitzWith_one_heatExhaustion isCompact_heatExhaustion_superlevel
  induction z using OnePoint.rec with
  | infty =>
      induction w using OnePoint.rec with
      | infty =>
          rw [dist_self]
          norm_num
      | coe y =>
          have hdist : dist (OnePoint.infty : OnePoint ℝ) (y : OnePoint ℝ) = heatExhaustion y := by
            rw [dist_comm]
            rfl
          rw [hdist]
          exact le_trans (heatExhaustion_le_one y) (by norm_num)
  | coe x =>
      induction w using OnePoint.rec with
      | infty =>
          have hdist : dist (x : OnePoint ℝ) (OnePoint.infty : OnePoint ℝ) = heatExhaustion x :=
            rfl
          rw [hdist]
          exact le_trans (heatExhaustion_le_one x) (by norm_num)
      | coe y =>
          have hdist : dist (x : OnePoint ℝ) (y : OnePoint ℝ) =
              min (dist x y) (heatExhaustion x + heatExhaustion y) := rfl
          rw [hdist]
          refine le_trans (min_le_right _ _) ?_
          have hsum : heatExhaustion x + heatExhaustion y ≤ 1 + 1 :=
            add_le_add (heatExhaustion_le_one x) (heatExhaustion_le_one y)
          linarith only [hsum]

/-- In the exhaustion metric of the line the distance of two live points is at most their
distance on the line. -/
theorem edist_coe_coe_le_heatExhaustion (x y : ℝ) :
    letI := OnePoint.exhaustionMetricSpace heatExhaustion continuous_heatExhaustion
      heatExhaustion_pos lipschitzWith_one_heatExhaustion isCompact_heatExhaustion_superlevel
    edist (x : OnePoint ℝ) (y : OnePoint ℝ) ≤ edist x y := by
  let := OnePoint.exhaustionMetricSpace heatExhaustion continuous_heatExhaustion
    heatExhaustion_pos lipschitzWith_one_heatExhaustion isCompact_heatExhaustion_superlevel
  rw [edist_dist, edist_dist]
  exact ENNReal.ofReal_le_ofReal
    (OnePoint.exhaustionMetricSpace_dist_coe_coe_le heatExhaustion continuous_heatExhaustion
      heatExhaustion_pos lipschitzWith_one_heatExhaustion isCompact_heatExhaustion_superlevel x y)

end Metric

section Moments

/-- **The compactified heat semigroup satisfies the local Kolmogorov criterion** in the
exhaustion metric, with the Gaussian fourth moment and the diameter bound as constants. -/
theorem hasLocalKolmogorovMoments_onePointKernelSemigroup_heatResolvent :
    letI := OnePoint.exhaustionMetricSpace heatExhaustion continuous_heatExhaustion
      heatExhaustion_pos lipschitzWith_one_heatExhaustion isCompact_heatExhaustion_superlevel
    heatResolvent.onePointKernelSemigroup.HasLocalKolmogorovMoments 4 2
      gaussianFourthMoment 16 := by
  let := OnePoint.exhaustionMetricSpace heatExhaustion continuous_heatExhaustion
    heatExhaustion_pos lipschitzWith_one_heatExhaustion isCompact_heatExhaustion_superlevel
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · intro h _hh z
    induction z using OnePoint.rec with
    | infty =>
        rw [heatResolvent.p2m_embedded_002f874a7e2c568c h, lintegral_dirac]
        simp only [edist_self, ENNReal.rpow_ofNat, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow, coe_gaussianFourthMoment, zero_le]
    | coe x =>
        have hmass : heatSemigroup h x Set.univ = 1 := isConservative_heatSemigroup h x
        have hlaw : heatResolvent.onePointKernelSemigroup h (x : OnePoint ℝ) =
            (heatSemigroup h x).map ((↑) : ℝ → OnePoint ℝ) := by
          rw [heatResolvent.p2m_embedded_396ad0af3d01b90b h x, kernelSemigroup_heatResolvent,
            hmass, tsub_self, zero_smul, add_zero]
        have hmeas : Measurable fun z : OnePoint ℝ ↦ edist z (x : OnePoint ℝ) ^ (4 : ℝ) :=
          (measurable_edist_left (x := (x : OnePoint ℝ))).pow_const 4
        rw [hlaw, lintegral_map hmeas OnePoint.continuous_coe.measurable]
        refine le_trans (lintegral_mono fun y ↦ ?_) (_root_.MarkovProcess.p2m_embedded_d699d49b7a4121f2.2.2 h x)
        exact ENNReal.rpow_le_rpow (edist_coe_coe_le_heatExhaustion y x) (by norm_num)
  · intro y z
    have hdist : edist z y ≤ 2 := by
      rw [edist_dist]
      calc ENNReal.ofReal (dist z y) ≤ ENNReal.ofReal 2 :=
            ENNReal.ofReal_le_ofReal (_root_.MarkovProcess.p2m_embedded_c3091aaf2596da94 z y)
        _ = 2 := by
            rw [show (2 : ℝ) = ((2 : ℝ≥0) : ℝ) by norm_num, ENNReal.ofReal_coe_nnreal]
            rfl
    calc edist z y ^ (4 : ℝ) ≤ (2 : ℝ≥0∞) ^ (4 : ℝ) :=
          ENNReal.rpow_le_rpow hdist (by norm_num)
      _ = 16 := by
          rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
          norm_num
      _ = ((16 : ℝ≥0) : ℝ≥0∞) := by norm_num

end Moments

/-- **The regularity data of the compactified heat process**: the exhaustion `1 / (1 + |x|)` and
the Kolmogorov regularity which its metric gives the compactified heat semigroup. -/
def onePointRegular_heatResolvent : heatResolvent.OnePointRegular where
  rho := heatExhaustion
  continuous_rho := continuous_heatExhaustion
  rho_pos := heatExhaustion_pos
  lipschitz_rho := lipschitzWith_one_heatExhaustion
  isCompact_superlevel := isCompact_heatExhaustion_superlevel
  kolmogorovRegular := by
    let := OnePoint.exhaustionMetricSpace heatExhaustion continuous_heatExhaustion
      heatExhaustion_pos lipschitzWith_one_heatExhaustion isCompact_heatExhaustion_superlevel
    let : CompleteSpace (OnePoint ℝ) :=
      completeSpace_of_isComplete_univ isCompact_univ.isComplete
    exact SubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments _
      heatResolvent.isConservative_onePointKernelSemigroup
      (hasLocalKolmogorovMoments_onePointKernelSemigroup_heatResolvent.toHasKolmogorovMoments
        heatResolvent.isConservative_onePointKernelSemigroup)



end MarkovProcess


