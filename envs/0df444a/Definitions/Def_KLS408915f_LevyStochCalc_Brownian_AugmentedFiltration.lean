-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Brownian_AugmentedFiltration
-- name    : KLS408915f_LevyStochCalc_Brownian_AugmentedFiltration
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T11:13:04.548523+00:00
-- url     : https://prove2.me/theorems/03e9e6dd-3c93-48a3-a780-ef0516faf135
-- title:
--   Null-set augmentation of a filtration
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `augFiltration ℱ μ` is the filtration whose time-$t$ σ-algebra is `aug (ℱ (max t 0))` by the null sets of $\mu$, so times $t\le0$ use the time-zero σ-algebra. The embedded results identify its value at nonpositive times and show that augmenting a right-continuous filtration remains right-continuous.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/AugmentedFiltration.lean#L51-L139 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.AugmentedFiltration`, definition bundle `KLS408915f_LevyStochCalc_Brownian_AugmentedFiltration`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Algebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_DenseCountable
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_ENNReal
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_FiniteInf
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_LinearAlgebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeanInequalities
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeasureTheory
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Metric
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Nat
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Topology
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_Chaining
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_CoveringNumber
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_HasBoundedInternalCoveringNumber
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_IsKolmogorovProcess
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_KolmogorovChentsov
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_KolmogorovChentsovInequality
import Definitions.Def_KLS408915f_BrownianMotion_Continuity_LimitModification
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_BrownianMotion
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_Moment
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_ProjectiveLimit
import Definitions.Def_KLS408915f_BrownianMotion_Gaussian_StochasticProcesses
import Definitions.Def_KLS408915f_KolmogorovExtension4_CompactSystem
import Definitions.Def_KLS408915f_KolmogorovExtension4_KolmogorovExtension
import Definitions.Def_KLS408915f_KolmogorovExtension4_RegularContent
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ContinuityDyadicChaining
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Existence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Martingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MartingaleCondExp
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Augmentation
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_TrivialSigma
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Finset.Max
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.FiniteExhaustion
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.SesquilinearForm.Star
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Order.CompleteLattice.Group
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.CompactSystem
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.EMetricSpace.PairReduction
import Mathlib.Topology.IsClosedRestrict
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Topology.MetricSpace.MetricSeparated
import Mathlib.Topology.Order.MonotoneContinuity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/AugmentedFiltration.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
namespace LevyStochCalc
namespace Brownian
open LevyStochCalc.Probability
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
/-- The filtration obtained by freezing `ℱ` before time `0` and augmenting each σ-algebra by
the `μ`-null sets. -/
def augFiltration (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (μ : Measure Ω) :
    Filtration ℝ ‹MeasurableSpace Ω› where
  seq t := aug (ℱ (max t 0)) ‹MeasurableSpace Ω› μ
  mono' _ _ hst := aug_mono (ℱ.mono (max_le_max hst le_rfl))
  le' _ := aug_le
theorem augFiltration_of_nonpos (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (μ : Measure Ω)
    {t : ℝ} (ht : t ≤ 0) : augFiltration ℱ μ t = augFiltration ℱ μ 0 := by
  change aug (ℱ (max t 0)) ‹MeasurableSpace Ω› μ = aug (ℱ (max 0 0)) ‹MeasurableSpace Ω› μ
  rw [max_eq_right ht, max_self]
/-- Augmenting a right-continuous filtration keeps it right-continuous. -/
theorem rightCont_augFiltration_le (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (μ : Measure Ω) :
    (augFiltration ℱ.rightCont μ).rightCont ≤ augFiltration ℱ.rightCont μ := by
  intro t
  rcases lt_or_ge t 0 with ht | ht
  · have hs : t < t / 2 := by linarith
    have h1 : (augFiltration ℱ.rightCont μ).rightCont t
        ≤ augFiltration ℱ.rightCont μ (t / 2) := by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le _ hs
    rw [augFiltration_of_nonpos _ _ (by linarith : t / 2 ≤ 0)] at h1
    rw [augFiltration_of_nonpos _ _ ht.le]
    exact h1
  · have hseq : ∀ n : ℕ, t < t + ((n : ℝ) + 1)⁻¹ := by
      intro n
      have : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
      linarith
    have hanti : Antitone fun n : ℕ => ℱ.rightCont (t + ((n : ℝ) + 1)⁻¹) := by
      intro a b hab
      refine ℱ.rightCont.mono ?_
      have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      have hinv : ((b : ℝ) + 1)⁻¹ ≤ ((a : ℝ) + 1)⁻¹ := by gcongr
      linarith
    have h1 : (augFiltration ℱ.rightCont μ).rightCont t
        ≤ ⨅ n : ℕ, aug (ℱ.rightCont (t + ((n : ℝ) + 1)⁻¹)) ‹MeasurableSpace Ω› μ := by
      refine le_iInf fun n => ?_
      have h2 : (augFiltration ℱ.rightCont μ).rightCont t
          ≤ augFiltration ℱ.rightCont μ (t + ((n : ℝ) + 1)⁻¹) := by
        rw [Filtration.rightCont_eq]
        exact iInf₂_le _ (hseq n)
      have h3 : augFiltration ℱ.rightCont μ (t + ((n : ℝ) + 1)⁻¹)
          = aug (ℱ.rightCont (t + ((n : ℝ) + 1)⁻¹)) ‹MeasurableSpace Ω› μ := by
        change aug (ℱ.rightCont (max (t + ((n : ℝ) + 1)⁻¹) 0)) ‹MeasurableSpace Ω› μ = _
        rw [max_eq_left (by linarith [hseq n])]
      rwa [h3] at h2
    rw [aug_iInf_of_antitone hanti] at h1
    have h4 : (⨅ n : ℕ, ℱ.rightCont (t + ((n : ℝ) + 1)⁻¹)) ≤ ℱ.rightCont t := by
      rw [Filtration.rightCont_eq]
      refine le_iInf₂ fun u hu => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < u - t by linarith)
      refine le_trans (iInf_le _ n) ?_
      rw [Filtration.rightCont_eq]
      refine iInf₂_le u ?_
      rw [one_div] at hn
      linarith
    have h5 : augFiltration ℱ.rightCont μ t = aug (ℱ.rightCont t) ‹MeasurableSpace Ω› μ := by
      change aug (ℱ.rightCont (max t 0)) ‹MeasurableSpace Ω› μ = _
      rw [max_eq_left ht]
    rw [h5]
    exact le_trans h1 (aug_mono h4)
instance isRightContinuous_augFiltration (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (μ : Measure Ω) :
    Filtration.IsRightContinuous (augFiltration ℱ.rightCont μ) :=
  ⟨rightCont_augFiltration_le ℱ μ⟩
end Brownian
end LevyStochCalc


