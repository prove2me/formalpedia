-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardIntegrandFrozen
-- name    : KLS408915f_LevyStochCalc_Ito_PicardIntegrandFrozen
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T10:01:56.532268+00:00
-- url     : https://prove2.me/theorems/43c8e00f-3f49-4437-8c51-079e5fc52188
-- title:
--   Picard integrands along frozen processes
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc). For a process frozen at horizon $T$, this bundle supplies joint measurability and progressive or marked-progressive measurability of the drift, diffusion, and jump integrands, both for `SBoundedProcess` values and for raw processes frozen by $s\mapsto\min(s,T)$. It also defines `picardStepOnRawStop` and `picardStepOnStop`, the Picard step applied to these frozen paths, using `IsRegular`, `IsLipschitz`, and the finite Bielecki-energy hypotheses to discharge the required squared-integrability conditions.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardIntegrandFrozen.lean#L36-L223 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardIntegrandFrozen`, definition bundle `KLS408915f_LevyStochCalc_Ito_PicardIntegrandFrozen`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Algebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_DenseCountable
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_ENNReal
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Filtration
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_FiniteInf
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Indistinguishable
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_LeftLimWithin
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_LinearAlgebra
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Martingale
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeanInequalities
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_MeasureTheory
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Metric
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Nat
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_StoppedProcess
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Topology
import Definitions.Def_KLS408915f_BrownianMotion_Auxiliary_Upcrossing
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
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_Cadlag
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_Predictable
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_Quasimartingale_Basic
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality
import Definitions.Def_KLS408915f_BrownianMotion_StochasticIntegral_SimpleProcess
import Definitions.Def_KLS408915f_KolmogorovExtension4_CompactSystem
import Definitions.Def_KLS408915f_KolmogorovExtension4_KolmogorovExtension
import Definitions.Def_KLS408915f_KolmogorovExtension4_RegularContent
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ContinuityDyadicChaining
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Existence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityDyadicAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPointwise
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityPredictableL2
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityShiftedAverages
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoDensityUnbounded
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionApi
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionConvergence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionExistence
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionLp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoL2CompletionQuadVar
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoMartingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIntegrand
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ItoSimpleMoments
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Martingale
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MartingaleCondExp
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Multidim
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MultidimFiltered
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_MultidimIto
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineAppend
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineCommon
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_SimplePredictableRefineInvariance
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardBieleckiNorm
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardIntegrandBounds
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardStepMap
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_PicardStochasticLipschitz
import Definitions.Def_KLS408915f_LevyStochCalc_Ito_Setting
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_CadlagModification
import Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_Compensated
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedApprox
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityBoxIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityDyadic
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityLimit
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityMarkApprox
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityMarkSum
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityRectSimple
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityRefinement
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityShifted
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityStepIntegral
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDensityTruncation
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedDiff
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleAdapted
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedMartingaleQuadratic
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedProcess
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedProcessQuadVar
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_CompensatedSimple
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_Filtered
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_MarkStepIncrement
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_MarkStepIsometry
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_MarkStepWeight
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_PoissonSuperposition
import Definitions.Def_KLS408915f_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_IndepJoin
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Progressive
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Transport
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_TrivialSigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Group.Continuity
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
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.SetSemiring
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
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Martingale.Upcrossing
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Notation
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.CompactSystem
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.EMetricSpace.PairReduction
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.IsClosedRestrict
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Topology.MetricSpace.MetricSeparated
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Separation.Regular

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardIntegrandFrozen.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Ito
namespace Picard
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
section Frozen
variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
variable {ν : MeasureTheory.Measure E}
variable {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
/-- Joint measurability of the diffusion integrand along the frozen process. -/
theorem measurable_sigma_stop
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    (Y : SBoundedProcess (n := n) P ℱ T) (i : Fin n) (j : Fin d) :
    Measurable (Function.uncurry fun ω s => coeffs.σ s (Y.stop.X s ω) i j) :=
  measurable_sigma_comp_state coeffs hReg Y.stop.measurable_path i j
/-- Progressive measurability of the diffusion integrand along the frozen process. -/
theorem progressivelyMeasurable_sigma_stop
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    (Y : SBoundedProcess (n := n) P ℱ T) (i : Fin n) (j : Fin d) :
    Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (Y.stop.X s ω) i j) := by
  have h : Measurable (Function.uncurry fun (s : ℝ) (x : Fin n → ℝ) => coeffs.σ s x i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hReg.2.1)
  exact progressivelyMeasurable_comp_state Y.stop.adapted h
/-- Joint measurability of the jump integrand along the frozen process. -/
theorem measurable_gamma_stop
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    (Y : SBoundedProcess (n := n) P ℱ T) (i : Fin n) :
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Y.stop.X p.2.1 p.1) p.2.2 i :=
  measurable_gamma_comp_state coeffs hReg Y.stop.measurable_path i
/-- Marked progressive measurability of the jump integrand along the frozen process. -/
theorem markedProgressivelyMeasurable_gamma_stop
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    (Y : SBoundedProcess (n := n) P ℱ T) (i : Fin n) :
    Probability.MarkedProgressivelyMeasurable ℱ
      (fun ω s e => coeffs.γ s (Y.stop.X s ω) e i) := by
  have h : Measurable fun p : ℝ × (Fin n → ℝ) × E => coeffs.γ p.1 p.2.1 p.2.2 i :=
    (measurable_pi_apply i).comp hReg.2.2.1
  exact markedProgressivelyMeasurable_comp_state
    (g := fun (s : ℝ) (x : Fin n → ℝ) (e : E) => coeffs.γ s x e i) Y.stop.adapted h
/-- Joint measurability of the drift integrand along the frozen process. -/
theorem measurable_mu_stop
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    (Y : SBoundedProcess (n := n) P ℱ T) (i : Fin n) :
    Measurable (Function.uncurry fun ω s => coeffs.μ s (Y.stop.X s ω) i) :=
  measurable_mu_comp_state coeffs hReg Y.stop.measurable_path i
/-- Progressive measurability of the drift integrand along the frozen process. -/
theorem progressivelyMeasurable_mu_stop
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    (Y : SBoundedProcess (n := n) P ℱ T) (i : Fin n) :
    Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.μ s (Y.stop.X s ω) i) := by
  have h : Measurable (Function.uncurry fun (s : ℝ) (x : Fin n → ℝ) => coeffs.μ s x i) :=
    (measurable_pi_apply i).comp hReg.1
  exact progressivelyMeasurable_comp_state Y.stop.adapted h
/-- Joint measurability of the diffusion integrand along a raw process frozen at the horizon. -/
theorem measurable_sigma_rawStop
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z)) (T : ℝ)
    (i : Fin n) (j : Fin d) :
    Measurable (Function.uncurry fun ω s => coeffs.σ s (Z (min s T) ω) i j) :=
  measurable_sigma_comp_state coeffs hReg (X := fun s ω => Z (min s T) ω)
    (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)) i j
/-- Progressive measurability of the diffusion integrand along a raw process frozen at the
horizon. -/
theorem progressivelyMeasurable_sigma_rawStop
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i) (T : ℝ)
    (i : Fin n) (j : Fin d) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (Z (min s T) ω) i j := by
  have h : Measurable (Function.uncurry fun (s : ℝ) (x : Fin n → ℝ) => coeffs.σ s x i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hReg.2.1)
  exact progressivelyMeasurable_comp_state (X := fun s ω => Z (min s T) ω)
    (fun i' => (hZa i').minTime T) h
/-- Joint measurability of the jump integrand along a raw process frozen at the horizon. -/
theorem measurable_gamma_rawStop
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z)) (T : ℝ) (i : Fin n) :
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Z (min p.2.1 T) p.1) p.2.2 i :=
  measurable_gamma_comp_state coeffs hReg (X := fun s ω => Z (min s T) ω)
    (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)) i
/-- Marked progressive measurability of the jump integrand along a raw process frozen at the
horizon. -/
theorem markedProgressivelyMeasurable_gamma_rawStop
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i) (T : ℝ)
    (i : Fin n) :
    Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => coeffs.γ s (Z (min s T) ω) e i := by
  have h : Measurable fun p : ℝ × (Fin n → ℝ) × E => coeffs.γ p.1 p.2.1 p.2.2 i :=
    (measurable_pi_apply i).comp hReg.2.2.1
  exact markedProgressivelyMeasurable_comp_state (X := fun s ω => Z (min s T) ω)
    (g := fun s x e => coeffs.γ s x e i) (fun i' => (hZa i').minTime T) h
/-- Joint measurability of the drift integrand along a raw process frozen at the horizon. -/
theorem measurable_mu_rawStop
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z)) (T : ℝ) (i : Fin n) :
    Measurable (Function.uncurry fun ω s => coeffs.μ s (Z (min s T) ω) i) :=
  measurable_mu_comp_state coeffs hReg (X := fun s ω => Z (min s T) ω)
    (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)) i
/-- Progressive measurability of the drift integrand along a raw process frozen at the
horizon. -/
theorem progressivelyMeasurable_mu_rawStop
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i) (T : ℝ)
    (i : Fin n) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.μ s (Z (min s T) ω) i := by
  have h : Measurable (Function.uncurry fun (s : ℝ) (x : Fin n → ℝ) => coeffs.μ s x i) :=
    (measurable_pi_apply i).comp hReg.1
  exact progressivelyMeasurable_comp_state (X := fun s ω => Z (min s T) ω)
    (fun i' => (hZa i').minTime T) h
/-- The horizon energy bounds of a raw process frozen at the horizon, from a finite Bielecki
norm at weight `0`. -/
theorem lintegral_sq_rawStop_lt_top {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZm : Measurable (Function.uncurry Z)) (hZb : bieleckiNorm (P := P) 0 T Z < ⊤)
    (hT : 0 ≤ T) (b : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      ∑ i', (‖Z (min s T) ω i'‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  lt_of_le_of_lt (lintegral_lintegral_sq_stopOf_le T Z hZm hT b)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top hZb))
/-- **The Picard step along a raw state process frozen at the horizon.** -/
noncomputable def picardStepOnRawStop [MeasureTheory.SigmaFinite ν]
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
    (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hZb : bieleckiNorm (P := P) 0 T Z < ⊤) (hT : 0 ≤ T) (x₀ : Fin n → ℝ) :
    ℝ → Ω → (Fin n → ℝ) :=
  picardStep W N ℱ hℱW hℱN coeffs (fun s ω => Z (min s T) ω) x₀
    (measurable_sigma_rawStop coeffs hReg hZm T)
    (progressivelyMeasurable_sigma_rawStop coeffs hReg hZa T)
    (fun i j _ hT' => lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd))
      (lintegral_sq_rawStop_lt_top hZm hZb hT) i j hT')
    (measurable_gamma_rawStop coeffs hReg hZm T)
    (markedProgressivelyMeasurable_gamma_rawStop coeffs hReg hZa T)
    (fun i _ hT' => lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd))
      (lintegral_sq_rawStop_lt_top hZm hZb hT) i hT')
/-- **The Picard map applied to a frozen member of the process space.**

Freezing at the horizon is what makes the step total: `picardStep` asks for its integrands to be
square integrable at every horizon, which `SBoundedProcess.sup_L2` supplies only on `[0, T]`. -/
noncomputable def picardStepOnStop [MeasureTheory.SigmaFinite ν]
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (Y : SBoundedProcess (n := n) P ℱ T) (hT : 0 ≤ T) (x₀ : Fin n → ℝ) :
    ℝ → Ω → (Fin n → ℝ) :=
  picardStep W N ℱ hℱW hℱN coeffs Y.stop.X x₀
    (fun i j => measurable_sigma_stop coeffs hReg Y i j)
    (fun i j => progressivelyMeasurable_sigma_stop coeffs hReg Y i j)
    (fun i j _ hT' => lintegral_sq_sigma_stop_lt_top coeffs hReg hLip Y hT i j hT')
    (fun i => measurable_gamma_stop coeffs hReg Y i)
    (fun i => markedProgressivelyMeasurable_gamma_stop coeffs hReg Y i)
    (fun i _ hT' => lintegral_sq_gamma_stop_lt_top coeffs hReg hLip Y hT i hT')
end Frozen
end Picard
end Ito
end LevyStochCalc


