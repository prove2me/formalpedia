-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Law
-- name    : KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Law
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T11:56:05.996461+00:00
-- url     : https://prove2.me/theorems/f3001755-5166-49fa-bf84-16ecf7546a06
-- title:
--   Joint law for the finite-copy suspension
-- statement:
--   `JointSpace N n` is $\mathrm{EuclideanSpace}\,\mathbb{R}\,(\mathrm{Option}(\mathrm{Fin}\,N\times\mathrm{Fin}\,n))$, with `none` representing the auxiliary scalar coordinate and `some (i,j)` representing a coordinate of copy $i$. `sigma β` is $\sqrt{1+2/\beta^2}$, `copyStat f N x` is $N^{-1/2}\sum_i f(x_i)$, and `embed` maps $(x,s)$ to the vector whose `none` coordinate is $(F_N(x)+s)/\sigma$ and whose pair coordinates are those of the copies. `jointLaw` is the pushforward of the product of the $N$-fold measure product of $\mu$ and `laplaceMeasure β`; the included theorems show it is a probability measure when $f$ is measurable and the factors are probability measures, in particular for $\beta>0$. `CumulantBound d b` names the universal isotropic log-concave cumulant inequality, while `coordinateEquiv` identifies the joint index space with `Fin (N*n+1)`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), item P71. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Law.lean#L34-L250 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Law`, definition bundle `KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Law`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_Laplace
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory
open FunctionalInequalities.Probability.Line
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
namespace Suspension
/-- The joint space `ℝ^{Nn+1}`, indexed by `none` (the coordinate `S`) and pairs `(i, j)`. -/
abbrev JointSpace (N n : ℕ) : Type := EuclideanSpace ℝ (Option (Fin N × Fin n))
/-- The source's `σ_β = √(1 + 2/β²)`. -/
def sigma (β : ℝ) : ℝ := Real.sqrt (1 + 2 / β ^ 2)
/-- `F_N = N^{-1/2} Σ_i f(x_i)`. -/
def copyStat {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (N : ℕ)
    (x : Fin N → EuclideanSpace ℝ (Fin n)) : ℝ :=
  (∑ i, f (x i)) / Real.sqrt N
/-- The map `(x₁, …, x_N, s) ↦ ((F_N(x) + s)/σ, x₁, …, x_N)` into the joint space. -/
def embed {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (σ : ℝ) (N : ℕ)
    (q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ) : JointSpace N n :=
  WithLp.toLp 2 fun o => Option.elim o ((copyStat f N q.1 + q.2) / σ) fun ij => q.1 ij.1 ij.2
/-- The joint law of `(S, X₁, …, X_N)`: the image of `μ^{⊗N} ⊗ η_β` under `embed`. -/
def jointLaw {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (β σ : ℝ) (N : ℕ) : Measure (JointSpace N n) :=
  ((Measure.pi fun _ : Fin N => μ).prod (laplaceMeasure β)).map (embed f σ N)
/-- `jointLaw μ f β σ N` is a probability measure when `μ` and `laplaceMeasure β` are and `f` is
measurable. -/
theorem isProbabilityMeasure_jointLaw {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) {β : ℝ}
    [IsProbabilityMeasure (laplaceMeasure β)] (σ : ℝ) (N : ℕ) :
    IsProbabilityMeasure (jointLaw μ f β σ N) := by
    have hg :
        Measurable
          (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
            fun o : Option (Fin N × Fin n) =>
              o.elim
                ((copyStat f N q.1 + q.2) / σ)
                (fun ij => (q.1 ij.1).ofLp ij.2)) := by
      rw [measurable_pi_iff]
      intro o
      cases o with
      | none =>
          unfold copyStat
          measurability
      | some ij =>
          measurability
    have h_embed : Measurable (embed f σ N) := by
      unfold embed
      exact (WithLp.measurable_toLp 2 _).comp hg
    refine ⟨?_⟩
    rw [jointLaw,
      Measure.map_apply_of_aemeasurable h_embed.aemeasurable MeasurableSet.univ]
    simp
/-- The joint law is a probability measure for every rate `β > 0` (the Laplace law's mass is
`isProbabilityMeasure_laplaceMeasure`). -/
theorem isProbabilityMeasure_jointLaw_of_pos {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) {β : ℝ}
    (hβ : 0 < β) (σ : ℝ) (N : ℕ) : IsProbabilityMeasure (jointLaw μ f β σ N) :=
  haveI := isProbabilityMeasure_laplaceMeasure hβ
  isProbabilityMeasure_jointLaw μ hf σ N
open scoped RealInnerProductSpace in
/-- The hypothesis of BKL Proposition 7.1: `R^ν_{d+1} ≤ b Id` for every isotropic log-concave
probability measure `ν` in every dimension, i.e. `Σ_J κ^ν_{d+1}(u, e_{J 1}, …, e_{J d})² ≤ b |u|²`
in the standard basis of `ℝ^m`. This names the hypothesis; it asserts nothing. -/
def CumulantBound (d : ℕ) (b : ℝ) : Prop :=
  ∀ (m : ℕ) (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin m))),
    KLS.Isotropic ν → _root_.FunctionalInequalities.KLS.LogConcave ν →
      ∀ u : EuclideanSpace ℝ (Fin m),
      ∑ J : Fin d → Fin m, Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
        (Fin.cons u fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k)) ^ 2 ≤ b * ‖u‖ ^ 2
/-- The index set of the joint space has `N n + 1` elements. -/
theorem card_option_prod (N n : ℕ) : Fintype.card (Option (Fin N × Fin n)) = N * n + 1 := by
  simp
/-- The coordinate reindexing of the joint space onto `ℝ^{Nn+1}`. -/
def coordinateEquiv (N n : ℕ) : JointSpace N n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (N * n + 1)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFinOfCardEq (card_option_prod N n))
end Suspension
end LogConcave
end KLS
end FunctionalInequalities


