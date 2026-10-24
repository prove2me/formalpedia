-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_Basic
-- name    : KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:56:27.001888+00:00
-- url     : https://prove2.me/theorems/75474d91-943f-4c14-bc64-857e9ddbc51c
-- title:
--   Poisson iterates and tensor-field energies
-- statement:
--   For a probability measure $ν$ on a finite-dimensional real inner-product space and a linear partial map $T:L^2(ν)\to L^2(ν;V)$, `Field ν k` is the family of $L^2(ν)$ components indexed by $k$ tensor slots, and `normSq` is their squared Hilbert–Schmidt norm. The bundle defines totalized weak gradients, generators, centered inverses, componentwise gradients and iterates, together with `energy`, `meanGradSq`, `defect`, permutation and symmetrization operations, scaling, and Taylor coefficient fields; domain-dependent operators return $0$ outside their domains.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Basic.lean#L42-L133 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.Basic`, definition bundle `KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_Basic`; the repository is private at upload time).

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
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointClosure
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointComp
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Contraction
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Dissipation
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_MeanValue
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Domain
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_FormDomain
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Smoothing
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Form
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_VonNeumann
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_Slope_Recovery
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Dirichlet
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Comparison
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Quadratic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Closable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Markov
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Closure
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Multiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_BoundedMultiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_L2_Energy
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Ambient
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Intrinsic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Optimal
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Order.Filter.ENNReal
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace Classical
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
namespace PoissonIterate
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
/-- A tensor field with `k` indices over `Fin (finrank ℝ V)`, as the family of its components in
`L²(ν)`. -/
abbrev Field (ν : ProbabilityMeasure V) (k : ℕ) : Type _ :=
  (Fin k → Fin (Module.finrank ℝ V)) → Lp ℝ 2 (ν : Measure V)
variable {ν : ProbabilityMeasure V} (T : Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V))
/-- The squared Hilbert–Schmidt `L²` norm `Σ_I ‖u_I‖²` of a tensor field. -/
def normSq {k : ℕ} (u : Field ν k) : ℝ :=
  ∑ I, ‖u I‖ ^ 2
/-- The gradient `T u` on the domain of `T`, and `0` elsewhere. -/
def weakGrad (u : Lp ℝ 2 (ν : Measure V)) : Lp V 2 (ν : Measure V) :=
  if h : u ∈ T.domain then T ⟨u, h⟩ else 0
/-- The generator `T†T u` (`= -ℒ u` in the heat model) on its domain, and `0` elsewhere. -/
def gen (u : Lp ℝ 2 (ν : Measure V)) : Lp ℝ 2 (ν : Measure V) :=
  if h : u ∈ (adjointComp T).domain then adjointComp T ⟨u, h⟩ else 0
/-- The weak partial derivative `∂_j u = ⟪e_j, T u⟫` in the standard orthonormal basis. -/
def partialDeriv (j : Fin (Module.finrank ℝ V)) (u : Lp ℝ 2 (ν : Measure V)) :
    Lp ℝ 2 (ν : Measure V) :=
  (innerSL ℝ (stdOrthonormalBasis ℝ V j)).compLp (weakGrad T u)
/-- The centered inverse `(-L)⁻¹ g`: the centered `u ∈ D(T†T)` with `T†T u = g` when one exists
(it is unique when `T` is the closed heat-model gradient), and `0` otherwise. -/
def centeredInv (g : Lp ℝ 2 (ν : Measure V)) : Lp ℝ 2 (ν : Measure V) :=
  if h : ∃ u : (adjointComp T).domain,
      L2.mean ν (u : Lp ℝ 2 (ν : Measure V)) = 0 ∧ adjointComp T u = g then
    (h.choose : Lp ℝ 2 (ν : Measure V))
  else 0
/-- The gradient `∇u` of a tensor field: a new first index. -/
def gradField {k : ℕ} (u : Field ν k) : Field ν (k + 1) :=
  fun J => partialDeriv T (J 0) (u (Fin.tail J))
/-- The centered gradient `∇₀u = ∇u - ∫ ∇u dν` (BKL (22)), componentwise. -/
def grad0 {k : ℕ} (u : Field ν k) : Field ν (k + 1) :=
  fun J => L2.center ν (gradField T u J)
/-- The generator applied componentwise, `-L u`. -/
def genField {k : ℕ} (u : Field ν k) : Field ν k :=
  fun I => gen T (u I)
/-- The centered inverse applied componentwise, `(-L)⁻¹ g`. -/
def invField {k : ℕ} (g : Field ν k) : Field ν k :=
  fun I => centeredInv T (g I)
/-- The normalizing coefficient `α` of BKL (31) for the step from `h`:
`‖∇₀h‖ / ‖∇(-L)⁻¹∇₀h‖`, and `0` when the denominator vanishes (in particular when `∇₀h = 0`,
the source's linear case). -/
def scale {k : ℕ} (h : Field ν k) : ℝ :=
  if normSq (gradField T (invField T (grad0 T h))) = 0 then 0
  else Real.sqrt (normSq (grad0 T h) / normSq (gradField T (invField T (grad0 T h))))
/-- One step of BKL (30): `h ↦ α (-L)⁻¹ ∇₀ h`. -/
def step {k : ℕ} (h : Field ν k) : Field ν (k + 1) :=
  scale T h • invField T (grad0 T h)
/-- The iterates: `iter T f k` is the source's `h_{k+1}`, with `h₁ = f`. -/
def iter (f : Lp ℝ 2 (ν : Measure V)) : (k : ℕ) → Field ν k
  | 0 => fun _ => f
  | k + 1 => step T (iter f k)
/-- The Dirichlet energy `v = ‖∇h‖²` (BKL (34)). -/
def energy {k : ℕ} (h : Field ν k) : ℝ :=
  normSq (gradField T h)
/-- The energy drop `p = |∫ ∇h dν|²` (BKL (35)), as the sum of the squared means of the
components of `∇h`. -/
def meanGradSq {k : ℕ} (h : Field ν k) : ℝ :=
  ∑ J, L2.mean ν (gradField T h J) ^ 2
/-- The defect `χ = ‖∇²h - α ∇h'‖²` of BKL (37) for `h' = step h` and `α = scale h`. -/
def defect {k : ℕ} (h : Field ν k) : ℝ :=
  normSq (gradField T (gradField T h) - scale T h • gradField T (step T h))
/-- Permuting the index positions of a tensor field: `(permField σ u) I = u (I ∘ σ)`. -/
def permField {k : ℕ} (σ : Equiv.Perm (Fin k)) (u : Field ν k) : Field ν k :=
  fun I => u (I ∘ σ)
/-- `S_q u`: the average of `u` over the permutations of its first `q` index positions. -/
def symField {k : ℕ} (q : ℕ) (u : Field ν k) : Field ν k :=
  ((fixingOutside (slots k 0 q)).card : ℝ)⁻¹ •
    ∑ σ ∈ fixingOutside (slots k 0 q), permField σ u
/-- The Taylor coefficient array `T_d u` of a tensor field (BKL (28), componentwise): the `d`
Taylor indices come first, followed by the `k` indices of `u`; the norm is Hilbert–Schmidt. -/
def taylorField (d : ℕ) {k : ℕ} (u : Field ν k) : Coord (Module.finrank ℝ V) (d + k) :=
  WithLp.toLp 2 fun J =>
    taylorTensor (ν : Measure V) (⇑(u fun i => J (Fin.natAdd d i))) d
      (fun i => stdOrthonormalBasis ℝ V (J (Fin.castAdd k i)))
end PoissonIterate
end LogConcave
end KLS
end FunctionalInequalities


