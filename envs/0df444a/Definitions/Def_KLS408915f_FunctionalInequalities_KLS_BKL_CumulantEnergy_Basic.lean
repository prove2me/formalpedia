-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic
-- name    : KLS408915f_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T11:44:52.845983+00:00
-- url     : https://prove2.me/theorems/b03c6f0e-c280-4b09-9619-ef7b445a3d13
-- title:
--   Cumulant energies and localization drift terms
-- statement:
--   For a measure $\nu$ on $\mathrm{EuclideanSpace}\,\mathbb{R}\,(\mathrm{Fin}\,n)$, `cumulantEnergy ν r u` is the finite sum over $J:\mathrm{Fin}\,r\to\mathrm{Fin}\,n$ of squared cumulants of order $r+1$, with first slot $u$ and remaining slots given by the inverse-square-root covariance operator applied to standard basis vectors. `lowerDrift ν h i₀` sums the covariance-inverse pairings of cumulant vectors over Boolean masks containing slot $i₀$ and having at least two selected and at least two unselected slots. The auxiliary definitions `maskCount`, `sigmaBasis`, `maskTerm`, `middleMasks`, and `pairTerm` expose the corresponding mask counts, whitened basis vectors, individual summands, admissible masks, and squared pair terms.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Basic.lean#L22-L380 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic`, definition bundle `KLS408915f_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Bilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_InverseSqrt
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace KLS
namespace BKL
variable {n : ℕ}
/-- The middle term `L_m` of BKL arXiv:2610.05474v1, (72), at a fixed law `ν` with covariance `A`:
`L_m(h) = Σ_{J ∋ i₀, 2 ≤ |J|, |Jᶜ| ≥ 2} ⟪κ_{|J|+1}(h_J, ·), A⁻¹ κ_{m−|J|+1}(h_{Jᶜ}, ·)⟫` (slot `i₀ = 0`). -/
def lowerDrift (ν : Measure (EuclideanSpace ℝ (Fin n))) {m : ℕ} (h : Fin m → EuclideanSpace ℝ (Fin n))
    (i₀ : Fin m) : ℝ :=
  ∑ q ∈ Finset.univ.filter (fun q : Fin m → Bool =>
      q i₀ = true ∧ 2 ≤ (selected h q).length ∧ 2 ≤ (selected h (fun i => !(q i))).length),
    ⟪cumulantVector ν (selected h q),
      Ring.inverse (Covariance.operator ν) (cumulantVector ν (selected h (fun i => !(q i))))⟫
/-- The cumulant energy `E_{r+1} = |κ_{r+1}(u)|²_A = Σ_J κ_{r+1}(u, σ e_{J_1}, …, σ e_{J_r})²`, `σ = A^{-1/2}`
(BKL (75)–(76)). -/
def cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) (r : ℕ) (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ J : Fin r → Fin n, cumulant ν (r + 1)
    (Fin.cons u fun k => inverseSqrt (Covariance.operator ν) (EuclideanSpace.basisFun (Fin n) ℝ (J k))) ^ 2
end BKL
end KLS
end FunctionalInequalities
section S4Section6Pointwise
open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace KLS
namespace BKL
variable {n : ℕ}
section Masks
/-- number of selected slots -/
def maskCount {k : ℕ} (q : Fin k → Bool) : ℕ := (Finset.univ.filter fun i => q i = true).card
end Masks
section Algebra
/-- `σ e_j` -/
def sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (j : Fin n) : EuclideanSpace ℝ (Fin n) :=
  inverseSqrt (Covariance.operator ν) (EuclideanSpace.basisFun (Fin n) ℝ j)
/-- One mask summand of `lowerDrift`. -/
def maskTerm (ν : Measure (EuclideanSpace ℝ (Fin n))) {m : ℕ} (h : Fin m → EuclideanSpace ℝ (Fin n))
    (q : Fin m → Bool) : ℝ :=
  ⟪cumulantVector ν (selected h q),
    Ring.inverse (Covariance.operator ν) (cumulantVector ν (selected h (fun i => !(q i))))⟫
/-- The masks of the middle allocations: slot `0` selected, at least two slots on each side. -/
def middleMasks (k : ℕ) : Finset (Fin (k + 1) → Bool) :=
  Finset.univ.filter fun q => q 0 = true ∧ 2 ≤ maskCount q ∧ 2 ≤ maskCount (fun i => !(q i))
/-- The squared pair term `⟪κ(u, l₁, ·), A⁻¹ κ(l₂, ·)⟫²` as a function of the two selected lists. -/
def pairTerm (ν : Measure (EuclideanSpace ℝ (Fin n))) (u : EuclideanSpace ℝ (Fin n))
    (l₁ l₂ : List (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ⟪cumulantVector ν (u :: l₁), Ring.inverse (Covariance.operator ν) (cumulantVector ν l₂)⟫ ^ 2
end Algebra
end BKL
end KLS
end FunctionalInequalities
end S4Section6Pointwise


