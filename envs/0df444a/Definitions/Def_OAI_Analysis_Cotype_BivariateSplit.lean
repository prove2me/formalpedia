-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_BivariateSplit
-- name    : OAI_Analysis_Cotype_BivariateSplit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T19:30:56.264578+00:00
-- url     : https://prove2.me/theorems/6e6cb172-8c83-447e-b516-37026445caa5
-- title:
--   Splitting the grouped polynomial in the Chebyshev basis
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Sign matrices are Boolean $m\times m$ matrices $S$; $C_{k,l}(f)$ is the total Fourier coefficient of $f$ over $k\times l$ rectangles, and $T_j$ denotes the Chebyshev polynomial of degree $j$. Fix a degree $d$.
--
--   1. **Chebyshev basis and low part.** The basis $(T_j)$ of $\mathbb R[X]$, and the projection keeping the coordinates of $T_0,\dots,T_d$, so that $T_j\mapsto T_j$ for $j\le d$ and $T_j\mapsto0$ otherwise.
--   2. **Retained coefficients.** $C_{k,l}(f)2^{-kl}$ if $k\le d$ or $l\le d$, and $0$ otherwise.
--   3. **Sections and split.** The retained polynomial in $s$ for fixed $u$, its Chebyshev-low part in $s$, and the complementary part, which is high in $s$ and taken as a polynomial in $u$. This splits the truncated grouped polynomial into pieces with controlled degrees in each variable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/BivariateSplit.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/BivariateSplit.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Cotype mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality
import Definitions.Def_OAI_Analysis_Cotype_Rectangles
import Definitions.Def_OAI_Analysis_Cotype_BinaryRank
import Definitions.Def_OAI_Analysis_Cotype_BiasedFourier
import Definitions.Def_OAI_Analysis_Cotype_Damping
import Definitions.Def_OAI_Analysis_Cotype_WalshExactPairing
import Definitions.Def_OAI_Analysis_Cotype_WalshSymmetry
import Definitions.Def_OAI_Analysis_Cotype_CubeCoordinateProjections
import Definitions.Def_OAI_Analysis_Cotype_CubeFirstChaos
import Definitions.Def_OAI_Analysis_Cotype_FrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_BinaryCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshFrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_FrameFeasibility
import Definitions.Def_OAI_Analysis_Cotype_EquivariantLifts
import Definitions.Def_OAI_Analysis_Cotype_DualAction
import Definitions.Def_OAI_Analysis_Cotype_EquivariantPairing
import Definitions.Def_OAI_Analysis_Cotype_FrameLifts
import Definitions.Def_OAI_Analysis_Cotype_L2MomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteLevelTower
import Definitions.Def_OAI_Analysis_Cotype_WeightedCompact
import Definitions.Def_OAI_Analysis_Cotype_CompactQuotient
import Definitions.Def_OAI_Analysis_Cotype_GrowthTuplePairing
import Definitions.Def_OAI_Analysis_Cotype_PatternPairing
import Definitions.Def_OAI_Analysis_Cotype_TaggedFrames
import Definitions.Def_OAI_Analysis_Cotype_CoefficientTarget
import Definitions.Def_OAI_Analysis_Cotype_DampedPolynomial
import Definitions.Def_OAI_Analysis_Cotype_GroupedPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ProjectionCoefficients
import Definitions.Def_OAI_Analysis_Cotype_PatternNormalization
import Definitions.Def_OAI_Analysis_Cotype_PatternProjections
import Definitions.Def_OAI_Analysis_Cotype_DeletedTail
import Definitions.Def_OAI_Analysis_Cotype_ChebyshevBounds
import Definitions.Def_OAI_Analysis_Cotype_ChebyshevTruncation

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial Polynomial.Chebyshev
namespace Cotype

def chebBasis : Module.Basis ℕ ℝ ℝ[X] :=
  (chebyshevTsequence ℝ).basis (fun i =>
    isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr ((chebyshevTsequence ℝ).ne_zero i)))

@[simp] theorem chebBasis_apply (i : ℕ) : chebBasis i = T ℝ i := by
  simp [chebBasis, chebyshevTsequence]

def chebLow (d : ℕ) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun Q := ∑ j ∈ Finset.range (d+1), (chebBasis.repr Q) j • T ℝ j
  map_add' Q R := by simp [map_add, add_smul, Finset.sum_add_distrib]
  map_smul' a Q := by simp [map_smul, mul_smul, Finset.smul_sum]

@[simp] theorem chebLow_basis (d j : ℕ) :
    chebLow d (T ℝ j) = if j ≤ d then T ℝ j else 0 := by
  change (∑ i ∈ Finset.range (d+1), (chebBasis.repr (T ℝ j)) i • T ℝ i) = _
  rw [← chebBasis_apply j, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

variable {m : ℕ}

def retainedCoefficient (f : SignMatrix m → ℝ) (d k l : ℕ) : ℝ :=
  if k ≤ d ∨ l ≤ d then Ckl f k l * (1/2 : ℝ)^(k*l) else 0

def retainedSectionS (f : SignMatrix m → ℝ) (d : ℕ) (u : ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (m+1), ∑ l ∈ Finset.range (m+1),
    (retainedCoefficient f d k l * u^l) • (X : ℝ[X])^k

def splitLowS (f : SignMatrix m → ℝ) (d : ℕ) (u : ℝ) : ℝ[X] :=
  chebLow d (retainedSectionS f d u)

def splitHighU (f : SignMatrix m → ℝ) (d : ℕ) (s : ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (m+1), ∑ l ∈ Finset.range (m+1),
    (retainedCoefficient f d k l * (((X : ℝ[X])^k - chebLow d (X^k)).eval s)) • X^l

end Cotype

end

end OAI


